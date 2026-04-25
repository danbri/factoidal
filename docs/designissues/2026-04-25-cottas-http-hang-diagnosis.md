# 2026-04-25 — factoidal-http --data-cottas hang diagnosis (Agent Zayin2)

## Symptom (as reported)

`factoidal-http --data-cottas <file>` hangs forever (2:38 CPU, 44 KB
RSS, never reaches `LISTEN`), while `factoidal --data-cottas <file>`
(CLI) works (after Cottas-Perf's bulk decode landed in 9378d52).

## What I actually found

The CLI does **not** work on the 3.14 M-quad UK Parliament COTTAS
either. Both binaries take the same load path
(`Parser_BallyhooCOTTAS.cottas_open_dataset_store -> load_cache ->
decode_column -> probe_parquet_column_delta_length_byte_array_decode_all`),
and both spend 100% CPU in `BatUTF8.nth_aux` /
`BatUTF8.next` for many minutes (sampled at PID 16413 after 17:24 of
runtime; never finishing).

The HTTP "hang" is the same slow load — `factoidal-http` does
`load_dataset cfg` synchronously **before** binding the listener, so a
slow load looks like a hang. Once load completes, HTTP serves
correctly: the same flag works on a small COTTAS (8 triples / 1.4 KB)
in < 1 s end-to-end.

So: there is no bug in the HTTP argv / load wiring relative to the CLI.
Daleth2's `--data-cottas` integration in `factoidal_http.ml` is a
faithful copy of `load_cottas_dataset` from `factoidal_cli.ml`. The
problem is upstream, in the F\* COTTAS load path.

## Two compounding bugs

### Bug 1 — O(N²) in FStar_String

The fstar.lib OCaml runtime routes `FStar_String.{index, strlen, sub}`
through `BatUTF8`, which walks the byte sequence on every call to
count codepoints. `Parquet.Footer.fst` manipulates a hex-encoded
representation of the decompressed page payload (~16 MB hex per
column for the parliament corpus). One `String.sub` over a 16 MB ASCII
hex string is ~`O(j × (i+j))` ≈ 10¹³ ops in BatUTF8 walks.

The CPU samples confirm this — both binaries sit in
`BatUTF8.nth_aux` from inside
`probe_parquet_column_delta_length_byte_array_page_cache + 232`,
i.e. the `String.sub payload_hex values_start_hex (...)` at line 1553
of `Parquet.Footer.fst`.

### Bug 2 — Multi-miniblock DELTA_LENGTH_BYTE_ARRAY

Once the slow `String.sub` is bypassed (see fix below), the bulk
decoder fails much earlier with `current_len < 0` inside
`build_dlba_length_list`. Adding granular `eprintf`s shows:

* protein__protein1.cottas (1.2 MB):
  `value_count=122880 block_size=2048 miniblocks=8 bit_width=2` → fails
  at `delta_index=2080` (just past the first 2048-value block).
* parliament 64 MB:
  `value_count=122880 block_size=2048 miniblocks=8 bit_width=7` → fails
  at `delta_index=258` (just past the first 256-value miniblock).

The root cause: `build_dlba_length_list` re-uses the **first**
miniblock's `bit_width` for **every** subsequent value, but Parquet's
DELTA_LENGTH_BYTE_ARRAY format gives each miniblock its own
`bit_width` and each block its own `min_delta`. The same single-width
assumption exists in the per-cell `accumulate_lengths` path
(`Parquet_Footer.ml:2505`), which is why the pre-Cottas-Perf path
also failed on these corpora — just very slowly.

This is a real F\* logic gap, out of scope for this 60-min session
and rule #1 (semantic logic must live in F\*). Tracked as a follow-up
for the Cottas-Perf line of work.

## Fix delivered

**Patch:** `103_parquet_ascii_string_fast_path.sh` — post-extraction
override of `FStar_String.{index, strlen, length, sub}` *inside*
`Parquet_Footer.ml` only, routing them through Stdlib byte ops.
Hex-encoded Parquet bytes are pure ASCII (digits + A-F), so codepoint
ops collapse to byte ops and the override is observationally
equivalent. No semantic logic in the patch (rule #15 OK).

This **eliminates Bug 1**.

* Smoke test on a 1.4 KB / 8-triple COTTAS:
  CLI `factoidal --data-cottas X.cottas --count`: pre-fix 0.27 s,
  post-fix 0.02 s.
* HTTP smoke (`--port 3034`, fresh launch):
  binds and answers `SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }`
  with 8 in well under 1 s.
* W3C parser regression: `w3c_runner --rdf` 1031/1031 pass, no
  regression.

For 3.14 M-quad parliament COTTAS, **Bug 2** still blocks load: bulk
decode now returns `None` in 0.11 s (instead of grinding for many
minutes). Same outcome on the smaller `protein__protein1.cottas`
(0.06 s).

## Wallclock summary (3.14 M-quad parliament COTTAS)

| Build | Real | What happened |
|-------|------|---------------|
| Pre-fix (HEAD) | > 5:14 (killed) | Stuck in BatUTF8 inside `String.sub`. |
| Post-103-patch | 0.11 s | Reaches `build_dlba_length_list`, hits multi-miniblock bug, returns `None`. |

So for any COTTAS that does fit in a single miniblock (e.g. KGX
trial fragments < ~256 values per column), this patch alone is
sufficient. For the parliament-scale corpora the multi-miniblock fix
in F\* is needed too.

## Files touched

* `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/103_parquet_ascii_string_fast_path.sh`
  (new, ~120 LoC including doc).
* `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/README.md`
  (one-line patch inventory entry).
* `formal/fstar/ocaml-output/Parquet_Footer.ml` (regenerated; the
  patch's effect is the 12-line `module FStar_String = struct ... end`
  shadow at the top of the file, between `open Prims` and
  `type parquet_footer`).
* `bin/darwin-arm64/{factoidal,factoidal-http,owl_runner,rdfc10_runner,w3c_runner}`
  rebuilt against the patched runtime.

No `--lax`. No semantic logic in the patch. Hard limit ≤ 100 LoC of
patch code (the `103_*.sh` itself is mostly comment + idempotency
boilerplate; the actual sed-style insertion is 11 lines of OCaml).
