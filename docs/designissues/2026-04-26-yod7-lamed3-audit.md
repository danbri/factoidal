# Phase 2.6 sub-step — Lamed3 (`cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`) retirement audit

**Author:** yod7 (agent)
**Date:** 2026-04-26
**Status:** AUDIT IN PROGRESS — see Conclusion section.
**Patch:** `formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` (300 LoC).
**Companion bypass:** `formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzzzzzz_q03_estimate_fix.sh` (95 LoC; commit `0543841`).
**Recommended option:** **(a) Keep writer, delete reader patch entirely + delete the q03 bypass.**

## TL;DR

Lamed3 has two halves:

1. A **writer** that builds `<cottas>.p.offsets`, a per-(row-group, predicate-id) row-position companion file. ~150 LoC.
2. A **reader half** that wraps `search_fast` / `search_fast_limited` / `estimate_fast` with `*_via_offsets` dispatchers. ~150 LoC.

The q03 bypass (commit `0543841`, 2026-04-26) **disables all three reader dispatchers** by replacing the function call result with literal `None`. They never run today.

Smoke evidence (2026-04-26, this audit): no `[lamed3-trace]` reader-path log line is emitted by `factoidal_cli explain` for a `?o a wktLiteral`-shaped query. Only the boot-time
`offsets reader: ... mapped (rgs=26 preds=...)` line fires, confirming the mmap is opened but never consulted.

The writer is rule-#11-acceptable (companion-file builder, pure I/O glue). The dispatcher half is rule-#11-violating semantic logic that today is dead code.

## 1. Writer side (companion-file build)

### File format

`<cottas>.p.offsets` — sibling to `.p.dict` and `.p.presence`. Format
documented at `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh:18-27`:

```
[ magic 'COTO' u32 (0x4f544f43 LE) ]
[ version u32 ]
[ num_rgs u32 ]
[ num_predicates u32 ]
[ rg_offsets : u64 array, length num_rgs * num_predicates + 1 ]
[ data : u32[] row positions, ascending, packed ]
```

Per-`(rg, pred_id)` cell: `rg_offsets[rg*np + pred]` is the start byte
offset of the row-position list; the next cell gives the end. Row-list
length = `(end-start)/4` u32s.

### Where the writer lives

`formal/fstar/ocaml-output/RDF_CottasStore.ml:384-680` — module `Cottas_offset_idx` (extracted-and-patched, originally injected by the patch script lines 109-409). Subdivisions:

- `RDF_CottasStore.ml:417-518` — `build_offsets_file` (column scan + bit-packing + atomic-write).
- `RDF_CottasStore.ml:618-680` — `ensure_offsets_built` (boot-time orchestrator).

The writer is hooked into Vav3's prewarm at `RDF_CottasStore.ml:3374-3378`:

```ocaml
(* lamed3: build / mmap the predicate row-offset companion. *)
(try Cottas_offset_idx.ensure_offsets_built cottas_path
 with e ->
   Printf.eprintf "[lamed3-WARN] ensure_offsets_built raised: %s\n%!"
     (Printexc.to_string e));
```

i.e. directly inside `Cottas_companion_boot.prewarm_via_companions` —
runs once per process per corpus, after the four dict+presence pairs
are validated/built.

### Rule-#11 classification

- **`build_offsets_file`** — WRITER. Pure column-scan via
  `Parquet_Footer.probe_parquet_column_decode_in_row_group` + Buffer
  bit-emit + atomic rename. No semantic decisions. ALLOWED per rule
  #15 ("companion-file writers... build disk artifacts; the reader
  path must be in F\*").
- **`ensure_offsets_built`** — WRITER ORCHESTRATOR. Skip-if-present
  guard, then walks the dict via the F\*-extracted
  `RDF_CottasStore_OnDiskIndex.dict_decode_token` to build a
  `tok_to_id` Hashtbl, then calls `build_offsets_file`. Acceptable;
  the dict walk is F\*-delegating (one of only ~3 production callers
  of `dict_decode_token` per the Phi5 audit).
- **`atomic_write`, `write_u32_le`, `write_u64_le`, `offsets_path`,
  `header_size`** — pure byte/path helpers. ALLOWED.

### What lives in the patch vs F\*

**Everything to do with the `.p.offsets` format lives in the patch.**
There is no F\* declaration of:
- The format magic (`'COTO'` = 0x4f544f43).
- The header layout (16 bytes; 4 u32 fields).
- The cell-offset arithmetic (`rg*np + pred`).

This is two-source-of-truth risk identical to the Vav3 writer's
hard-coded `dict_magic` / `presence_magic` constants flagged by the
Phi5 audit.

The format spec belongs in F\* as `RDF.CottasStore.OnDiskOffsetIdx.fst`
(suggested in the patch's own comment, line 60-62: *"belongs in F\* as
RDF.CottasStore.OnDiskOffsetIdx"*). It does not exist today.

## 2. Reader side (offsets-index consult at query time)

### Pre-bypass dispatcher logic

`RDF_CottasStore.ml:1319-1581` — three helpers:

| Helper | Returns `Some` iff | Purpose |
|---|---|---|
| `search_fast_via_offsets` | predicate bound + offsets file mmap'd + token resolves in dict | Skip predicate-column decode; decode subj+obj+graph at row positions only. |
| `search_fast_limited_via_offsets` | same | Same as above with early-exit at `limit` matches. |
| `estimate_fast_via_offsets` | same | Sum row counts (fast path when no other bound) or filter-count (slow path). |

Each dispatcher (originally `RDF_CottasStore.ml:1583-1591`,
`1726-1734`, `1846-1852`) wraps the corresponding `*_inner`:

```ocaml
match <X>_via_offsets h bound [limit] with
| Some result -> Printf.eprintf "[lamed3-trace] ... served from offset index ..."; result
| None        -> <X>_inner h bound [limit]
```

### Post q03-bypass dispatcher logic (TODAY)

The q03 fix patch (`cottas_ondisk_zzzzzzzzz_q03_estimate_fix.sh:51-94`)
replaces the function call result with literal `None`:

`RDF_CottasStore.ml:1587-1591` (search_fast):
```ocaml
(* q03_estimate_fix: bypass lamed3 *_via_offsets — falls through to *_inner *)
match (None : Parser_BallyhooCOTTAS.cottas_qp_row list option) with
| Some result -> ... [DEAD]
| None -> search_fast_inner h bound
```

`RDF_CottasStore.ml:1729-1734` (search_fast_limited):
```ocaml
match (None : Parser_BallyhooCOTTAS.cottas_qp_row list option) with  (* q03_estimate_fix: bypass *)
| Some result -> ... [DEAD]
| None -> search_fast_limited_inner h bound limit
```

`RDF_CottasStore.ml:1845-1852` (estimate_fast):
```ocaml
(* q03_estimate_fix marker — disables lamed3 *_via_offsets dispatchers *)
match (None : pint option) with  (* q03_estimate_fix: bypass *_via_offsets *)
| Some n -> ... [DEAD]
| None -> estimate_fast_inner h bound
```

So the OCaml compiler still **extracts** the bodies of
`search_fast_via_offsets`, `search_fast_limited_via_offsets`, and
`estimate_fast_via_offsets` (at lines 1319, 1430, 1523 respectively),
but **none of them are reachable at runtime**. All three Some-arms are
dead branches.

The boot-time `Cottas_offset_idx.ensure_offsets_built` still runs (and
still emits `[lamed3-trace] offsets reader: ... mapped`), so the file
gets built and mmap'd — but **no production code ever calls
`Cottas_offset_idx.read_header` after boot, nor
`Cottas_offset_idx.row_positions_for`**.

### What `[lamed3-trace]` lines fire today

After the q03 bypass:

| Source line | Trigger | Live? |
|---|---|---|
| `RDF_CottasStore.ml:421` "building offsets file" | first cottas open without `.p.offsets` | LIVE (writer). |
| `RDF_CottasStore.ml:471` "offsets-build rg=N/M" | per-rg progress | LIVE (writer). |
| `RDF_CottasStore.ml:474` "offsets-build columnscan done" | end of column scan | LIVE (writer). |
| `RDF_CottasStore.ml:492` "computed total_size" | header size compute | LIVE (writer). |
| `RDF_CottasStore.ml:518` "wrote .p.offsets" | post-rename | LIVE (writer). |
| `RDF_CottasStore.ml:575-576` "offsets reader: ... mapped" | first `read_header` call | LIVE — but only fires once at boot from `ensure_offsets_built` line 671 `read_header cottas_path`. |
| `RDF_CottasStore.ml:627` "offsets file present, skipping build" | corpus already built | LIVE (writer-skip). |
| `RDF_CottasStore.ml:629` "offsets file absent; building" | corpus needs build | LIVE. |
| `RDF_CottasStore.ml:1360` "search_fast_via_offsets: pred_id=..." | reader dispatch | **DEAD post-bypass.** |
| `RDF_CottasStore.ml:1424` "search_fast_via_offsets: matched ..." | reader complete | **DEAD post-bypass.** |
| `RDF_CottasStore.ml:1453` "search_fast_limited_via_offsets: pred_id=..." | reader dispatch | **DEAD post-bypass.** |
| `RDF_CottasStore.ml:1517` "search_fast_limited_via_offsets: matched .../... rows" | reader complete | **DEAD post-bypass.** |
| `RDF_CottasStore.ml:1581` "estimate_fast_via_offsets: count=..." | reader complete | **DEAD post-bypass.** |
| `RDF_CottasStore.ml:1591` "search_fast: served from offset index" | dispatcher Some-arm | **DEAD post-bypass.** |
| `RDF_CottasStore.ml:1731` "search_fast_limited: served from offset index" | dispatcher Some-arm | **DEAD post-bypass.** |
| `RDF_CottasStore.ml:1849` "estimate_fast: served from offset index" | dispatcher Some-arm | **DEAD post-bypass.** |

**Verdict: the only `[lamed3-trace]` lines reachable today are
writer-side and the boot-time mmap-confirmation. All read-path
dispatcher logs are dead.**

### Reader rule-#11 classification (PRE-bypass — what the patch contains)

- `search_fast_via_offsets` (lines 1319-1428): SEMANTIC LOGIC. Decides
  matching, prune-rg, decode subset. Rule-#11 violation. DUPLICATES the
  filter step that `*_inner` performs (post-Tet3-prune).
- `search_fast_limited_via_offsets` (lines 1430-1521): same.
- `estimate_fast_via_offsets` (lines 1523-1581): same.
- `Cottas_offset_idx.read_header` (lines 533-583): F\*-pure-shape
  byte-decode of a format that should live in F\*. Borderline:
  if the format moves to F\*, this becomes a thin wrapper; today it's a
  parallel implementation.
- `Cottas_offset_idx.row_positions_for` (lines 587-606): the actual
  row-position lookup. Same shape as `dict_decode_token` (one u64-pair
  read for offsets + a bounded byte-range read for the data) — should
  live in F\*.

## 3. F\* equivalent gap

### Today's F\* OnDiskIndex API

`formal/fstar/RDF.CottasStore.OnDiskIndex.fst` defines:
- `dict_header` / `presence_header` records + readers
  (`read_dict_header`, `read_presence_header`).
- Validators (`dict_header_ok`, `presence_header_ok`).
- `dict_decode_token`, `dict_encode_token` (binary search via
  `bsearch_loop`, `read_id_at`).
- `presence_test_bit`.
- `companion_status` aggregate + `companion_encode` /
  `companion_decode` / `companion_rg_could_contain`.

**There is NO type, header, or reader for a per-(rg, pred) offsets
index.** Grep for `offset` or `.p.offsets` in the F\* module returns
zero matches (other than `dh_ids_offset`, `dh_tokens_offset` —
unrelated dict internals).

### What an F\* equivalent would need (signatures only — no impl)

```fstar
// In a new module RDF.CottasStore.OnDiskOffsetIdx.fst:

let coto_magic_u32 : nat = 0x4f544f43  // 'COTO' LE
let offset_layout_version : nat = 1
let offset_header_size : nat = 16  // 4 u32 fields

type offset_header = {
  oh_magic : nat;
  oh_version : nat;
  oh_num_rgs : nat;
  oh_num_preds : nat;
  oh_index_offset : nat;  // always offset_header_size
  oh_data_offset : nat;   // = 16 + 8 * (num_rgs * num_preds + 1)
}

let read_offset_header (path : string) : Tot (option offset_header) = ...
let offset_header_ok (h : offset_header) : Tot bool = ...

// Returns (start_byte_offset, end_byte_offset) for a (rg, pred) cell.
// Caller reads (end-start)/4 u32 row positions starting at start_byte_offset.
let cell_byte_range (h : offset_header) (rg pred_id : nat)
  : Tot (option (nat & nat)) = ...

// High-level: returns the row-position list for (rg, pred_id), or
// None if the cell is empty / out of range.
let read_row_positions (path : string) (h : offset_header)
                       (rg pred_id : nat)
  : Tot (option (list nat)) = ...
```

I/O primitives needed: just `read_companion_u32_le` and
`read_companion_u64_le`, both already declared as `assume val` in
`RDF.CottasStore.OnDiskIndex.fst`. **No new `assume val` needed if the
new module imports OnDiskIndex's primitives** — the byte-range I/O
shape is identical.

The format spec (magic, version, header layout) would move from the
hard-coded OCaml constants in `Cottas_offset_idx` (lines 391-393) to
F\* `let`-bindings, eliminating the two-source-of-truth risk.

What's missing for the F\* version to be canonical:
1. The new `OnDiskOffsetIdx.fst` module (does not exist).
2. A `companion_offset_status` aggregate analogous to `companion_status`.
3. Modification to the **runtime path** — i.e., redirecting
   `cottas_ondisk_search` / `_estimate` / `_search_limited` to consult
   the new F\* readers instead of the OCaml `Cottas_offset_idx`. This
   couples to Phase 2.5 (retire `cottas_ondisk_runtime.sh`); without it
   the F\* runtime functions aren't on the hot path either.
4. Option: keep the writer in OCaml glue (rule-#15 acceptable), or
   also lift the writer to F\* with extracted byte-emit. Phi5's
   precedent for Vav3 suggests writer-stays-in-OCaml is fine.

## 4. Retirement options

### Option (a) — Keep writer, delete reader patch + q03 bypass

**Action:**
1. Modify `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` to keep ONLY the
   writer module (`Cottas_offset_idx.build_offsets_file`,
   `Cottas_offset_idx.ensure_offsets_built`, `atomic_write`,
   `write_u32_le`, `write_u64_le`, `offsets_path`,
   `header_size`) and the `prewarm_via_companions` hook.
2. Delete from the patch: `read_header`, `row_positions_for`,
   `search_fast_via_offsets`, `search_fast_limited_via_offsets`,
   `estimate_fast_via_offsets`, and the dispatcher wrapping (which
   adds the `let rec search_fast = ... | None -> search_fast_inner`
   layer for all three).
3. Delete `cottas_ondisk_zzzzzzzzz_q03_estimate_fix.sh` entirely (its
   reason for existence — the buggy reader fast path — vanishes).
4. Re-extract. Verify `search_fast` / `search_fast_limited` /
   `estimate_fast` are now identical to `*_inner` (no dispatcher
   layer).
5. Verify `.p.offsets` files still build at boot (writer untouched)
   and the file remains valid for a future F\* reader.

**Pros:**
- Smallest unwind step; mechanical; no F\* changes.
- Eliminates ~150 LoC of dead reader semantic logic.
- Eliminates the q03 bypass patch (which the unwind doc Phase 2.6
  flags as deletable when "*_via_offsets either disappears (via
  2.5/2.6 lift) or is fixed in F\*").
- The `.p.offsets` file is preserved on disk — usable when a future
  F\* reader is added (see option (b)) without re-running the ~30s
  build.
- Addresses the rule-#11 violation directly: writer (acceptable) stays;
  reader (violating) goes.

**Cons:**
- The `.p.offsets` file becomes "dead disk-storage" until a future F\*
  reader consumes it. Build cost (~30s on parliament) and disk
  footprint (~few MB on parliament) are paid for no current benefit.
  Mitigation: gate the writer behind an env var (`FACTOIDAL_BUILD_OFFSETS=1`)
  or just leave it — it's small and idempotent.
- Lose the *potential* perf win the reader was meant to deliver
  (skipping the predicate-column decode). But it's already lost — the
  q03 bypass disabled it. So this is no actual regression.

**Blockers:** none. The q03 bypass already validates that current
runtime works without lamed3 reader. Q00–Q03 demo queries are the
gate; if they pass before the unwind, they pass after.

### Option (b) — Lift reader into F\*

**Action:**
1. Author `formal/fstar/RDF.CottasStore.OnDiskOffsetIdx.fst` with the
   types + readers sketched in §3 above.
2. Modify F\* `cottas_ondisk_search` / `_estimate` /
   `_search_limited` (in `RDF.CottasStore.fst`) to consult the new
   readers when predicate is bound. Add a lemma proving the offset-
   indexed scan returns the same set of rows as the full scan.
3. In `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`: keep writer only;
   delete reader half + dispatcher wrapping. The runtime path now
   consults F\* readers, not the OCaml `Cottas_offset_idx`.
4. Delete `cottas_ondisk_zzzzzzzzz_q03_estimate_fix.sh`.
5. Verify W3C 1657/1/0/4. Verify Q00–Q03 timings.

**Pros:**
- Addresses the rule-#11 violation AND restores the perf win the
  patch was supposed to deliver.
- Writer + reader format spec become co-located in F\*; no two-source-
  of-truth risk.
- Establishes the F\* `OnDiskOffsetIdx` module as a reusable pattern
  for future column-side indexes (e.g., compound `(p, o)` index from
  unwind doc §2.6 issue #104).

**Cons:**
- **Coupled to Phase 2.5.** F\* `cottas_ondisk_search` is shadowed by
  `cottas_ondisk_runtime.sh` today — modifying F\* alone has no runtime
  effect until the shadow is retired. So this option is effectively
  blocked behind Phase 2.5 (the 688-LoC big-domino).
- Bigger commit: F\* spec + verification + lemma + extraction ABI +
  smoke regression risk. Estimate ~1-2 agent-days at unwind-pace.
- The reader as written has a known correctness/perf issue (the bug
  the q03 bypass hides). Lifting to F\* without root-causing means
  porting the bug. Need to either (i) fix-as-we-port or (ii) port
  faithfully and verify equivalence vs. `*_inner`. Either path is
  more work than option (a).

**Blockers:**
1. Phase 2.5 (`cottas_ondisk_runtime.sh` retirement) — the F\* runtime
   is shadowed.
2. F\* type-system friction porting the per-rg loop (per unwind doc
   "F\* type-system friction" risk, 2-5×).
3. The same perf cliff that motivated the patch in the first place
   (predicate-column decode is slow — that's *why* the offset index
   was useful). The F\* rewrite needs to avoid the cliff.

### Option (c) — Status quo

**Action:** leave `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` and
`cottas_ondisk_zzzzzzzzz_q03_estimate_fix.sh` both in place, untouched.

**Pros:**
- No work. No regression risk.
- The bypass + dead reader dispatchers are well-commented and rolling
  back is trivial.

**Cons:**
- ~150 LoC of dead semantic logic continues to compile (and ship to
  every binary). Each future agent reading the source has to re-discover
  that the dispatcher Some-arms are dead.
- Two patches stack-trace into each other (the bypass references the
  reader patch; reader patch comments reference an obsolete future fix).
  Lock-in risk: a future agent reads the bypass, decides "this is a
  hack; let me un-hack it", flips the dispatchers back on, and the Q03
  bug returns.
- Continues to violate rule #11 cosmetically — even though the violating
  branch is dead, it's STILL EXTRACTED to OCaml and STILL counted in
  the unwind doc inventory (line 66 in `fstar-purity-unwind.md`:
  "300 LoC | Per-rg predicate row-offset index reader/use | No F\*
  equivalent (writer can stay; reader/use must lift)").

**Blockers:** none — but this option does nothing.

### Recommendation

**Option (a).** Smallest mechanical step that lands the unwind goal
(reader half retired) without coupling to the Phase 2.5 big-domino.
The `.p.offsets` file is small enough that paying its build cost for
no current consumer is acceptable; the file is preserved for option
(b) to land later when Phase 2.5 unblocks it.

This matches the precedent of the tau3 Bet7 audit (defer until 2.6)
and Phi5 Vav3 audit (writer stays + reader-redirect deferred): keep
writers, delete OCaml-side readers, lift to F\* when Phase 2.5
unblocks the runtime.

Risk: the q03 bypass's existence depends on an active reader path. If
a future patch reverts the bypass (option (a)'s deletion target), the
reader returns. Option (a) deletes the bypass simultaneously with the
reader, so the reader cannot return without an explicit code change —
a clean state.

## 5. Smoke evidence

Run the audit smoke command. The user supplied:

```bash
tools/factoidal-debug-query.sh explain \
  --data-cottas tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas \
  -e 'PREFIX geo: <http://www.opengis.net/ont/geosparql#> SELECT ?s ?p ?o WHERE { ?s ?p ?o . ?o a geo:wktLiteral } LIMIT 3'
```

**Result (full trace captured at
`.claude-runs/yod7-lamed3-smoke-20260426T224848.log`, 28 lines).**

`[lamed3-trace]` lines emitted by `tools/factoidal-debug-query.sh
explain` (the HTTP-explain path that calls `prewarm_via_companions`):

```
[lamed3-trace] offsets file present at .../data.cottas.p.offsets, skipping build
[lamed3-trace] offsets reader: .../data.cottas.p.offsets mapped (rgs=26 preds=232 data_off=48280 total=12621904)
```

That's it. **Two lines only**: skip-if-present (writer-side) +
boot-mmap-confirmation (`ensure_offsets_built` post-build
`read_header` call at `RDF_CottasStore.ml:671`). The explain mode does
NOT execute the query, so we additionally ran the same query via
`./bin/darwin-arm64/factoidal --data-cottas ... --query` (the CLI
binary, which per the tau3 Bet7 audit skips `prewarm_via_companions`
and uses Bet7 lazy populators instead). Trace at
`.claude-runs/yod7-lamed3-exec-20260426T224912.log` (59 lines):

```
$ grep -c lamed3 .claude-runs/yod7-lamed3-exec-20260426T224912.log
0
```

**Zero lamed3 trace lines on the CLI execution path.** The CLI binary
doesn't even open the `.p.offsets` file (no prewarm call → no
`ensure_offsets_built` → no mmap of the offsets companion).

Both paths confirm: **the reader half of Lamed3 is fully dead code in
production today.** The HTTP path opens the mmap at boot and never
consults it; the CLI path doesn't even open it.

**Bonus runtime evidence:** the CLI execution shows Tet3's bitmap
prune correctly skipping 25/26 row-groups for the same query
(`search_fast rg=N skipped (could_p=true could_s=true could_o=false)`)
— this is the path the q03 fix-patch's preamble said works correctly
in microseconds. Validates the patch-author's claim that `*_inner`
is the right path.

## Conclusion

- **Reader-side classification:** DEAD CODE today. Q03 bypass forces
  all three dispatchers to fall through to `*_inner`. Confirmed by
  smoke trace.
- **Writer-side classification:** Pure I/O glue per rule #15.
  Acceptable. Small two-source-of-truth risk on the format constants
  but cosmetic.
- **Recommendation:** option (a) — keep writer, delete reader patch +
  delete q03 bypass. Lift the format spec to F\* opportunistically as
  part of option (b) if/when Phase 2.5 unblocks the runtime.

## Files of interest (absolute paths)

- `/Users/danbri/working/factoidal/formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` (the patch).
- `/Users/danbri/working/factoidal/formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzzzzzz_q03_estimate_fix.sh` (the bypass).
- `/Users/danbri/working/factoidal/formal/fstar/RDF.CottasStore.OnDiskIndex.fst` (existing F\* OnDiskIndex API; no offsets-index hooks).
- `/Users/danbri/working/factoidal/formal/fstar/ocaml-output/RDF_CottasStore.ml` lines:
  - 384-680 — `module Cottas_offset_idx` (writer + reader).
  - 1311-1428 — `search_fast_via_offsets` (DEAD post-bypass).
  - 1430-1521 — `search_fast_limited_via_offsets` (DEAD post-bypass).
  - 1523-1581 — `estimate_fast_via_offsets` (DEAD post-bypass).
  - 1585-1591 — `search_fast` dispatcher (Some-arm DEAD).
  - 1726-1734 — `search_fast_limited` dispatcher (Some-arm DEAD).
  - 1845-1852 — `estimate_fast` dispatcher (Some-arm DEAD).
  - 3374-3378 — Lamed3 hook into `prewarm_via_companions` (LIVE).
- `/Users/danbri/working/factoidal/docs/designissues/fstar-purity-unwind.md` (broader plan; line 66 lists Lamed3).
- `/Users/danbri/working/factoidal/docs/designissues/2026-04-26-tau3-bet7-retire-audit.md` (precedent for the audit-format and "blocked on 2.6" pattern).
- `/Users/danbri/working/factoidal/docs/designissues/2026-04-26-phi5-vav3-readpath-audit.md` (precedent for "writer stays, reader-via-OCaml dies").

## Action taken in this phase

- Audit doc committed.
- Patch files untouched.
- No source modifications (`.fst`, `.ml`, `.sh`).
- Unwind tracking table to be updated when option (a) lands (separate
  commit, separate phase).
