# Issue #103 — Parquet.Footer.fst → Parser.FastString migration plan

**Filed**: 2026-05-14
**Tracker**: [#103](https://github.com/danbri/factoidal/issues/103)
**Boundary-audit row**: §3 `103_parquet_ascii_string_fast_path.sh` — `ASSUME-IO`-ish; INVESTIGATE
**Status**: planning — no code change yet.

This doc plans the retirement of `103_parquet_ascii_string_fast_path.sh`,
following the same playbook that retired `95_stack_safe_list_ops.sh` (per
the audit's "same fix as #95" note). It is **not** an attempt at a one-shot
migration — Parquet.Footer.fst has 145 `String.*` call sites against four
distinct primitives, and a partial migration leaves the OCaml shadow in
place. The phases below split the work into landable units.

## Why this exists

Parquet.Footer.fst manipulates hex-encoded payload strings that are
ASCII-only by construction (`[0-9A-F]` plus printable bytes 32-126 in
the ASCII-string decode path). F\*'s `String.length` / `String.index` /
`String.sub` extract to OCaml's `FStar_String` which routes through
BatUTF8 — codepoint-counting walks the byte sequence on every call,
giving O(N²) on multi-megabyte hex strings. The 3.14M-quad UK Parliament
COTTAS reproduces this as a CPU peg in `BatUTF8.nth_aux` for 5+ minutes,
never finishing.

`103_parquet_ascii_string_fast_path.sh` works around this by injecting
a module-local `FStar_String` shadow into the extracted `Parquet_Footer.ml`
that routes `index`/`strlen`/`length`/`sub`/`string_of_list` through
byte ops. The patch is sound (ASCII safety argument), but it carries
semantic logic in post-extraction `sed` style, which is exactly what
rule #11 / the audit's `INVESTIGATE` flag asks us to remove.

The proper fix per the audit: route through `Parser.FastString.fs_byte_*`
primitives, which are themselves `assume val`s realised by
`89_fast_string_primitives.sh` under the `ASSUME-IO` category. After the
migration, Parquet.Footer.fst calls `fs_byte_length` / `fs_byte_at` /
`fs_byte_sub` directly; the shadow module disappears; the #103 patch is
deleted.

## Current call-site inventory

In `formal/fstar/Parquet.Footer.fst`:

| Op | Calls | Migration |
|---|---:|---|
| `String.length` | 120 | → `Parser.FastString.fs_byte_length` |
| `String.sub` | 24 | → `Parser.FastString.fs_byte_sub` |
| `String.string_of_list` | 3 | → new `Parser.FastString.fs_string_of_list_ascii` (Phase A) |
| `String.index` | 1 | → `Parser.FastString.fs_byte_at` (returns `nat`, not `char` — adapt the one call site) |
| **Total** | **148** | |

All 145 byte-indexed sites are decode-stage operations on hex strings or
ASCII payload runs; codepoint semantics never matter. The `string_of_list`
sites (in `finish_ascii_run`, lines 84-86) compose lists of `FStar.Char.char`
where every char is the codepoint of a printable byte (32-126) from
`extract_ascii_strings_hex` — also single-byte-safe.

## Phase A — add `fs_string_of_list_ascii` primitive

**Scope**: pure `assume val` declaration + extension to the
`89_fast_string_primitives.sh` realisation patch. Does **not** touch any
caller; no behavioral change.

**Files**:
- `formal/fstar/Parser.FastString.fst` — add:

  ```fstar
  // Build a string from a list of byte-valued codepoints (each n < 256).
  // O(N) via a single allocation; passes through Stdlib.Bytes.unsafe_set.
  //
  // The F* spec uses `list FStar.Char.char` (each `char` is `nat` with
  // an FStar-side range refinement). For this primitive we constrain
  // each element to fit in one byte; passing a wider codepoint is a
  // precondition violation. Useful in ASCII-only decode paths where
  // FStar.String.string_of_list's BatUTF8.init+List.at composition is
  // O(N²).
  assume val fs_string_of_list_ascii :
    l:list (n:nat{n < 256}) -> string
  ```

- `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/89_fast_string_primitives.sh`
  — append a fifth substitution block, matching the existing
  `failwith "Not yet implemented: Parser.FastString.fs_string_of_list_ascii"`
  stub and replacing with:

  ```ocaml
  let fs_string_of_list_ascii (l : Z.t Prims.list) : Prims.string =
    let open Stdlib in
    let n = List.length l in
    let b = Bytes.create n in
    List.iteri (fun i c ->
      Bytes.unsafe_set b i (Char.unsafe_chr ((Z.to_int c) land 0xff))) l;
    Bytes.unsafe_to_string b
  ```

  (Mirrors the existing #103 shadow's `string_of_list` body but exposed
  as a top-level primitive instead of a module-local override.)

**Build pipeline**:
```bash
eval $(opam env --switch=fstar)
cd formal/fstar
fstar.exe --z3version 4.13.3 Parser.FastString.fst   # verify
./build-ocaml.sh extract                              # re-extract + patches
./build-ocaml.sh compile                              # confirm builds
```

**Verification**:
- `make verify` of `Parser.FastString.fst` passes (no body to verify; pure
  signature addition).
- `./build-ocaml.sh compile` succeeds; binaries link.

**Effort**: XS. One signature line + one realisation block. ~½ day with
the extract/compile cycle.

**Lands**: a new primitive available to the next phase. No call-site
migration. The #103 patch is still applied; nothing retires yet.

## Phase B — migrate the bulk byte ops (120 + 24 + 1)

**Scope**: 145 call-site rewrites in `Parquet.Footer.fst` for
`String.length` / `String.sub` / `String.index`. The migration is
mechanical; the type signatures of `fs_byte_length` (`nat`),
`fs_byte_at` (`nat` returning `nat`), and `fs_byte_sub` (`string`)
match the F\*-side types directly.

**One subtlety**: `String.index s i` returns `FStar.Char.char`;
`fs_byte_at s i` returns `nat`. The one current `String.index` call at
line 1 of the function body (used inside `hex_nibble` chain) is
forwarded into `hex_nibble : FStar.Char.char -> option nat` which
itself just turns the char back into an int. Replacing with
`fs_byte_at` lets us drop the char→int conversion at that site.

**Method** (mechanical):
```fstar
String.length s         → Parser.FastString.fs_byte_length s
String.sub s start len  → Parser.FastString.fs_byte_sub s start len
String.index s i        → Parser.FastString.fs_byte_at s i  (also adapt hex_nibble)
```

The `String.string_of_list` call (3 sites) is **deferred to Phase C**
— it requires the new primitive from Phase A.

**Files**: `formal/fstar/Parquet.Footer.fst` only. No glue patch
changes. After re-extraction, `Parquet_Footer.ml` will call
`Parser_FastString.fs_byte_*` directly; the existing 145 call sites
in the shadow module are still present, but unused, because no F\*-
side caller routes through them anymore.

**Verification**:
- `make verify Parquet.Footer.fst` passes (refinement on `fs_byte_at`
  matches `String.index`'s preconditions).
- W3C parquet/COTTAS smoke test: `bin/cottas-ondisk-smoketest`
  succeeds on a ≥ 1M-quad fixture; load time ≤ 2 × the pre-migration
  baseline (target: no perf regression).

**Effort**: M. Mechanical but volume-heavy (145 sites). 1-2 days
with careful review.

**Lands**: F\* side calls FastString primitives. The shadow module
inside `Parquet_Footer.ml` is now dead code, but the `#103` patch
still injects it on every extract. **Patch is not yet removable** —
Phase C must land first.

## Phase C — migrate `string_of_list` (3 sites)

**Scope**: replace `String.string_of_list (List.Tot.rev current)` in
`finish_ascii_run` (and any other site) with
`fs_string_of_list_ascii (List.Tot.map FStar.Char.int_of_char (List.Tot.rev current))`,
adapting the `FStar.Char.char` → `nat` type shift.

Alternative: change `current` to be `list (n:nat{n < 256})` directly
upstream in `extract_ascii_strings_hex`, removing the `FStar.Char.char_of_int`
intermediate at line 98. This is the cleaner refactor and saves a pass.

**Files**: `formal/fstar/Parquet.Footer.fst`.

**Verification**:
- `make verify Parquet.Footer.fst` passes.
- The W3C smoke test from Phase B continues to pass.

**Effort**: S. Small refactor; 3 call sites + the upstream type change.

**Lands**: every F\*-side reference to `Parquet_Footer.ml`'s shadow
`FStar_String` is gone. The shadow module is now provably dead.

## Phase D — delete `103_parquet_ascii_string_fast_path.sh`

**Scope**: remove the patch file; re-extract and confirm the build
still produces the same on-disk bytes for a fixed Parquet fixture.

**Files**:
- Delete `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/103_parquet_ascii_string_fast_path.sh`.
- Update `docs/designissues/fstar-ocaml-boundary-audit.md` §3:
  flip the `103` row from `ASSUME-IO`-ish / INVESTIGATE → `RETIRED`
  / DONE with a commit link.

**Verification**:
- `./build-ocaml.sh extract` produces a `Parquet_Footer.ml` that does
  **not** contain the `__PARQUET_ASCII_STRING_FAST_PATH__` marker.
- `bin/cottas-ondisk-smoketest` matches Phase B's baseline.
- Full W3C suite passes (no regression).
- Issue #103 closed with the deleting commit.

**Effort**: XS. The delete + audit refresh is mechanical; the
verification step is the work.

## Phase E — perf-witness CI gate (optional, recommended)

**Scope**: add a CI test that loads a known Parquet fixture and asserts
the load completes within a wall-clock bound (e.g. ≤ 5s for a
100k-quad fixture). Mirrors the hash-witness pattern from §4 of the
boundary audit, but for performance instead of bytes.

Rationale: the entire point of #103 is performance. A regression in
`FastString` (or a future contributor accidentally re-routing through
`FStar.String`) would silently restore the O(N²) blowup; a CI gate
catches it.

**Files**: `tests/perf/parquet_load_wallclock.ml` (or extend an
existing perf bench). Refer to `tests/unit/dict_writer_roundtrip.ml`
for the round-trip-witness pattern's CI-wiring (`dune` stanza,
fixture layout).

**Effort**: S. Bench plumbing exists; this is one more entry.

**Lands**: `#103` migration is *anti-fragile* against future
regressions.

## Phase ordering and parallelism

Phases A → B → C → D are sequential (each phase's verification
depends on the previous landing). Phase E (perf gate) can land in
parallel with D once C is in.

Phases A, B, C can each be a separate PR; D is the closing PR. E is
a fast-follow.

## Risks and unknowns

- **Refinement-precondition tightening**: `String.sub` requires
  `start + len <= String.length s`; `fs_byte_sub` accepts a wider
  domain (clamps on overflow per the realisation in #89). F\* won't
  reject this — the refinement is weaker on the new primitive — but
  it does mean a call site that *relied* on the stronger precondition
  for downstream reasoning may need an explicit assertion. Spot-check
  any caller that uses `String.length` arithmetic to bound a `String.sub`
  argument.
- **`fs_byte_at` returns `nat`, not `FStar.Char.char`**: the one
  `String.index` site uses `hex_nibble` which already converts char
  back to nat. After Phase B, `hex_nibble` can be either kept (with a
  trivial `FStar.Char.char_of_int` wrapper) or simplified to take a
  `nat` directly. The cleaner option is to simplify `hex_nibble`'s
  signature once.
- **`make verify` time**: Parquet.Footer.fst is a large module
  (~2500 LoC). After Phase B, every refinement-condition on
  `fs_byte_at`/`fs_byte_sub` must discharge against z3 4.13.3.
  Locally the existing `make verify` of this module is ~30s; the
  migration may shift that to 30-60s. Watch for blowup; if it occurs,
  consider tactic hints rather than `--admit_smt_queries`.
- **jsoo / wasm regressions**: the existing `89_fast_string_primitives.sh`
  has a long `Pass-1` comment about jsoo `use-js-string=true` semantics.
  Phase B routes Parquet.Footer.fst through those same primitives;
  the jsoo bundle must still load Parquet fixtures correctly. Run
  `./build-ocaml.sh js` + a smoke browser test before closing Phase D.

## Out of scope (deliberate)

- `extract_ascii_strings_hex`'s algorithmic shape: works, leave alone.
- Adding new `Parser.FastString` primitives beyond `fs_string_of_list_ascii`:
  not needed for this migration.
- Migrating other modules that use `FStar.String` ops on hex strings
  (e.g. `RDF.CottasStore.OnDiskIndex.fst`): tracked separately in
  the boundary audit; this plan covers Parquet.Footer.fst only.
- Performance optimization of the existing fs\_byte\_\* realisations.
  The current bodies in `89_fast_string_primitives.sh` are already
  O(1) on native; the jsoo path is byte-true via TextEncoder per #240.

## Cross-references

- [`docs/designissues/2026-04-25-cottas-parquet-load-path-perf.md`](2026-04-25-cottas-parquet-load-path-perf.md)
  — original perf diagnosis that motivated the #103 patch.
- [`docs/designissues/fstar-ocaml-boundary-audit.md`](fstar-ocaml-boundary-audit.md)
  §3 row for `103_parquet_ascii_string_fast_path.sh` — current
  classification.
- [`formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/89_fast_string_primitives.sh`](../../formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/89_fast_string_primitives.sh)
  — the realisation patch this plan extends.
- Issue [#95](https://github.com/danbri/factoidal/issues/95) — the
  prior `stack_safe_list_ops` retirement followed the same
  glue-patch → F\*-spec playbook; reuse the PR shape (one PR per
  phase).
- Issue [#240](https://github.com/danbri/factoidal/issues/240) —
  jsoo `use-js-string` regression that drove the #89 byte-true
  rewrite. Phase B inherits that behaviour.
