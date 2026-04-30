# Issue #121 step 3 — `FStar.UInt32.t` rewrite is the wrong tool

Branch: `claude/121-step3-uint32`. Diagnosis-only commit; no code change.

## TL;DR

The Option-2 plan (introduce `Parser.NTriples.Count.fst` whose loop
counters are `FStar.UInt32.t` instead of `nat`, on the assumption that
`UInt32.t` extracts to native OCaml `int`) is **unsound on this F\* /
OCaml extraction backend**. It would make `--count` slower, not faster.
The remaining Zarith cost in the per-byte hot loop has to be attacked at
the `Parser.FastString` `assume val` boundary, not inside the parsers.

## Evidence

1. `nat` extraction. `Prims.int` is realised as `Z.t` in
   `~/.opam/fstar/lib/fstar/lib/app/Prims.ml`:

   ```ocaml
   type int = Z.t
   let int_zero = Z.zero
   let int_one  = Z.one
   ```

   So every `pos + 1` in the parsers extracts to `Z.add pos Z.one`
   — Zarith allocations / GMP shims. This is the cost step 2 measured
   (87.79 s vs rapper's 25.05 s).

2. `FStar.UInt32.t` extraction. From
   `~/.opam/fstar/lib/fstar/lib/app/ints/FStar_UInt32.ml`:

   ```ocaml
   module M = Stdint.Uint32
   type t = M.t
   let add = M.add
   let v (x:t) : Prims.int = Prims.parse_int (M.to_string x)
   ```

   `Stdint.Uint32.t` is **not** the OCaml native `int`. It is a boxed
   32-bit integer from the `stdint` package. `add`/`sub` go through
   `Stdint.Uint32.add`, which is a C stub call, and the `v` projection
   used by every refinement-type discharge does
   `Z.of_string (Stdint.Uint32.to_string x)` — i.e. format as decimal
   then parse as bignum. Worse than Zarith.

3. `FStar.SizeT.t` extraction. From
   `~/.opam/fstar/lib/fstar/lib/ulib.ml/FStar_SizeT.ml`:

   ```ocaml
   type t = Sz of FStar_UInt64.t
   let v (x:t) : Prims.nat = FStar_UInt64.v (...)
   let add x y = Sz (FStar_UInt64.add ...)
   ```

   A wrapped `FStar_UInt64.t` (= `Stdint.Uint64.t`). Same problem one
   layer deeper. Not native `int`.

4. The `Parser.FastString` boundary. The hot loop's per-byte primitives
   are `assume val`s realised in
   `minimal_regrettable_glue_code_each_with_an_open_issue/89_fast_string_primitives.sh`:

   ```ocaml
   let fs_byte_length (s : Prims.string) : Prims.nat =
     Z.of_int (String.length s)
   let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat =
     Z.of_int (Char.code (String.unsafe_get s (Z.to_int i)))
   ```

   Every byte read pays a `Z.to_int` (on the position) **and** a
   `Z.of_int` (on the result). Switching the loop counter to `UInt32.t`
   would force a `Stdint.Uint32` ↔ `Z.t` conversion at every call site
   (because the F\* signature of `fs_byte_at` is
   `s:string -> i:nat -> n:nat{n<256}` and we cannot change the type of
   a callee independently of the caller in F\*). That conversion is
   `Z.of_string (Stdint.Uint32.to_string ...)` — formatting + parsing —
   per byte, on top of the existing Zarith cost. Strictly worse.

## What step 3 should actually do

The cost is in the boundary between F\* `nat` (Z.t) and OCaml's native
`String.unsafe_get` / `String.length` (native `int`). Two F\*-first
ways to attack it:

### Option A: `pos_t` = native int via `assume`

1. In `Parser.FastString.fst` add an opaque ghost type:
   ```fstar
   assume new type pos_t : eqtype
   assume val pos_zero : pos_t
   assume val pos_succ : pos_t -> pos_t
   assume val pos_lt   : pos_t -> pos_t -> bool
   assume val pos_to_nat : pos_t -> Ghost.erased nat
   assume val fs_byte_length_p : string -> pos_t
   assume val fs_byte_at_p     : string -> pos_t -> n:nat{n<256}
   ```
   Realise `pos_t` in `89_fast_string_primitives.sh` as `int`
   (native), and `pos_succ x = x + 1`, `pos_lt = (<)`. Verification
   uses `pos_to_nat` (ghost, erased) for refinement reasoning.
2. Add `validate_*_p` and `count_ntriples_p` in `Parser.NTriples.fst`
   that thread `pos_t` instead of `nat`. The byte-fetch primitive
   becomes a single `String.unsafe_get` with no Zarith on either side.

This is a real F\* change, not a patch. Step 3 belongs here.

### Option B: chunk the input before scanning

Read input in 64 KiB chunks, run the existing Zarith-heavy validator on
each chunk, but do the chunk-boundary bookkeeping in a thin shim that
uses native `int`. Less invasive, but harder to keep boundary-pure.

### Option C (rejected): rewrite the hot loop in OCaml under a patch

Rule #10 / #11 forbid this. The whole point is to keep the parser
verified.

## Recommendation

Close out the current "step 3 = `inline_for_extraction` + UInt32"
plan. Open a follow-up scoped to **Option A**:
- new `assume val`s for `pos_t` in `Parser.FastString.fst`
- companion patch realising them as native `int`
- mechanical port of `validate_iri` / `scan_iri_end` / `validate_*` /
  `count_ntriples_acc` to the `pos_t` API
- bench against parliament 7.3M N-Triples; goal still 25–30 s.

Until that lands, step 2 (87.79 s) is the floor for `--count` on
parliament-class inputs.

## Why I didn't run a benchmark

The premise of the original prompt is invalidated by inspection of
the F\* runtime libraries on disk; running the build to measure a
predictable regression would burn ~30 minutes of wall-clock and an
F\* extraction cycle for no new information. Wrote the diagnosis
instead, per the instruction to commit a block doc when the gain is
< 10%.
