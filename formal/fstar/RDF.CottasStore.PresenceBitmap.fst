module RDF.CottasStore.PresenceBitmap

// Psi3 (issue #100, 2026-04-26) — F*-source-of-truth read API for the
// per-row-group presence bitmap companion files written by Vav3.
//
// Phase 2.6 of the F*-purity unwind (see
// docs/designissues/fstar-purity-unwind.md). Today the per-rg presence
// data is consulted via Hashtbl-mirrored copies inside the OCaml glue
// patches:
//
//   - experimental_ocaml_glue/cottas_ondisk_zzz_yod6_pred_presence_prune.sh
//     (predicate-presence prune, ~412 LoC of OCaml)
//   - experimental_ocaml_glue/cottas_ondisk_zzzz_tet3_subj_obj_prune.sh
//     (subject + object presence prune, ~515 LoC of OCaml)
//
// Both patches mirror, in OCaml `Hashtbl.t` form, the same per-rg presence
// data that Vav3 already writes to disk as `.presence` companion files
// (format "COTP", see RDF.CottasStore.OnDiskIndex.fst). That mirror is
// rule-#11 violating: the OCaml side is making a "skip this rg" decision,
// which is a backend correctness decision that belongs in F*.
//
// This module is the F*-source-of-truth read API. Yod6 / Tet3's OCaml
// `pred_rg_could_contain` / `subj_rg_could_contain` / `obj_rg_could_contain`
// helpers WILL be migrated to call `rg_contains_token` from this module
// in the Phase 2.6 follow-up commit. (This commit only adds the F*
// module; OCaml patches are NOT modified per the rule-#11 freeze.)
//
// File format (mirrors RDF.CottasStore.OnDiskIndex.fst:44-52):
//
//   .presence file:
//     [ magic       : u32   ASCII 'COTP' = 0x50544f43 ]
//     [ version     : u32   layout version, currently 1 ]
//     [ num_rgs     : u32 ]
//     [ num_tokens  : u32 ]
//     [ bitmap      : ceil(num_rgs * num_tokens / 8) bytes
//                     row-major: bit at position (rg*num_tokens + tok)
//                     is set iff rg contains a row with that token. ]
//
// All byte-range I/O delegates to OnDiskIndex.fst's `assume val`
// primitives. No new I/O assumptions are introduced here.

open RDF.CottasStore.OnDiskIndex
open FStar.Mul

// ------------------------------------------------------------------
// Types. Re-export the structurally-typed `presence_header` already
// declared in OnDiskIndex.fst, plus add a refinement-typed bundle that
// pairs the file path with its parsed header — the shape Yod6 and Tet3
// callers want once a companion file has been opened and validated.
// ------------------------------------------------------------------

// A `bitmap_handle` is an opened+validated presence companion. The
// invariant `bitmap_handle_ok` captures: the header's magic and version
// match (so the bitmap layout is the one we know how to read).
type bitmap_handle = {
  bh_path : string;
  bh_header : presence_header;
}

let bitmap_handle_ok (h : bitmap_handle) : Tot bool =
  presence_header_ok h.bh_header

// A handle whose header is verified at the type level. Used as the
// argument to `rg_contains_token` so that callers cannot forget to
// validate before querying.
let valid_bitmap_handle = h:bitmap_handle{ bitmap_handle_ok h }

// ------------------------------------------------------------------
// Open / close. Composes the I/O assume_vals from OnDiskIndex.fst
// (mmap_companion_open, read_presence_header) into a single call.
// ------------------------------------------------------------------

// Try to open a presence companion file. Returns Some handle iff the
// file exists, the mmap succeeds, the header parses, and magic+version
// match the expected layout. None otherwise — caller falls back to
// "include all rgs" (Yod6/Tet3 today; this is the safe under-prune).
let open_bitmap (path : string) : Tot (option bitmap_handle) =
  match mmap_companion_open path with
  | None -> None
  | Some _file_size ->
    (match read_presence_header path with
     | None -> None
     | Some h ->
       if presence_header_ok h then
         Some { bh_path = path; bh_header = h }
       else None)

// Release the mmap. The OCaml glue tracks live mappings keyed by path.
let close_bitmap (h : bitmap_handle) : Tot unit =
  mmap_companion_close h.bh_path

// ------------------------------------------------------------------
// Lookup primitive: rg_contains_token.
//
// One byte read + one bit test. This IS the runtime read primitive that
// Yod6 / Tet3's `pred_rg_could_contain` etc. should call once Phase 2.6
// migrates them.
//
// Semantics:
//   - If `rg >= num_rgs` or `tok >= num_tokens`: returns false. The bound
//     is out of range, so by convention there is no row in that
//     non-existent rg with that out-of-range token. Yod6/Tet3 callers
//     should bound-check token-id against the dictionary's `num_tokens`
//     before calling; an out-of-range token-id from a successful encode
//     is a contract violation.
//   - Otherwise: reads the byte at offset
//     presence_header_size + (rg*num_tokens + tok)/8, tests bit
//     (rg*num_tokens + tok) mod 8 in LSB-first ordering.
//   - On read I/O failure (None from read_companion_byte): returns true.
//     This is the safe fallback (over-include, under-prune). The caller
//     will run a normal scan over the rg, find nothing matching, and the
//     correctness of the result-set is preserved.
// ------------------------------------------------------------------

let rg_contains_token (h : valid_bitmap_handle) (rg : nat) (tok : nat)
  : Tot bool =
  presence_test_bit h.bh_path h.bh_header rg tok

// ------------------------------------------------------------------
// Convenience: a variant that takes a possibly-failed-to-open handle
// (option), with the "no info -> include rg" semantics already built in.
// This is the exact shape Yod6's `pred_rg_could_contain` callers need
// — they pass through whatever opened, with an over-prune fallback when
// the companion didn't open.
//
// `bound` mirrors Yod6's `bound_p : string option`: the column may be
// unbound in the BGP, in which case every rg trivially "could contain"
// the wildcard. Token resolution (string -> token-id) is the dict
// step (companion_encode in OnDiskIndex.fst); this function operates
// on the resolved token-id.
// ------------------------------------------------------------------

let rg_could_contain (oh : option bitmap_handle) (rg : nat) (bound_tok_id : option nat)
  : Tot bool =
  match bound_tok_id with
  | None -> true   // unbound column: every rg is a candidate
  | Some tok ->
    (match oh with
     | None -> true   // companion not opened: safe over-prune
     | Some h ->
       if bitmap_handle_ok h then
         rg_contains_token h rg tok
       else
         true)        // header invalid: safe over-prune

// ------------------------------------------------------------------
// Soundness: spec-level statement.
//
// The following is the invariant the prune optimisation depends on. We
// state it formally so any future code that consumes `rg_contains_token`
// can rely on a uniform contract; the proof obligation is discharged
// against a spec-side description of "what's in row-group rg".
//
// `bitmap_built_correctly h occurs` says: for every (rg, tok) pair, the
// bit set in the bitmap iff token `tok` actually occurs in some row of
// row-group `rg`, where `occurs : nat -> nat -> bool` is the spec-level
// ground truth.
//
// The lemma `rg_contains_token_sound` states the contrapositive that
// matters at the prune call site: if the bitmap is correctly built and
// `rg_contains_token h rg tok = false`, then `occurs rg tok = false`.
// I.e. it is sound to skip rg `rg` when looking for token `tok`.
//
// This is `admit ()`'d. The `admit` is intentional, not aspirational —
// the spec-side `occurs` predicate is not yet plumbed through the
// COTTAS module surface (would require either a refinement on the file
// format itself or a parallel `RDF.CottasStore.fst:rg_tokens_of` ghost
// function). The Phase 2.6 follow-up that wires this lemma into a real
// proof will need both:
//   (a) a ghost projection from the on-disk bytes -> set of tokens per rg
//   (b) a writer-side lemma that the .presence builder respects (a)
// Neither is in scope for this commit (which is "lift the read API to
// F*"); the LEMMA STATEMENT is what's load-bearing for callers, and
// that statement is checked by the type checker.
// ------------------------------------------------------------------

// Spec-level "what tokens actually appear in row-group rg, in this
// dataset". `occurs rg tok = true` iff token id `tok` appears in some
// row of row-group `rg`. Quantified ghostly; never extracted.
let occurs_pred_t = nat -> nat -> bool

let bitmap_built_correctly
  (h : valid_bitmap_handle) (occurs : occurs_pred_t)
  : Type0 =
  forall (rg:nat) (tok:nat).
    rg < h.bh_header.ph_num_rgs /\ tok < h.bh_header.ph_num_tokens ==>
      (rg_contains_token h rg tok = occurs rg tok)

// Soundness lemma: a `false` result from rg_contains_token is sound to
// trust as "no row in this rg has that token".
//
// Status: admitted. See block comment above for why. The lemma's
// STATEMENT is what callers (Yod6/Tet3 in Phase 2.6 follow-up) rely on;
// the proof itself becomes discharge-able once the spec-side `occurs`
// is plumbed. No `admit` survives in production code paths; this lives
// in the spec layer (no extraction, no runtime impact).
val rg_contains_token_sound :
  h:valid_bitmap_handle ->
  occurs:occurs_pred_t ->
  rg:nat ->
  tok:nat ->
  Lemma
    (requires bitmap_built_correctly h occurs /\
              rg < h.bh_header.ph_num_rgs /\
              tok < h.bh_header.ph_num_tokens /\
              rg_contains_token h rg tok = false)
    (ensures occurs rg tok = false)

let rg_contains_token_sound h occurs rg tok = ()

// Note: the body `()` does discharge the lemma here, because the
// `requires` hypothesis `bitmap_built_correctly h occurs` (a forall over
// rg+tok with the stated equation) plus the in-bounds requirements give
// SMT exactly the equality it needs to flip from
// `rg_contains_token h rg tok = false` to `occurs rg tok = false`. So
// the lemma is proven, NOT admitted, in the form stated. The honest
// remaining gap (commented above) is the producer-side obligation
// that `bitmap_built_correctly` actually holds for any given on-disk
// .presence file — that's the writer-side proof, not in this module.

// ------------------------------------------------------------------
// Dimension accessors. Useful for callers that want to bound-check or
// allocate before iterating.
// ------------------------------------------------------------------

let bitmap_num_rgs (h : valid_bitmap_handle) : Tot nat =
  h.bh_header.ph_num_rgs

let bitmap_num_tokens (h : valid_bitmap_handle) : Tot nat =
  h.bh_header.ph_num_tokens

// ------------------------------------------------------------------
// AND-of-bitmaps composition.
//
// When a triple-pattern binds two or more terms (e.g. both s and p), a
// rg is a candidate iff EVERY bound-presence bit is set. This is the
// generalisation of Yod6's pred-only test to Tet3's subj+pred+obj test.
//
// We express this compositionally: each `rg_could_contain` call is a
// boolean, and we AND them. The naming `rg_passes_all` makes the call
// site read like the spec.
// ------------------------------------------------------------------

let rg_passes_all
  (rg : nat)
  (oh_s : option bitmap_handle) (bound_s : option nat)
  (oh_p : option bitmap_handle) (bound_p : option nat)
  (oh_o : option bitmap_handle) (bound_o : option nat)
  : Tot bool =
  rg_could_contain oh_s rg bound_s &&
  rg_could_contain oh_p rg bound_p &&
  rg_could_contain oh_o rg bound_o

// Soundness for the AND form follows from the per-column soundness
// (each false-result is sound to skip; the AND just composes them).
// We don't state a separate lemma; the call site can apply
// `rg_contains_token_sound` to whichever column drove the false.
