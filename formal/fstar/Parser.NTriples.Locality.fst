module Parser.NTriples.Locality

(** ========================================================================
 * PILOT case of the parser-locality induction program (task brief,
 * 2026-08-11 landing). Proof-only module -- NOT wired into
 * build-ocaml.sh, no `assume val`, no `--lax`, no admits.
 *
 * WHY THIS FILE. Two theorems are blocked on the SAME wall, diagnosed by
 * two independent sessions from two entry points:
 *   - `theorem_stream_eq_batch` (RDF.NQuads.Streaming.fst, task #48):
 *     needs `parse_nquads_acc_concat_line`, which needs a LOCALITY lemma
 *     for `parse_subject`/`parse_iri`/`parse_object` (and their call
 *     graph through Parser.Combinators.fst) -- "behaves identically on
 *     `complete ^ carry` at any position `p < fs_byte_length complete` as
 *     it does on `complete` alone."
 *   - The symbolic N-Triples round-trip (RDF.NTriples.RoundTrip.fst
 *     checkpoint (b)): needs `scan_iri_end` shown to terminate at
 *     `fs_byte_length i` for an arbitrary well-formed IRI body `i`, which
 *     that file's own Part 6 banner ("NEXT NARROWEST UNPROVED STATEMENT" /
 *     "THE WALL, precisely") diagnoses as needing a "`scan_iri_end`
 *     commutes with prefixing" shift lemma -- "a genuinely separate
 *     multi-step induction ... that a 3-attempt guard does not clear."
 *
 * Both FINDINGs converge on the SAME missing piece, stated over BYTE
 * READS rather than string identity -- exactly the register that avoids
 * the wall RDF.NTriples.RoundTrip.fst's Part 6 records directly:
 * `"" ^ s == s` and `(a^b)^c == a^(b^c)` both FAIL for symbolic strings
 * via plain `()` (confirmed by direct probe there), because Z3 has no
 * native associativity/identity theory for `FStar.String.strcat` over
 * symbolic operands. Position/byte-value facts do not have that problem:
 * they bottom out in `nat`/`FStar.Char.char` equalities Z3 chains by
 * ordinary transitivity -- exactly the register `RDF.NQuads.Streaming
 * .fst`'s own `lemma_fs_byte_index_concat` / `lemma_byte_index_at_middle`
 * (PHASE 2 CHECKPOINT, same 2026-08-11 session) already used for a
 * single-position fact. This file extends that register from ONE byte
 * read to a WHOLE COMBINATOR's recursion: `scan_iri_end`.
 *
 * WHY `scan_iri_end` AS THE TEMPLATE. It is Parser.NTriples.fst's
 * simplest recursive scanner: its only opaque atoms are `fs_byte_length`
 * and `fs_byte_index` (no `fs_byte_sub`, no accumulator, no escape
 * decoding -- that is `parse_iri_body_acc`'s job, the slow path this
 * function falls back to on backslash). Its recursion structure is a
 * plain `if fuel = 0 / if pos >= len / match on the byte at pos / else
 * recurse` -- the shape every other combinator in this file
 * (`parse_iri_raw`, `parse_subject`, `parse_object`, `ptake_while` in
 * Parser.Combinators.fst) shares, just with more branches and, in
 * `parse_iri_body_acc`'s and `parse_object`'s cases, an accumulator that
 * ALSO needs an `fs_byte_sub`-level locality fact (`fs_byte_sub_concat_
 * left`, already proved in Parser.FastString.Axioms.fst, is the exact
 * tool for that -- not needed here since `scan_iri_end` returns only a
 * position, no string).
 *
 * METHOD (the task brief's own suggested decomposition, followed
 * exactly): state the shift lemma under an embedding hypothesis, prove
 * it by induction on `scan_iri_end`'s own `fuel` parameter with a `rec`
 * lemma whose branch structure is LITERALLY PARALLEL to the function's
 * (per-branch: `fuel = 0` / `pos >= len` / `code = 0x3E` / `code = 0x5C`
 * / forbidden-or-control / recurse), and keep the position arithmetic
 * (`p + (i+1) == (p+i) + 1`) inside the SAME proof as the byte facts --
 * unlike the task brief's contingency plan, this turned out not to need
 * a separate helper: it is plain `nat` addition, which Z3's linear
 * arithmetic theory handles without any string reasoning at all, so
 * there was nothing here for heavy string facts to interfere with.
 * ======================================================================== *)

open Parser.NTriples
open Parser.FastString
open Parser.FastString.Axioms
open Parser.Combinators

#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"

(** ------------------------------------------------------------------------
 * Sub-lemma 1: `lemma_byte_index_at_middle` -- a byte read at position
 * `i` inside `mid` agrees with a byte read at the SHIFTED position
 * `fs_byte_length prefix + i` inside `prefix ^ (mid ^ suffix)`.
 *
 * Same fact, same derivation, as `RDF.NQuads.Streaming.fst`'s
 * `lemma_byte_index_at_middle` (chaining `lemma_fs_byte_index_concat`
 * twice) -- restated locally rather than imported so this module stays
 * self-contained (it composes only `Parser.FastString.Axioms.fst`'s
 * already-proved eight-fact trust surface plus `Parser.FastString.fsti`'s
 * `fs_byte_index_eq` bridging lemma, no new axiom).
 * ------------------------------------------------------------------------ *)
val lemma_byte_index_at_middle (prefix mid suffix : string) (i : nat)
  : Lemma (requires i < fs_byte_length mid)
          (ensures fs_byte_index (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + i)
                   == fs_byte_index mid i)
let lemma_byte_index_at_middle prefix mid suffix i =
  let p = fs_byte_length prefix in
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  fs_byte_at_concat prefix (mid ^ suffix) (p + i);
  fs_byte_at_concat mid suffix i;
  fs_byte_index_eq (prefix ^ (mid ^ suffix)) (p + i);
  fs_byte_index_eq mid i

(** ------------------------------------------------------------------------
 * Sub-lemma 2 (the PILOT theorem): `lemma_scan_iri_end_shift` -- the
 * shift/locality lemma for `scan_iri_end` itself.
 *
 * STATEMENT. If `scan_iri_end mid i fuel` finds the terminating `>` at
 * some position `gt_pos` STRICTLY INSIDE `mid` (i.e. `mid` is not cut
 * off mid-scan -- exactly "the scan cannot run past the line end", the
 * task brief's own precondition, stated here as the concrete fact this
 * scanner actually needs rather than a vaguer "line ends in `>` or
 * newline": `scan_iri_end` itself only ever terminates successfully on
 * `>`, so `gt_pos < fs_byte_length mid` IS "the scan found its
 * terminator without running off the end of `mid`"), then running the
 * SAME scan on `mid` embedded at position `fs_byte_length prefix` inside
 * `prefix ^ (mid ^ suffix)`, with the SAME fuel, finds the SAME
 * terminator at the SHIFTED position.
 *
 * PROOF. Induction on `fuel`, `rec`-mirroring `scan_iri_end`'s own
 * recursion branch-for-branch:
 *   - `fuel = 0`: `scan_iri_end mid i 0` unfolds (by `mid`'s own
 *     definitional equation, concrete on the literal `0`) to `ParseFail
 *     "IRI too long" i` -- contradicts the `requires`'s `ParseOk`, so
 *     the goal holds vacuously. No explicit contradiction lemma needed;
 *     ordinary constructor disjointness (`ParseOk <> ParseFail`) closes
 *     it once both sides are in Z3's context.
 *   - `i >= fs_byte_length mid`: symmetric -- unfolds to `ParseFail
 *     "unterminated IRI" i`, same vacuous contradiction.
 *   - Otherwise (`fuel > 0 /\ i < fs_byte_length mid`): establish the
 *     TWO length facts (`fs_byte_length_concat` on `mid`/`suffix` then
 *     on `prefix`/`(mid^suffix)`) needed so `full`'s own `pos >= len`
 *     check takes the SAME branch as `mid`'s (both false, since `i <
 *     fs_byte_length mid <= fs_byte_length full - fs_byte_length
 *     prefix`); apply sub-lemma 1 to get the byte-read agreement at this
 *     ONE position; then case on the shared byte's code exactly as
 *     `scan_iri_end` itself does:
 *       - `0x3E`: both scans return `ParseOk` at their respective
 *         (shifted) current position; `mid`'s own unfolded equation
 *         forces `gt_pos = i` (via `ParseOk` constructor injectivity
 *         against the `requires` hypothesis), closing the goal by
 *         `nat` arithmetic (`p + gt_pos == p + i`).
 *       - `0x5C` / control-or-forbidden: `mid`'s scan fails here,
 *         contradicting `requires` -- vacuous, same as the two base
 *         cases above.
 *       - otherwise: recurse at `(i + 1, fuel - 1)`, unchanged `gt_pos`.
 *         `fs_byte_length prefix + (i + 1) == (fs_byte_length prefix +
 *         i) + 1` is plain `nat` arithmetic, needing no string fact and
 *         no separate helper.
 * ------------------------------------------------------------------------ *)
val lemma_scan_iri_end_shift (prefix mid suffix : string) (i fuel : nat) (gt_pos : nat)
  : Lemma
      (requires
        scan_iri_end mid i fuel == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid)
      (ensures
        scan_iri_end (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + i) fuel
          == ParseOk (fs_byte_length prefix + gt_pos) (fs_byte_length prefix + gt_pos))
      (decreases fuel)
let rec lemma_scan_iri_end_shift prefix mid suffix i fuel gt_pos =
  let p = fs_byte_length prefix in
  if fuel = 0 then
    // scan_iri_end mid i 0 == ParseFail "IRI too long" i (mid's own
    // definitional unfolding on the concrete literal fuel=0) contradicts
    // the requires clause's ParseOk equation -- vacuous.
    ()
  else begin
    let len_mid = fs_byte_length mid in
    if i >= len_mid then
      // scan_iri_end mid i fuel == ParseFail "unterminated IRI" i --
      // contradicts requires -- vacuous.
      ()
    else begin
      // -- length facts so `full`'s own `pos >= len` check lines up
      // -- with `mid`'s (both false here, i < len_mid) --
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      // -- byte-read agreement at this one position --
      lemma_byte_index_at_middle prefix mid suffix i;
      let ch = fs_byte_index mid i in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then
        // Base case: scan_iri_end mid i fuel == ParseOk i i, forcing
        // (via requires + ParseOk constructor injectivity) gt_pos == i.
        // scan_iri_end full (p+i) fuel == ParseOk (p+i) (p+i) by full's
        // own unfolding (same code, same branch) -- matches the goal
        // since p + gt_pos == p + i.
        ()
      else if code = 0x5C then
        // scan_iri_end mid i fuel == ParseFail "has escapes" i --
        // contradicts requires -- vacuous.
        ()
      else if code <= 0x20 || is_iri_forbidden_codepoint code then
        // scan_iri_end mid i fuel == ParseFail "invalid character in IRI"
        // i -- contradicts requires -- vacuous.
        ()
      else
        // Recursive case: scan_iri_end mid i fuel ==
        // scan_iri_end mid (i+1) (fuel-1) (mid's own equation), so the
        // requires hypothesis transfers unchanged to (i+1, fuel-1, same
        // gt_pos). scan_iri_end full (p+i) fuel == scan_iri_end full
        // (p+i+1) (fuel-1) (full's own equation, same branch taken by
        // byte-read agreement above) == scan_iri_end full ((p+(i+1)))
        // (fuel-1) by nat arithmetic -- exactly the recursive call's
        // postcondition.
        lemma_scan_iri_end_shift prefix mid suffix (i + 1) (fuel - 1) gt_pos
    end
  end

(** ------------------------------------------------------------------------
 * Corollary: the shape `parse_iri_raw` actually uses -- the IRI content
 * starts at `i = 0` relative to `mid` (`start = pos + 1` right after the
 * opening `<`, with `mid` being everything from there). Stated
 * separately since this is the entry point the remaining combinators
 * (`parse_iri_raw` itself, then `parse_subject`/`parse_object` which
 * call it) will actually invoke, not just a special case worth leaving
 * implicit.
 * ------------------------------------------------------------------------ *)
val lemma_scan_iri_end_shift_from_start (prefix mid suffix : string) (fuel gt_pos : nat)
  : Lemma
      (requires
        scan_iri_end mid 0 fuel == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid)
      (ensures
        scan_iri_end (prefix ^ (mid ^ suffix)) (fs_byte_length prefix) fuel
          == ParseOk (fs_byte_length prefix + gt_pos) (fs_byte_length prefix + gt_pos))
let lemma_scan_iri_end_shift_from_start prefix mid suffix fuel gt_pos =
  lemma_scan_iri_end_shift prefix mid suffix 0 fuel gt_pos

#pop-options

(** ========================================================================
 * WHAT THE TEMPLATE MEANS FOR THE REMAINING COMBINATORS.
 *
 * `scan_iri_end` was the SIMPLEST case on purpose (position-only return,
 * no accumulator). Estimating the remaining call graph
 * `parse_iri_raw`/`parse_iri`/`parse_subject`/`parse_object` needs by
 * this template, in increasing order of new difficulty:
 *
 *   - `parse_iri_raw` (Parser.NTriples.fst, the function that CALLS
 *     `scan_iri_end`): SAME SHAPE, one layer up. Its fast path is
 *     `scan_iri_end` (now covered) followed by ONE `fs_byte_sub input
 *     start iri_len` call -- needs `fs_byte_sub_concat_left`/`_right`
 *     (already proved facts 5a/5b in Parser.FastString.Axioms.fst, no
 *     new proof) composed with THIS lemma's `gt_pos` to show the
 *     extracted substring is unchanged under embedding. Its escape path
 *     falls back to `parse_iri_body_acc`, which is genuinely new work
 *     (see below) -- but `parse_iri_raw`'s fast-path locality lemma
 *     itself is a direct corollary of `lemma_scan_iri_end_shift_from_
 *     start` plus one `fs_byte_sub_concat_*` call, not a new induction.
 *
 *   - `parse_iri` (wraps `parse_iri_raw` with an `is_iri` well-
 *     formedness check on the extracted string): SAME SHAPE again --
 *     once `parse_iri_raw`'s locality lemma gives the identical
 *     extracted string, `is_iri`'s result is a pure function OF that
 *     string, so it is unchanged for free. No new induction.
 *
 *   - `parse_iri_body_acc` (the escape/backslash slow path): NEW
 *     DIFFICULTY -- unlike `scan_iri_end`, this function THREADS AN
 *     ACCUMULATOR (`acc : list string`) that changes shape every
 *     iteration (`fs_utf8_of_codepoint cp :: acc` or `fs_byte_sub input
 *     pos 1 :: acc`) and finishes with `String.concat "" (List.Tot.rev
 *     acc)` -- a call into `FStar.String.concat`, which `RDF.NTriples
 *     .RoundTrip.fst`'s own Part 6 banner and `Parser.FastString.Axioms
 *     .fst`'s banner BOTH name as a separate, still-open wall (the
 *     "FStar.String.concat gap" the Axioms file's banner references).
 *     The per-position locality argument (the `fs_byte_at`/`fs_byte_
 *     index` half) is the SAME template as `scan_iri_end`'s recursive
 *     case, extended with `hex_val_opt` reads at up to 10 further
 *     positions per `\U` escape -- mechanical but longer. The
 *     ACCUMULATOR equality at the end is the new, harder half, and is
 *     NOT reducible to this template without first crossing the
 *     `FStar.String.concat` wall. Estimate: same shape for the scan
 *     itself, genuinely new difficulty for the finish.
 *
 *   - `parse_subject`/`parse_object` (Parser.NTriples.fst): dispatch on
 *     the lead byte (`<` -> IRI via `parse_iri`, `_` -> `parse_bnode`)
 *     then call `pws` (`ptake_while is_nt_ws`, Parser.Combinators.fst) --
 *     ANOTHER position-only recursive scanner, exactly `scan_iri_end`'s
 *     shape (no accumulator, terminates on a predicate going false
 *     rather than a specific byte) -- SAME SHAPE, the identical template
 *     applies with `is_nt_ws` in place of `code = 0x3E`/forbidden-check.
 *     `parse_object`'s literal branch additionally calls `parse_literal`
 *     (language tags, `^^` datatype IRIs, quoted-string escape decoding)
 *     which shares `parse_iri_body_acc`'s accumulator-plus-`String.
 *     concat` shape for its escape handling -- same NEW-difficulty class
 *     as that function, not the `scan_iri_end`/`pws` class.
 *
 * SUMMARY: `scan_iri_end`, `parse_iri_raw`, `parse_iri`, and `pws` (hence
 * the position-only skeleton of `parse_subject`/`parse_object`) are ALL
 * "same shape" as this landing's template -- mechanical repetition, no
 * new proof idea. `parse_iri_body_acc` and `parse_literal`'s escape
 * decoding are "new difficulty": both need an `FStar.String.concat`
 * locality fact this landing does not attempt (a separate, already-
 * named wall, not a surprise from this session). NOT attempted further
 * this landing per the guard-depth rule -- this is the sharpened next
 * rung, not a vague "harder than expected".
 * ======================================================================== *)
