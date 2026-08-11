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
open RDF.Term
open Parser.NQuads

module Spec = Parser.FastString.Spec

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

(** ------------------------------------------------------------------------
 * Sub-lemma 3: `lemma_scan_iri_end_shift_headroom` -- generalises
 * sub-lemma 2 with an extra fuel-headroom parameter on the FULL side.
 *
 * WHY THIS IS NEEDED (not just a generalisation for its own sake).
 * `parse_iri_raw`'s ACTUAL fuel is `fs_byte_length input - pos`, which is
 * DIFFERENT for `mid` (`fs_byte_length mid - pos`) and for the SAME scan
 * embedded in `full = prefix ^ (mid ^ suffix)` at the shifted position
 * (`fs_byte_length full - (fs_byte_length prefix + pos)`). Expanding via
 * `fs_byte_length_concat` twice: the full-side fuel equals the mid-side
 * fuel PLUS `fs_byte_length suffix`, exactly. Sub-lemma 2 required the
 * SAME numeric fuel on both sides, which is true only when `suffix = ""`
 * -- too narrow for `parse_iri_raw`'s real call sites. This lemma adds
 * an `extra:nat` parameter threaded unchanged through the recursion
 * (both sides decrement their own fuel by 1 per step, so `extra` stays
 * constant) so it can be instantiated with `extra = fs_byte_length
 * suffix` at the composition site (`lemma_parse_iri_raw_fastpath_shift`
 * below) with NO separate fuel-monotonicity lemma needed.
 *
 * WHY A GENERAL "fuel2 >= fuel1 implies same result" MONOTONICITY LEMMA
 * WOULD NOT WORK HERE (recorded so a future session does not re-derive
 * this and waste an attempt): `scan_iri_end`'s `fuel = 0` case ALWAYS
 * fails (`ParseFail "IRI too long"`), so unlike `ptake_while_acc` below,
 * there is no "coincidental success at fuel=0" case to guard against --
 * extending the fuel value can only ever let the SAME successful scan
 * run to completion, never change its outcome. That is exactly why the
 * proof below is a direct copy of sub-lemma 2's structure with `extra`
 * inserted, no new precondition needed.
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_scan_iri_end_shift_headroom
    (prefix mid suffix : string) (i fuel extra : nat) (gt_pos : nat)
  : Lemma
      (requires
        scan_iri_end mid i fuel == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid)
      (ensures
        scan_iri_end (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + i) (fuel + extra)
          == ParseOk (fs_byte_length prefix + gt_pos) (fs_byte_length prefix + gt_pos))
      (decreases fuel)
let rec lemma_scan_iri_end_shift_headroom prefix mid suffix i fuel extra gt_pos =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if i >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix i;
      let ch = fs_byte_index mid i in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then ()
      else if code = 0x5C then ()
      else if code <= 0x20 || is_iri_forbidden_codepoint code then ()
      else
        lemma_scan_iri_end_shift_headroom prefix mid suffix (i + 1) (fuel - 1) extra gt_pos
    end
  end
#pop-options

(** ------------------------------------------------------------------------
 * Sub-lemma 4: `lemma_ptake_while_acc_pos_shift_headroom` -- the
 * position-AND-string shift lemma for `ptake_while_acc`, the accumulator
 * combinator `pws` (via `ptake_while`, Parser.Combinators.fst) actually
 * recurses through -- NOT `ptake_while_scan`/`ptake_while_pos`, which are
 * position-only but have NO caller in the subject/object/whitespace path
 * (confirmed by reading Parser.Combinators.fst: `pws` at
 * Parser.NTriples.fst:94 calls `ptake_while`, which calls
 * `ptake_while_acc`).
 *
 * WHY THIS NEEDS A DIFFERENT PRECONDITION THAN SUB-LEMMA 3.
 * `ptake_while_acc`'s `fuel = 0` case SUCCEEDS (`ParseOk (str_of acc)
 * pos`, unconditionally, regardless of whether the predicate would have
 * continued matching) -- unlike `scan_iri_end`'s `fuel = 0`, which always
 * FAILS. A plain "same/more fuel gives the same result" claim is
 * therefore FALSE in general: if `fuel` happens to hit 0 exactly at a
 * position whose predicate is still true, a LARGER `fuel` would keep
 * scanning past it. The fix is the extra hypothesis `fuel + pos >=
 * endpos + 1`, i.e. "fuel had not yet run out at the point the scan
 * reports as its stop" -- this is exactly what rules out the
 * fuel-exhaustion artifact and pins the stop down as a genuine
 * predicate-false (or genuine `pos >= length` hit, already excluded by
 * `endpos < fs_byte_length mid`) event, at which point extending the
 * full side's fuel by a constant `extra` cannot change anything either
 * (the recursion never reaches its own `fuel = 0` check before this
 * point, so `extra` is inert until then, and after the stop it is never
 * consulted again). `pws` (Parser.Combinators.fst:316-320, via
 * `ptake_while pred input pos = ptake_while_acc pred input pos [] (len -
 * pos + 1)`) always supplies `fuel = fs_byte_length input - pos + 1`,
 * which makes `fuel + pos >= endpos + 1` hold automatically whenever
 * `endpos <= fs_byte_length input` -- i.e. `ptake_while`'s own fuel
 * formula is ALWAYS "sufficient" in this sense, so the composition at
 * `lemma_pws_shift` below discharges this hypothesis for free.
 *
 * WHY THE STRING RESULT (`out_s`) IS THE SAME ON BOTH SIDES FOR FREE
 * (the Stage-2 insight from the task brief, landing one stage early
 * because `pws`'s recursion already goes through the accumulator
 * combinator): `acc` is threaded as the SAME value into both the `mid`
 * call and the `full` call at every step of this induction (never two
 * independently-evolving accumulators) -- so when the recursion
 * terminates, both sides compute `String.concat "" (List.Tot.rev acc)`
 * (well, `String.string_of_list` here) over the LITERALLY SAME `acc`.
 * No `FStar.String.concat`/`strcat` algebra is invoked anywhere in this
 * proof; the string equality follows from applying the SAME pure
 * function to the SAME argument, which is definitional congruence, not
 * string-equational reasoning. (`pws` itself goes on to discard this
 * string entirely -- `match ptake_while ... with ParseOk _ pos' -> ...`
 * -- so `lemma_pws_shift` below does not even need this corollary, but
 * it costs nothing extra to state and may serve a future caller that
 * DOES need the extracted substring, e.g. `ptake_while1`.)
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_ptake_while_acc_pos_shift_headroom
    (pred: FStar.Char.char -> bool) (prefix mid suffix : string)
    (pos fuel extra : nat) (acc : list FStar.Char.char) (endpos : nat) (out_s : string)
  : Lemma
      (requires
        ptake_while_acc pred mid pos acc fuel == ParseOk out_s endpos /\
        endpos < fs_byte_length mid /\
        fuel + pos >= endpos + 1)
      (ensures
        ptake_while_acc pred (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) acc (fuel + extra)
          == ParseOk out_s (fs_byte_length prefix + endpos))
      (decreases fuel)
let rec lemma_ptake_while_acc_pos_shift_headroom pred prefix mid suffix pos fuel extra acc endpos out_s =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if pos >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix pos;
      let ch = fs_byte_index mid pos in
      if pred ch then
        lemma_ptake_while_acc_pos_shift_headroom pred prefix mid suffix (pos + 1) (fuel - 1) extra (ch :: acc) endpos out_s
      else ()
    end
  end
#pop-options

(** ------------------------------------------------------------------------
 * Sub-lemma 5 (the `pws` shift lemma): compose sub-lemma 4 with `pws`'s
 * ACTUAL fuel formula (`ptake_while`'s `fs_byte_length input - pos + 1`)
 * on both sides, discharging the `fuel + pos >= endpos + 1` side
 * condition automatically (see sub-lemma 4's banner) and discarding the
 * string result exactly as `pws` itself does.
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_pws_shift (prefix mid suffix : string) (pos : nat) (endpos : nat)
  : Lemma
      (requires
        pos <= fs_byte_length mid /\
        pws mid pos == ParseOk () endpos /\
        endpos < fs_byte_length mid)
      (ensures
        pws (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos)
          == ParseOk () (fs_byte_length prefix + endpos))
let lemma_pws_shift prefix mid suffix pos endpos =
  let p = fs_byte_length prefix in
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  // fuel_full == fuel_mid + fs_byte_length suffix, by the length facts above
  // (plain nat/int arithmetic once the two fs_byte_length_concat equations
  // are in context -- no separate helper).
  let fuel_mid = fs_byte_length mid - pos + 1 in
  match ptake_while_acc is_nt_ws mid pos [] fuel_mid with
  | ParseOk out_s stop ->
    lemma_ptake_while_acc_pos_shift_headroom is_nt_ws prefix mid suffix pos fuel_mid (fs_byte_length suffix) [] stop out_s
  | ParseFail _ _ -> ()
#pop-options
#pop-options

(** ------------------------------------------------------------------------
 * Sub-lemma 6: `lemma_parse_iri_raw_fastpath_shift` -- the shift lemma
 * for `parse_iri_raw`'s FAST path (banner's estimate: "a direct
 * corollary of `lemma_scan_iri_end_shift_from_start` plus one
 * `fs_byte_sub_concat_*` call, not a new induction" -- confirmed here).
 * Scope: only the case where `mid`'s scan finds its terminator strictly
 * inside `mid` on the no-escape fast path (the same `gt_pos <
 * fs_byte_length mid` discipline as every lemma above); the escape path
 * (`parse_iri_body_acc`) is Stage 2, not covered by this lemma.
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_iri_raw_fastpath_shift (prefix mid suffix : string) (pos gt_pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x3C /\
        scan_iri_end mid (pos + 1) (fs_byte_length mid - pos) == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid)
      (ensures
        (match parse_iri_raw mid pos,
               parse_iri_raw (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk iri_mid endpos_mid, ParseOk iri_full endpos_full ->
           iri_full == iri_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_iri_raw_fastpath_shift prefix mid suffix pos gt_pos =
  let p = fs_byte_length prefix in
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  lemma_byte_index_at_middle prefix mid suffix pos;
  let fuel_mid = fs_byte_length mid - pos in
  lemma_scan_iri_end_shift_headroom prefix mid suffix (pos + 1) fuel_mid (fs_byte_length suffix) gt_pos;
  let start = pos + 1 in
  let iri_len = gt_pos - start in
  if iri_len > 0 && start + iri_len <= fs_byte_length mid then begin
    fs_byte_sub_concat_right prefix (mid ^ suffix) (p + start) iri_len;
    fs_byte_sub_concat_left mid suffix start iri_len
  end else ()
#pop-options

(** ------------------------------------------------------------------------
 * Sub-lemma 7: `lemma_parse_iri_shift` -- `parse_iri` wraps
 * `parse_iri_raw` with an `is_iri` well-formedness check purely on the
 * extracted string (Parser.NTriples.fst:244). Sub-lemma 6 already gives
 * the identical extracted string on both sides, so `is_iri`'s result
 * (a pure function of that string) is unchanged for free -- direct
 * corollary, no new induction, as the file-end banner estimated.
 * Scope: the SUCCESS case only (`is_iri` holds) -- matches what
 * `parse_subject`/`parse_object`'s position-only skeleton (sub-lemmas 8
 * and 9 below) actually need.
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_iri_shift (prefix mid suffix : string) (pos gt_pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x3C /\
        scan_iri_end mid (pos + 1) (fs_byte_length mid - pos) == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid /\
        (match parse_iri_raw mid pos with
         | ParseOk iri_mid _ -> is_iri iri_mid
         | ParseFail _ _ -> False))
      (ensures
        (match parse_iri mid pos,
               parse_iri (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk i_mid endpos_mid, ParseOk i_full endpos_full ->
           i_full == i_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_iri_shift prefix mid suffix pos gt_pos =
  lemma_parse_iri_raw_fastpath_shift prefix mid suffix pos gt_pos
#pop-options

(** ------------------------------------------------------------------------
 * Sub-lemmas 8/9: `lemma_parse_subject_iri_shift` /
 * `lemma_parse_object_iri_shift` -- the "position-only skeleton" the
 * file-end banner calls for: `parse_subject`/`parse_object`
 * (Parser.NTriples.fst:591,615) dispatch on the lead byte, and for `<`
 * (0x3C) call `parse_iri`, wrapping its result in `S_IRI`/`T_IRI`. Given
 * the lead byte is `<` (transferred via the same byte-agreement lemma
 * used throughout this file) and sub-lemma 7's identical extraction,
 * both sides take the SAME branch and wrap the SAME extracted IRI in
 * the SAME constructor -- congruence, no new induction.
 *
 * SCOPE (matches the banner precisely): the `<` (IRI) branch only. The
 * `_` (blank-node, via `parse_bnode`) branch is NOT covered -- it scans
 * via `fs_cp_at`/codepoint-length advances (Parser.NTriples.fst:309-326,
 * `scan_bnode_body_cp`), a genuinely different locality argument (needs
 * a codepoint-level, not byte-level, shift fact for `fs_cp_at` under
 * embedding -- no such fact is proved in Parser.FastString.Axioms.fst
 * today). `parse_object`'s `"` (literal, via `parse_literal`) branch is
 * likewise not covered -- it shares `parse_iri_body_acc`'s
 * accumulator-plus-escape shape, the Stage-2 "new difficulty" class.
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_subject_iri_shift (prefix mid suffix : string) (pos gt_pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x3C /\
        scan_iri_end mid (pos + 1) (fs_byte_length mid - pos) == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid /\
        (match parse_iri_raw mid pos with
         | ParseOk iri_mid _ -> is_iri iri_mid
         | ParseFail _ _ -> False))
      (ensures
        (match parse_subject mid pos,
               parse_subject (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk s_mid endpos_mid, ParseOk s_full endpos_full ->
           s_full == s_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_subject_iri_shift prefix mid suffix pos gt_pos =
  lemma_byte_index_at_middle prefix mid suffix pos;
  lemma_parse_iri_shift prefix mid suffix pos gt_pos
#pop-options

#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_object_iri_shift (prefix mid suffix : string) (pos gt_pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x3C /\
        scan_iri_end mid (pos + 1) (fs_byte_length mid - pos) == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid /\
        (match parse_iri_raw mid pos with
         | ParseOk iri_mid _ -> is_iri iri_mid
         | ParseFail _ _ -> False))
      (ensures
        (match parse_object mid pos,
               parse_object (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk t_mid endpos_mid, ParseOk t_full endpos_full ->
           t_full == t_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_object_iri_shift prefix mid suffix pos gt_pos =
  lemma_byte_index_at_middle prefix mid suffix pos;
  lemma_parse_iri_shift prefix mid suffix pos gt_pos
#pop-options

(** ========================================================================
 * STAGE 2 (task #48 brief): `parse_iri_body_acc`, the escape/backslash
 * slow path -- the file-end banner's "new difficulty" case, attempted
 * here with the brief's own suggested resolution.
 *
 * THE ACCUMULATOR-CONCAT WALL, AND WHY IT DOES NOT APPLY TO A LOCALITY
 * LEMMA. `parse_iri_body_acc` threads `acc : list string` and finishes
 * with `String.concat "" (List.Tot.rev acc)` -- `RDF.NTriples.RoundTrip
 * .fst`'s Part 6 and `Parser.FastString.Axioms.fst`'s banner both name
 * `FStar.String.concat`/`strcat` ALGEBRA (`"" ^ s == s`, `(a^b)^c ==
 * a^(b^c)`) as a wall Z3 cannot discharge for SYMBOLIC string operands.
 * A shift/locality lemma never needs that algebra: it needs "the mid
 * run and the full run compute the SAME accumulator", after which the
 * SAME pure function (`String.concat "" (List.Tot.rev _)`) applied to
 * EQUAL arguments gives an equal result by plain congruence -- zero
 * concat equations invoked. Below, `acc_mid`/`acc_full` are threaded as
 * SEPARATE parameters with an explicit `acc_mid == acc_full` hypothesis
 * (not one shared variable, unlike sub-lemma 4's `list char` case)
 * because two of this function's cons elements are NOT syntactically
 * identical between the two runs even though they are VALUE-equal:
 * `fs_byte_sub input pos 1` differs textually for `mid` vs `full` (only
 * `fs_byte_sub_concat_left`/`_right`, Axioms facts 5a/5b, connect them,
 * same composition as sub-lemma 6's IRI-content extraction). The
 * `\u`/`\U` escape branches push `fs_utf8_of_codepoint cp` on both
 * sides, where `cp` is computed identically from hex digits read via
 * `lemma_byte_index_at_middle`-proved-equal chars -- so `cp_mid ==
 * cp_full` as the SAME integer (no separate lemma), and the pushed
 * fragment is syntactically the SAME expression, needing no
 * `fs_byte_sub_concat_*` call at all in that branch.
 *
 * WHY THE FUEL SIDE IS SIMPLER THAN SUB-LEMMA 4 (`ptake_while_acc`).
 * `parse_iri_body_acc`'s `fuel = 0` case FAILS (`ParseFail "IRI too
 * long"`, same as `scan_iri_end`), unlike `ptake_while_acc`'s, which
 * SUCCEEDS unconditionally at `fuel = 0`. A `ParseOk` hypothesis at
 * `fuel = 0` is therefore already a direct contradiction (mid's own
 * unfolded equation gives `ParseFail`) -- no `fuel + pos >= endpos + 1`
 * side condition needed; plain fuel-headroom (`extra` added on the full
 * side, unconditionally) suffices, exactly sub-lemma 3's pattern.
 * ======================================================================== *)
#push-options "--z3rlimit 300 --fuel 6 --ifuel 6"
val lemma_parse_iri_body_acc_shift
    (prefix mid suffix : string) (pos fuel extra : nat)
    (acc_mid acc_full : list string) (endpos : nat) (out_s : string)
  : Lemma
      (requires
        acc_mid == acc_full /\
        parse_iri_body_acc mid pos acc_mid fuel == ParseOk out_s endpos /\
        endpos <= fs_byte_length mid)
      (ensures
        parse_iri_body_acc (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) acc_full (fuel + extra)
          == ParseOk out_s (fs_byte_length prefix + endpos))
      (decreases fuel)
let rec lemma_parse_iri_body_acc_shift prefix mid suffix pos fuel extra acc_mid acc_full endpos out_s =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if pos >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix pos;
      let ch = fs_byte_index mid pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then ()
      else if code = 0x5C then begin
        if pos + 1 >= len_mid then ()
        else begin
          lemma_byte_index_at_middle prefix mid suffix (pos + 1);
          let next = fs_byte_index mid (pos + 1) in
          let ncode = FStar.Char.int_of_char next in
          if ncode = 0x75 then begin
            if pos + 6 > len_mid then ()
            else begin
              lemma_byte_index_at_middle prefix mid suffix (pos + 2);
              lemma_byte_index_at_middle prefix mid suffix (pos + 3);
              lemma_byte_index_at_middle prefix mid suffix (pos + 4);
              lemma_byte_index_at_middle prefix mid suffix (pos + 5);
              match hex_val_opt (fs_byte_index mid (pos + 2)),
                    hex_val_opt (fs_byte_index mid (pos + 3)),
                    hex_val_opt (fs_byte_index mid (pos + 4)),
                    hex_val_opt (fs_byte_index mid (pos + 5)) with
              | Some h0, Some h1, Some h2, Some h3 ->
                let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
                if not (valid_codepoint cp) then ()
                else if is_iri_forbidden_codepoint cp then ()
                else
                  lemma_parse_iri_body_acc_shift prefix mid suffix (pos + 6) (fuel - 1) extra
                    (fs_utf8_of_codepoint cp :: acc_mid) (fs_utf8_of_codepoint cp :: acc_full) endpos out_s
              | _ -> ()
            end
          end
          else if ncode = 0x55 then begin
            if pos + 10 > len_mid then ()
            else begin
              lemma_byte_index_at_middle prefix mid suffix (pos + 2);
              lemma_byte_index_at_middle prefix mid suffix (pos + 3);
              lemma_byte_index_at_middle prefix mid suffix (pos + 4);
              lemma_byte_index_at_middle prefix mid suffix (pos + 5);
              lemma_byte_index_at_middle prefix mid suffix (pos + 6);
              lemma_byte_index_at_middle prefix mid suffix (pos + 7);
              lemma_byte_index_at_middle prefix mid suffix (pos + 8);
              lemma_byte_index_at_middle prefix mid suffix (pos + 9);
              match hex_val_opt (fs_byte_index mid (pos + 2)),
                    hex_val_opt (fs_byte_index mid (pos + 3)),
                    hex_val_opt (fs_byte_index mid (pos + 4)),
                    hex_val_opt (fs_byte_index mid (pos + 5)),
                    hex_val_opt (fs_byte_index mid (pos + 6)),
                    hex_val_opt (fs_byte_index mid (pos + 7)),
                    hex_val_opt (fs_byte_index mid (pos + 8)),
                    hex_val_opt (fs_byte_index mid (pos + 9)) with
              | Some h0, Some h1, Some h2, Some h3, Some h4, Some h5, Some h6, Some h7 ->
                let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) + (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536)
                       + (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) + (h6 `op_Multiply` 16) + h7) in
                if not (valid_codepoint cp) then ()
                else if is_iri_forbidden_codepoint cp then ()
                else
                  lemma_parse_iri_body_acc_shift prefix mid suffix (pos + 10) (fuel - 1) extra
                    (fs_utf8_of_codepoint cp :: acc_mid) (fs_utf8_of_codepoint cp :: acc_full) endpos out_s
              | _ -> ()
            end
          end
          else ()
        end
      end
      else if code <= 0x20 || is_iri_forbidden_codepoint code then ()
      else begin
        fs_byte_sub_concat_right prefix (mid ^ suffix) (p + pos) 1;
        fs_byte_sub_concat_left mid suffix pos 1;
        lemma_parse_iri_body_acc_shift prefix mid suffix (pos + 1) (fuel - 1) extra
          (fs_byte_sub mid pos 1 :: acc_mid) (fs_byte_sub mid pos 1 :: acc_full) endpos out_s
      end
    end
  end
#pop-options

(** ------------------------------------------------------------------------
 * Capstone: `lemma_parse_iri_raw_shift` -- unifies sub-lemma 6 (fast
 * path) and the Stage-2 `lemma_parse_iri_body_acc_shift` (escape path)
 * into a single shift lemma for `parse_iri_raw` covering BOTH paths, by
 * casing on which branch `scan_iri_end` itself took (mirroring
 * `parse_iri_raw`'s own `match`). This is the lemma a future Stage-3
 * session composes into `parse_subject`/`parse_iri`/`parse_object`
 * without an escape-path carve-out.
 *
 * `lemma_scan_iri_end_success_bound` is a small structural fact needed
 * to supply the `gt_pos < fs_byte_length mid` witness the fast-path
 * lemma requires: `scan_iri_end`'s ONLY `ParseOk` return
 * (Parser.NTriples.fst:213, `code = 0x3E`) fires strictly inside the
 * `pos < len` branch, so success always implies the bound -- proved
 * once here rather than re-required of every caller.
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_scan_iri_end_success_bound (input : string) (pos fuel : nat) (gt_pos : nat)
  : Lemma (requires scan_iri_end input pos fuel == ParseOk gt_pos gt_pos)
          (ensures gt_pos < fs_byte_length input)
      (decreases fuel)
let rec lemma_scan_iri_end_success_bound input pos fuel gt_pos =
  if fuel = 0 then ()
  else
    let len = fs_byte_length input in
    if pos >= len then ()
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then ()
      else if code = 0x5C then ()
      else if code <= 0x20 || is_iri_forbidden_codepoint code then ()
      else lemma_scan_iri_end_success_bound input (pos + 1) (fuel - 1) gt_pos
#pop-options

(* `parse_result nat`'s `ParseOk` constructor carries two independent
   `nat` fields at the TYPE level -- nothing there forces them equal.
   `scan_iri_end` only ever CONSTRUCTS a `ParseOk` with equal fields
   (`ParseOk pos pos`, Parser.NTriples.fst:213), but a caller that
   pattern-matches abstractly (`match scan_iri_end ... with ParseOk a b
   -> ...`, as `lemma_parse_iri_raw_shift` below does, mirroring
   `parse_iri_raw`'s own match) gets two UNRELATED bound variables from
   that match alone -- confirmed by a first attempt at this capstone
   failing Error 19 exactly at the point of reusing `lemma_scan_iri_end_
   success_bound`'s `ParseOk gt_pos gt_pos` precondition. This lemma
   supplies the missing link once, by the same structural mirror as
   every lemma above. *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_scan_iri_end_result_eq (input : string) (pos fuel : nat) (a b : nat)
  : Lemma (requires scan_iri_end input pos fuel == ParseOk a b)
          (ensures a == b)
      (decreases fuel)
let rec lemma_scan_iri_end_result_eq input pos fuel a b =
  if fuel = 0 then ()
  else
    let len = fs_byte_length input in
    if pos >= len then ()
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then ()
      else if code = 0x5C then ()
      else if code <= 0x20 || is_iri_forbidden_codepoint code then ()
      else lemma_scan_iri_end_result_eq input (pos + 1) (fuel - 1) a b
#pop-options

(* Symmetric success-bound fact for `parse_iri_body_acc`: its ONLY
   `ParseOk` return (Parser.NTriples.fst:151-152, the `code = 0x3E`
   branch) is `pos + 1`, with `pos < fs_byte_length input` already
   established by the earlier `pos >= len` check having failed -- so a
   successful escape-path parse always stops at or before the input's
   own length, the exact bound `lemma_parse_iri_body_acc_shift`'s
   `endpos <= fs_byte_length mid` precondition needs. *)
#push-options "--z3rlimit 150 --fuel 6 --ifuel 6"
val lemma_parse_iri_body_acc_success_bound (input : string) (pos : nat) (acc : list string) (fuel : nat) (out_s : string) (endpos : nat)
  : Lemma (requires parse_iri_body_acc input pos acc fuel == ParseOk out_s endpos)
          (ensures endpos <= fs_byte_length input)
      (decreases fuel)
let rec lemma_parse_iri_body_acc_success_bound input pos acc fuel out_s endpos =
  if fuel = 0 then ()
  else
    let len = fs_byte_length input in
    if pos >= len then ()
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3E then ()
      else if code = 0x5C then begin
        if pos + 1 >= len then ()
        else
          let next = fs_byte_index input (pos + 1) in
          let ncode = FStar.Char.int_of_char next in
          if ncode = 0x75 then begin
            if pos + 6 > len then ()
            else
              match hex_val_opt (fs_byte_index input (pos + 2)),
                    hex_val_opt (fs_byte_index input (pos + 3)),
                    hex_val_opt (fs_byte_index input (pos + 4)),
                    hex_val_opt (fs_byte_index input (pos + 5)) with
              | Some h0, Some h1, Some h2, Some h3 ->
                let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
                if not (valid_codepoint cp) then ()
                else if is_iri_forbidden_codepoint cp then ()
                else
                  lemma_parse_iri_body_acc_success_bound input (pos + 6) (fs_utf8_of_codepoint cp :: acc) (fuel - 1) out_s endpos
              | _ -> ()
          end
          else if ncode = 0x55 then begin
            if pos + 10 > len then ()
            else
              match hex_val_opt (fs_byte_index input (pos + 2)),
                    hex_val_opt (fs_byte_index input (pos + 3)),
                    hex_val_opt (fs_byte_index input (pos + 4)),
                    hex_val_opt (fs_byte_index input (pos + 5)),
                    hex_val_opt (fs_byte_index input (pos + 6)),
                    hex_val_opt (fs_byte_index input (pos + 7)),
                    hex_val_opt (fs_byte_index input (pos + 8)),
                    hex_val_opt (fs_byte_index input (pos + 9)) with
              | Some h0, Some h1, Some h2, Some h3, Some h4, Some h5, Some h6, Some h7 ->
                let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) + (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536)
                       + (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) + (h6 `op_Multiply` 16) + h7) in
                if not (valid_codepoint cp) then ()
                else if is_iri_forbidden_codepoint cp then ()
                else
                  lemma_parse_iri_body_acc_success_bound input (pos + 10) (fs_utf8_of_codepoint cp :: acc) (fuel - 1) out_s endpos
              | _ -> ()
          end
          else ()
      end
      else if code <= 0x20 || is_iri_forbidden_codepoint code then ()
      else
        lemma_parse_iri_body_acc_success_bound input (pos + 1) (fs_byte_sub input pos 1 :: acc) (fuel - 1) out_s endpos
#pop-options

(** ------------------------------------------------------------------------
 * FINDING (guard-depth-3 stop on THIS statement only -- everything above
 * this banner, including the three support lemmas just above
 * (`lemma_scan_iri_end_result_eq`, `lemma_scan_iri_end_success_bound`,
 * `lemma_parse_iri_body_acc_success_bound`), is verified and kept; only
 * the CAPSTONE composition below was abandoned).
 *
 * ATTEMPTED: a single `lemma_parse_iri_raw_shift` unifying sub-lemma 6
 * (fast path) and `lemma_parse_iri_body_acc_shift` (escape path, Stage
 * 2) into ONE shift lemma for `parse_iri_raw` covering both paths, by
 * casing on `scan_iri_end mid (pos+1) (fs_byte_length mid - pos)` the
 * same way `parse_iri_raw` itself does. This is NOT a requirement of
 * the task brief's Stage 1/2 (sub-lemma 6 already covers the fast path,
 * which is all Stage 1 asked for) -- it was an opportunistic capstone,
 * abandoned per the 3-attempt guard rather than pursued further.
 *
 * THREE ATTEMPTS, each restructuring the statement, not just retrying:
 *   1. `(requires ... /\ parse_iri_raw mid pos == ParseOk iri endpos /\
 *      endpos <= fs_byte_length mid) (ensures parse_iri_raw full ... ==
 *      ParseOk iri (p + endpos))`, with `iri`/`endpos` as EXTERNAL
 *      parameters. Failed: Error 19, "Could not prove post-condition",
 *      located at the `lemma_scan_iri_end_success_bound` call site --
 *      root cause found: `match scan_iri_end mid start fuel with
 *      ParseOk gt_pos _ -> ...` binds an UNCONSTRAINED second component
 *      (F* patterns are linear; `ParseOk gt_pos gt_pos` is not valid
 *      syntax for "both fields equal"), so the required `ParseOk gt_pos
 *      gt_pos` precondition of the earlier lemmas has no witness that
 *      the two fields agree. Fixed by adding
 *      `lemma_scan_iri_end_result_eq` (kept, verified) to supply that
 *      link explicitly.
 *   2. Same statement, `lemma_scan_iri_end_result_eq` added, plus a
 *      resource bump (`--z3rlimit 200` to `400`, `--fuel/--ifuel 4` to
 *      `6`). Failed identically: Error 19 at the SAME overall
 *      post-condition location (750,2-765,23 in that revision), no
 *      narrower diagnostic -- ruling out "just needs more budget" as
 *      the fix.
 *   3. Restated the `ensures` as a nested match (`match parse_iri_raw
 *      mid pos with ParseFail _ _ -> True | ParseOk iri_mid endpos_mid
 *      -> match parse_iri_raw full ... with ...`) instead of sub-lemma
 *      6/7's flat comma-match `match X, Y with ...`, reasoning that the
 *      original flat-match `| _, _ -> False` catch-all over-claims
 *      "mid fails implies full also fails" -- NOT proved true in
 *      general here (unlike sub-lemma 6, this capstone's `requires`
 *      does not pin down which `scan_iri_end` branch fires, so a
 *      genuine `parse_iri_raw mid pos` failure -- e.g. "invalid
 *      character in IRI" -- is a real, reachable case, and nothing
 *      rules out the embedding succeeding past `mid`'s end into
 *      `suffix` in that case). Also added
 *      `lemma_parse_iri_body_acc_success_bound` (kept, verified) to
 *      supply the escape-path bound the same way
 *      `lemma_scan_iri_end_success_bound` does for the fast path.
 *      Failed again: Error 19, "Could not prove post-condition", same
 *      overall shape, no per-branch detail from batch `fstar.exe`
 *      (F* MCP for a goal-level inspection was not reachable in this
 *      subagent's environment -- would be the next diagnostic step, not
 *      another blind restatement).
 *
 * WHAT THIS MEANS FOR A FUTURE ATTEMPT. The individual PIECES all
 * verify (`lemma_parse_iri_raw_fastpath_shift`,
 * `lemma_parse_iri_body_acc_shift`, `lemma_scan_iri_end_result_eq`,
 * `lemma_scan_iri_end_success_bound`,
 * `lemma_parse_iri_body_acc_success_bound`) -- what fails is composing
 * them behind a SINGLE outer `match scan_iri_end ... with` whose three
 * arms hand off to two DIFFERENT already-proved lemmas plus a vacuous
 * case, packaged as one `ensures`. A worthwhile next step, not tried
 * here: split into two separate lemmas (one per path, each with its OWN
 * narrow `requires` pinning which `scan_iri_end` branch fired -- exactly
 * sub-lemma 6's shape, extended to the escape path) rather than one
 * lemma dispatching internally; a caller (e.g. `parse_subject`/
 * `parse_object`'s eventual full-branch lemma) would then do the
 * dispatch itself, matching how `parse_iri_raw`'s OWN callers already
 * work. Downstream consumers needing "just the fast path" already have
 * it (sub-lemma 6/7); this FINDING blocks only a caller that needs
 * escape-path coverage too.
 * ------------------------------------------------------------------------ *)

(** ========================================================================
 * STAGE 3, ITEM 1 (task #48 ordered work list item 1): blank-node branch
 * locality (`parse_bnode`, via `scan_bnode_body_cp`) -- the banner above
 * (sub-lemmas 8/9) named this as needing "a codepoint-level, not byte-
 * level, shift fact for `fs_cp_at` under embedding -- no such fact is
 * proved in Parser.FastString.Axioms.fst today". This section derives
 * and proves that fact from FIRST PRINCIPLES (`Parser.FastString.Spec`'s
 * definitional `utf8_decode_at`), entirely self-contained in THIS module
 * -- Parser.FastString.Axioms.fsti's own banner is a hard "DO NOT WIDEN"
 * on its eight-fact OCaml-realisation-checked trust surface, so nothing
 * below touches that file; `Parser.FastString.Spec.fst` has no `.fsti`
 * (fully transparent to any importer), so composing directly against its
 * `utf8_decode_at`/`nth_byte` is additive, no shared-module churn, no
 * re-verification of Axioms/RoundTripLemmas/BaseCases needed.
 *
 * THE HARD PART, AND WHY IT NEEDS A NEW HYPOTHESIS `scan_iri_end`'s SHIFT
 * LEMMA DID NOT. `fs_cp_at` can read up to 4 bytes starting at `pos`
 * (`Parser.FastString.Spec.utf8_decode_at`'s lead-byte-determined 1/2/3/4-
 * byte forms). When `pos` sits within the last 1-3 bytes of `mid`, those
 * lookahead reads fall OFF THE END of `mid` alone (`nth_byte` returns
 * `None`) but land ON REAL BYTES of `suffix` once `mid` is embedded in
 * `prefix ^ (mid ^ suffix)` -- so a naive shift claim ("same `pos`, same
 * result") is FALSE in general: `suffix`'s bytes can "complete" what
 * looks like a truncated UTF-8 sequence at the tail of `mid`, decoding a
 * DIFFERENT codepoint under embedding than in `mid` alone (worked
 * example: `mid` ends in a lone 0xC2 lead byte -- decodes to U+FFFD/
 * advance-1 in `mid` alone, since there is no continuation byte to read
 * -- but if `suffix` starts with a genuine continuation byte 0x80-0xBF,
 * the SAME position decodes a real 2-byte codepoint once embedded).
 *
 * THE FIX (found here, not in any prior file): `Parser.FastString.Spec.
 * utf8_decode_at`'s OWN case structure treats "ran out of bytes" (`None`)
 * and "next byte exists but is not a continuation byte" (`Some b` with
 * `not (is_continuation b)`) IDENTICALLY -- both produce `(0xFFFD, 1)`
 * (see `utf8_decode_at`'s `match nth_byte bs (p+1) with None -> (0xFFFD,
 * 1) | Some b1 -> if not (is_continuation b1) then (0xFFFD, 1) else ...`,
 * repeated per lookahead byte). So the divergence above is impossible
 * whenever `suffix`'s OWN FIRST byte (if any) is not a continuation byte
 * -- the SAME position that was `None` in `mid` alone becomes `Some
 * (non-continuation)` in the embedding, and BOTH outcomes are `(0xFFFD,
 * 1)`. Crucially this holds for ANY overrun depth (1, 2, or 3 bytes past
 * `mid`'s end) with only `suffix`'s FIRST byte constrained: positions are
 * consecutive integers, so whichever lookahead position is the FIRST to
 * reach `fs_byte_length mid` is necessarily `suffix`'s byte 0 exactly
 * (never byte 1 or 2 -- integers cannot skip over the boundary), and once
 * THAT read is known non-continuation, `utf8_decode_at`'s own `if not
 * (is_continuation b1) || not (is_continuation b2) [|| ...] then (0xFFFD,
 * 1) else ...` structure forces the reject branch regardless of what any
 * LATER lookahead byte is (a boolean `||` with one true disjunct is true
 * no matter the others) -- and if a later lookahead position is instead
 * `None` (suffix too short), the pattern's own catch-all arm gives
 * `(0xFFFD, 1)` anyway. So `suffix`'s bytes at offset 1+ are completely
 * unconstrained; only offset 0 (its very first byte) ever matters. This
 * is a strictly weaker, more useful hypothesis than any fixed-headroom
 * bound (`pos + 4 <= fs_byte_length mid`), and it is the practically
 * realistic one: this file's actual consumer (N-Quads line streaming,
 * `RDF.NQuads.Streaming.fst`) always cuts `mid`/`suffix` at a LINE
 * boundary (ASCII `\n`, itself non-continuation, or end of input), so
 * this hypothesis holds automatically at every real call site -- see
 * that file's own carry/split machinery.
 *
 * METHOD. `utf8_decode_at_join` (byte-list level, proved by explicit
 * case analysis mirroring `utf8_decode_at`'s own branch structure,
 * exactly as this file's other template lemmas do) is the core fact;
 * `lemma_cp_at_at_middle` lifts it to `fs_cp_at` via the SAME `fs_cp_at_
 * eq` / `utf8_bytes_concat` / `Spec.utf8_decode_at_shift` composition
 * sub-lemma 1 already used for `fs_byte_index`. `lemma_scan_bnode_body_
 * cp_shift_headroom` then mirrors `scan_bnode_body_cp`'s own recursion
 * branch-for-branch (ASCII fast path via `lemma_byte_at_at_middle`,
 * non-ASCII via `lemma_cp_at_at_middle`), using the SAME fuel-headroom
 * technique as sub-lemma 4 (`ptake_while_acc`'s `fuel = 0` case also
 * SUCCEEDS rather than failing, so the same `fuel + pos >= endpos + 1`
 * side condition is needed here too -- `parse_bnode`'s own fuel formula,
 * `len - after_first + 1`, discharges it "for free" by the SAME pure
 * arithmetic `lemma_pws_shift` already relies on: `fuel + pos == len +
 * 1 >= endpos + 1` follows directly from the `endpos < len` requires,
 * no separate fuel-invariant induction needed).
 *
 * SCOPE / WHAT IS NOT DONE HERE. The genuinely new, previously-missing
 * piece -- the `fs_cp_at` locality fact itself, plus the whole-scan
 * shift lemma for `scan_bnode_body_cp` -- is PROVED below, each on the
 * FIRST attempt (no restatement needed). The outer `parse_bnode` wrapper
 * (matching `_:` literally, reading the start-char, dispatching ASCII-
 * vs-codepoint for the start char, trimming a trailing `.`, then
 * `fs_byte_sub`-extracting the label) is NOT composed here -- it is
 * mechanical repetition of sub-lemma 6/8/9's own template (chain
 * `lemma_byte_at_at_middle`/`lemma_cp_at_at_middle` for each of the ~5
 * intermediate byte/codepoint reads `parse_bnode` performs, then
 * `lemma_scan_bnode_body_cp_shift_headroom` for the body scan, then
 * `fs_byte_sub_concat_left`/`_right` for the final label extraction,
 * exactly sub-lemma 6's pattern) -- not attempted this landing per the
 * guard-depth discipline (a first blind attempt at the FULL composed
 * `requires` risked several restatement cycles on a 5-way-nested `let`
 * precondition with no interactive F* MCP available to localise a
 * failure quickly, and the ordered work list's remaining items 2-8 were
 * judged higher-value with the remaining session budget). A future
 * session composing it needs no new proof idea, only the chaining.
 * ======================================================================== *)

// -- byte-list level helpers, local restatements of the (private, not
// -- `.fsti`-exported) helpers `Parser.FastString.Axioms.fst` uses
// -- internally for its own fact 4/5 proofs -- same self-containment
// -- rationale as sub-lemma 1's own banner.
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val nth_byte_append_left (a b : list Spec.byte) (i : nat)
  : Lemma (requires i < FStar.List.Tot.length a)
          (ensures Spec.nth_byte (FStar.List.Tot.append a b) i == Spec.nth_byte a i)
let rec nth_byte_append_left a b i =
  match a with
  | hd :: tl -> if i = 0 then () else nth_byte_append_left tl b (i - 1)

val nth_byte_none_of_ge (bs : list Spec.byte) (i : nat)
  : Lemma (requires i >= FStar.List.Tot.length bs)
          (ensures Spec.nth_byte bs i == None)
let rec nth_byte_none_of_ge bs i =
  match bs with
  | [] -> ()
  | hd :: tl -> nth_byte_none_of_ge tl (i - 1)

val nth_byte_some_of_lt (bs : list Spec.byte) (i : nat)
  : Lemma (requires i < FStar.List.Tot.length bs)
          (ensures Some? (Spec.nth_byte bs i))
let rec nth_byte_some_of_lt bs i =
  match bs with
  | hd :: tl -> if i = 0 then () else nth_byte_some_of_lt tl (i - 1)
#pop-options

// -- the codepoint-decode join fact, byte-list level: decoding at a
// -- position INSIDE `a` agrees whether or not `a` is followed by `b`,
// -- PROVIDED `b`'s first byte (when present) is not a UTF-8
// -- continuation byte. See this section's banner for the full argument
// -- (why only `b`'s FIRST byte ever matters, regardless of how many
// -- bytes the decode overruns into `b`).
#push-options "--z3rlimit 300 --fuel 4 --ifuel 4"
val utf8_decode_at_join (a b : list Spec.byte) (p : nat)
  : Lemma
      (requires
        p < FStar.List.Tot.length a /\
        (b == [] \/ not (Spec.is_continuation (FStar.List.Tot.hd b))))
      (ensures Spec.utf8_decode_at (FStar.List.Tot.append a b) p == Spec.utf8_decode_at a p)
let utf8_decode_at_join a b p =
  let la = FStar.List.Tot.length a in
  nth_byte_append_left a b p;
  nth_byte_some_of_lt a p;
  match b with
  | [] -> FStar.List.Tot.append_l_nil a
  | hd :: tl ->
    (match Spec.nth_byte a p with
     | None -> ()
     | Some b0 ->
       if b0 < 0x80 then ()
       else if b0 < 0xC2 then ()
       else if b0 < 0xE0 then begin
         if p + 1 < la then nth_byte_append_left a b (p + 1)
         else begin
           nth_byte_none_of_ge a (p + 1);
           Spec.nth_byte_append a b 0
         end
       end
       else if b0 < 0xF0 then begin
         if p + 1 < la then begin
           nth_byte_append_left a b (p + 1);
           if p + 2 < la then nth_byte_append_left a b (p + 2)
           else begin
             nth_byte_none_of_ge a (p + 2);
             Spec.nth_byte_append a b 0
           end
         end else begin
           nth_byte_none_of_ge a (p + 1);
           nth_byte_none_of_ge a (p + 2);
           Spec.nth_byte_append a b 0
         end
       end
       else if b0 < 0xF5 then begin
         if p + 1 < la then begin
           nth_byte_append_left a b (p + 1);
           if p + 2 < la then begin
             nth_byte_append_left a b (p + 2);
             if p + 3 < la then nth_byte_append_left a b (p + 3)
             else begin
               nth_byte_none_of_ge a (p + 3);
               Spec.nth_byte_append a b 0
             end
           end else begin
             nth_byte_none_of_ge a (p + 2);
             nth_byte_none_of_ge a (p + 3);
             Spec.nth_byte_append a b 0
           end
         end else begin
           nth_byte_none_of_ge a (p + 1);
           nth_byte_none_of_ge a (p + 2);
           nth_byte_none_of_ge a (p + 3);
           Spec.nth_byte_append a b 0
         end
       end
       else ())
#pop-options

// -- string level: `fs_cp_at` under a 3-way embedding, prefix-shifted,
// -- given the suffix-boundary-safety hypothesis. Composes `fs_cp_at_eq`
// -- + `utf8_bytes_concat` (twice) + `Spec.utf8_decode_at_shift` (strips
// -- the prefix, exactly sub-lemma 1's technique) + `utf8_decode_at_join`
// -- above (strips the suffix-side divergence risk).
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_cp_at_at_middle (prefix mid suffix : string) (pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        (fs_byte_length suffix = 0 \/
         not (Spec.is_continuation (fs_byte_at suffix 0))))
      (ensures
        fs_cp_at (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) == fs_cp_at mid pos)
let lemma_cp_at_at_middle prefix mid suffix pos =
  fs_cp_at_eq (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos);
  fs_cp_at_eq mid pos;
  Spec.utf8_bytes_concat prefix (mid ^ suffix);
  Spec.utf8_bytes_concat mid suffix;
  fs_byte_length_eq prefix;
  fs_byte_length_eq mid;
  fs_byte_length_eq suffix;
  Spec.utf8_decode_at_shift (Spec.utf8_bytes prefix)
    (FStar.List.Tot.append (Spec.utf8_bytes mid) (Spec.utf8_bytes suffix)) pos;
  (match Spec.utf8_bytes suffix with
   | [] -> FStar.List.Tot.append_l_nil (Spec.utf8_bytes mid)
   | hd :: tl ->
     fs_byte_at_eq suffix 0;
     nth_byte_some_of_lt (Spec.utf8_bytes suffix) 0;
     Spec.nth_byte_zero hd tl;
     utf8_decode_at_join (Spec.utf8_bytes mid) (Spec.utf8_bytes suffix) pos)
#pop-options

// -- fs_byte_at analogue of sub-lemma 1 (`lemma_byte_index_at_middle`),
// -- needed since `scan_bnode_body_cp` reads via `fs_byte_at`, not
// -- `fs_byte_index` -- direct corollary of Axioms fact 4
// -- (`fs_byte_at_concat`), no new induction.
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_byte_at_at_middle (prefix mid suffix : string) (pos : nat)
  : Lemma (requires pos < fs_byte_length mid)
          (ensures fs_byte_at (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) == fs_byte_at mid pos)
let lemma_byte_at_at_middle prefix mid suffix pos =
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  fs_byte_at_concat prefix (mid ^ suffix) (fs_byte_length prefix + pos);
  fs_byte_at_concat mid suffix pos
#pop-options

// -- the whole-scan shift lemma for `scan_bnode_body_cp`, `rec`-mirroring
// -- its own branch structure exactly as `lemma_scan_iri_end_shift`
// -- (sub-lemma 2) does for `scan_iri_end`, with the same fuel-headroom
// -- technique as sub-lemma 4 (`ptake_while_acc`'s `fuel = 0` case also
// -- SUCCEEDS, unlike `scan_iri_end`'s, so `fuel + pos >= endpos + 1` is
// -- needed to rule out a fuel-exhaustion artifact) and, in the
// -- non-ASCII branch, `lemma_cp_at_at_middle` above in place of
// -- sub-lemma 1's plain byte read.
#push-options "--z3rlimit 300 --fuel 4 --ifuel 4"
val lemma_scan_bnode_body_cp_shift_headroom
    (prefix mid suffix : string) (pos fuel extra : nat) (endpos : nat)
  : Lemma
      (requires
        scan_bnode_body_cp mid pos fuel == endpos /\
        endpos < fs_byte_length mid /\
        fuel + pos >= endpos + 1 /\
        (fs_byte_length suffix = 0 \/ not (Spec.is_continuation (fs_byte_at suffix 0))))
      (ensures
        scan_bnode_body_cp (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) (fuel + extra)
          == fs_byte_length prefix + endpos)
      (decreases fuel)
let rec lemma_scan_bnode_body_cp_shift_headroom prefix mid suffix pos fuel extra endpos =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if pos >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_at_at_middle prefix mid suffix pos;
      let b = fs_byte_at mid pos in
      if b < 0x80 then begin
        if is_bnode_char_cp b then
          lemma_scan_bnode_body_cp_shift_headroom prefix mid suffix (pos + 1) (fuel - 1) extra endpos
        else ()
      end else begin
        lemma_cp_at_at_middle prefix mid suffix pos;
        let (cp, adv) = fs_cp_at mid pos in
        let advance : nat = if adv = 0 then 1 else adv in
        if is_bnode_char_cp cp then
          lemma_scan_bnode_body_cp_shift_headroom prefix mid suffix (pos + advance) (fuel - 1) extra endpos
        else ()
      end
    end
  end
#pop-options

(** ========================================================================
 * STAGE 3, ITEM 2 (task #48 ordered work list item 2): literal branch
 * (`parse_literal` -- quoted strings, language tags, `^^` datatype IRIs).
 * Applies the Stage-2 equal-accumulator method (`parse_iri_body_acc`'s
 * technique) to `parse_string_body`, PLUS Item 1's new `fs_cp_at`
 * locality fact for its non-ASCII fast-byte push, PLUS a two-lemma
 * (not one-capstone) split for `parse_string_literal`'s fast-vs-escape
 * dispatch -- following the FINDING banner's own recorded next-step
 * suggestion for exactly this shape of problem, rather than repeating
 * the abandoned single-outer-match attempt.
 *
 * VERIFIED, EACH ON THE FIRST OR SECOND ATTEMPT (no restatement beyond
 * threading one extra explicit-witness parameter, `fk`, through the
 * escape-path lemma -- not a proof-technique failure):
 *   - `lemma_scan_string_fast_shift_headroom` -- `scan_string_fast`'s
 *     SUCCESS shift (position-only, ALWAYS FAILS at fuel=0 like
 *     `scan_iri_end`, so plain headroom with no side condition).
 *   - `lemma_parse_string_body_shift` -- the accumulator shift for the
 *     escape/backslash slow path, SAME method as `lemma_parse_iri_body_
 *     acc_shift`: `acc_mid == acc_full` threaded, zero `FStar.String.
 *     concat` algebra invoked. Single-char escapes (`\t\n\r\\\"\b\f\'`)
 *     push a FIXED char (syntactically identical on both sides, simpler
 *     than `parse_iri_body_acc`'s `fs_byte_sub` case); `\u`/`\U` push
 *     `safe_char_of_int cp` from hex digits read via `lemma_byte_index_
 *     at_middle`-proved-equal bytes (same `cp` on both sides, no new
 *     lemma); the non-ASCII fast-byte branch pushes `safe_char_of_int
 *     cp` from Item 1's `lemma_cp_at_at_middle` -- the FIRST reuse of
 *     that fact outside its own section, confirming it is a genuinely
 *     general primitive, not `scan_bnode_body_cp`-specific.
 *   - `lemma_scan_string_fast_shift_hasescapes` -- the FAILURE-shift
 *     companion, fixed to the SPECIFIC message `"has escapes"` (the one
 *     `parse_string_literal`'s own `match` dispatches on) rather than a
 *     general failure-shift -- the fuel=0/pos>=len/newline failure
 *     branches all carry a DIFFERENT message literal, so they contradict
 *     a fixed target message by simple string-literal mismatch, exactly
 *     as `ParseOk`/`ParseFail` constructor mismatch closed `scan_iri_
 *     end`'s base cases -- no headroom hypothesis needed at all.
 *   - `lemma_parse_string_literal_fastpath_shift` / `_escapepath_shift`
 *     -- the two-lemma split. Each has its OWN narrow `requires` pinning
 *     which `scan_string_fast` outcome fired (mirroring `parse_string_
 *     literal`'s own dispatch); a caller (or a future top-level
 *     `parse_literal` composition) picks whichever applies, exactly as
 *     the FINDING banner suggested for `parse_iri_raw`'s still-open
 *     capstone.
 *   - `lemma_ptake_while_scan_shift_headroom` -- `ptake_while_scan`'s
 *     shift (position-only, generic over `pred`; SUCCEEDS at fuel=0 like
 *     `ptake_while_acc`, so the SAME `fuel + pos >= endpos + 1` headroom
 *     hypothesis is needed -- simpler to state than sub-lemma 4 since
 *     there is no accumulator at all here).
 *   - `lemma_ptake_while1_pos_shift` -- the wrapper discharging the
 *     headroom side condition "for free" from `ptake_while1_pos`'s own
 *     `fuel = len - pos + 1` formula, exactly `lemma_pws_shift`'s
 *     arithmetic (`fuel + pos == fs_byte_length mid + 1 >= endpos + 1`
 *     follows directly from this lemma's own `endpos < fs_byte_length
 *     mid` requires -- no separate fuel-invariant induction, confirming
 *     that WAS the right general pattern, not a `pws`-specific
 *     coincidence).
 *   - `lemma_parse_lang_tag_shift` -- `parse_lang_tag` (`@` byte check +
 *     `is_alpha` check on the next byte + `ptake_while1_pos is_lang_
 *     char`), success case, direct composition of the pieces above.
 *   - `lemma_parse_datatype_shift` -- `parse_datatype` (`^^` byte check
 *     + `parse_iri`), success case, REUSES sub-lemma 7 (`lemma_parse_
 *     iri_shift`) directly rather than re-deriving IRI locality -- the
 *     first cross-section reuse in this file, confirming sub-lemma 7's
 *     scope (any caller needing "IRI parse at a shifted position, same
 *     result") composes cleanly into a sibling combinator's own proof.
 *
 * NOT DONE: the top-level `parse_literal` wrapper tying the three
 * branches (plain / `@lang` / `^^dt`) together. Attempting it exposed a
 * genuine non-local edge case worth recording precisely (not "harder
 * than expected" -- a specific, nameable gap): `parse_literal`'s "ran
 * out of input right after the closing quote" branch (`pos' >=
 * fs_byte_length mid`, unconditionally treated as PLAIN, no `@`/`^^`
 * possible) is NOT LOCAL when `suffix` is non-empty and `mid` happens to
 * end exactly at `pos'` -- the embedded parse would go on to read
 * `suffix`'s own leading bytes at that position and could find a REAL
 * `@lang` or `^^dt` there that `mid` alone could never see, since `mid`
 * simply ran out. This is a different (milder) hazard than Item 1's
 * `fs_cp_at` continuation-byte problem -- it is not about a single
 * primitive read disagreeing, but about `parse_literal`'s OWN branch
 * dispatch depending on "is there more input at all", which embedding
 * can change from false to true. The fix is mechanical (an extra
 * hypothesis scoping to `pos' < fs_byte_length mid`, i.e. requiring the
 * literal is NOT the last thing in `mid`, for the plain-literal branch
 * specifically -- the `@lang`/`^^dt` branches already require reading a
 * real byte at `pos'` and so are unaffected) but was not written this
 * landing: the three-way composition (plain vs lang vs datatype, each
 * needing its own precise `requires`, PLUS choosing fastpath- vs
 * escapepath- shift for the underlying string literal) multiplies to
 * six concrete lemma statements, and the remaining ordered-work-list
 * items (3-8, reaching all the way to `theorem_stream_eq_batch`) were
 * judged higher-value with the session budget remaining. A future
 * session has every piece needed pre-verified above; only the
 * mechanical chaining (plus the one-line `pos' < fs_byte_length mid`
 * scoping fix) remains.
 * ======================================================================== *)

// -- byte-list level: this file's earlier sub-lemma 1 restated the
// -- `fs_byte_index` agreement locally; `scan_string_fast`/`parse_
// -- string_body` below read via `fs_byte_index` too, so `lemma_byte_
// -- index_at_middle` (sub-lemma 1, already in scope from earlier in
// -- this file) is reused directly -- no restatement needed here.

// -- scan_string_fast: position-only fast scan for the closing quote.
// -- ALWAYS FAILS at fuel=0 ("string too long"), exactly `scan_iri_end`'s
// -- shape -- plain headroom, no side condition.
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_scan_string_fast_shift_headroom
    (prefix mid suffix : string) (pos fuel extra : nat) (endpos : nat)
  : Lemma
      (requires
        scan_string_fast mid pos fuel == ParseOk () endpos /\
        endpos <= fs_byte_length mid)
      (ensures
        scan_string_fast (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) (fuel + extra)
          == ParseOk () (fs_byte_length prefix + endpos))
      (decreases fuel)
let rec lemma_scan_string_fast_shift_headroom prefix mid suffix pos fuel extra endpos =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if pos >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix pos;
      let ch = fs_byte_index mid pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x22 then ()
      else if code = 0x5C then ()
      else if code = 0x0A || code = 0x0D then ()
      else
        lemma_scan_string_fast_shift_headroom prefix mid suffix (pos + 1) (fuel - 1) extra endpos
    end
  end
#pop-options

// -- parse_string_body: accumulator escape/backslash slow path. Equal-
// -- accumulator technique (Stage 2), reusing Item 1's fs_cp_at locality
// -- fact (lemma_cp_at_at_middle) for the non-ASCII fast-byte branch.
// -- fuel=0 FAILS ("string too long"), same as parse_iri_body_acc, so
// -- plain fuel-headroom (no side condition) suffices.
#push-options "--z3rlimit 400 --fuel 6 --ifuel 6"
val lemma_parse_string_body_shift
    (prefix mid suffix : string) (pos fuel extra : nat)
    (acc_mid acc_full : list FStar.Char.char) (endpos : nat) (out_s : string)
  : Lemma
      (requires
        acc_mid == acc_full /\
        parse_string_body mid pos acc_mid fuel == ParseOk out_s endpos /\
        endpos <= fs_byte_length mid /\
        (fs_byte_length suffix = 0 \/ not (Spec.is_continuation (fs_byte_at suffix 0))))
      (ensures
        parse_string_body (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) acc_full (fuel + extra)
          == ParseOk out_s (fs_byte_length prefix + endpos))
      (decreases fuel)
let rec lemma_parse_string_body_shift prefix mid suffix pos fuel extra acc_mid acc_full endpos out_s =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if pos >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix pos;
      let ch = fs_byte_index mid pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x22 then ()
      else if code = 0x5C then begin
        if pos + 1 >= len_mid then ()
        else begin
          lemma_byte_index_at_middle prefix mid suffix (pos + 1);
          let esc = fs_byte_index mid (pos + 1) in
          let esc_code = FStar.Char.int_of_char esc in
          if esc_code = 0x74 then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x09 :: acc_mid) (FStar.Char.char_of_int 0x09 :: acc_full) endpos out_s
          else if esc_code = 0x6E then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x0A :: acc_mid) (FStar.Char.char_of_int 0x0A :: acc_full) endpos out_s
          else if esc_code = 0x72 then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x0D :: acc_mid) (FStar.Char.char_of_int 0x0D :: acc_full) endpos out_s
          else if esc_code = 0x5C then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x5C :: acc_mid) (FStar.Char.char_of_int 0x5C :: acc_full) endpos out_s
          else if esc_code = 0x22 then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x22 :: acc_mid) (FStar.Char.char_of_int 0x22 :: acc_full) endpos out_s
          else if esc_code = 0x62 then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x08 :: acc_mid) (FStar.Char.char_of_int 0x08 :: acc_full) endpos out_s
          else if esc_code = 0x66 then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x0C :: acc_mid) (FStar.Char.char_of_int 0x0C :: acc_full) endpos out_s
          else if esc_code = 0x27 then
            lemma_parse_string_body_shift prefix mid suffix (pos + 2) (fuel - 1) extra
              (FStar.Char.char_of_int 0x27 :: acc_mid) (FStar.Char.char_of_int 0x27 :: acc_full) endpos out_s
          else if esc_code = 0x75 then begin
            if pos + 6 > len_mid then ()
            else begin
              lemma_byte_index_at_middle prefix mid suffix (pos + 2);
              lemma_byte_index_at_middle prefix mid suffix (pos + 3);
              lemma_byte_index_at_middle prefix mid suffix (pos + 4);
              lemma_byte_index_at_middle prefix mid suffix (pos + 5);
              match hex_val_opt (fs_byte_index mid (pos + 2)),
                    hex_val_opt (fs_byte_index mid (pos + 3)),
                    hex_val_opt (fs_byte_index mid (pos + 4)),
                    hex_val_opt (fs_byte_index mid (pos + 5)) with
              | Some h0, Some h1, Some h2, Some h3 ->
                let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
                if not (valid_codepoint cp) then ()
                else
                  lemma_parse_string_body_shift prefix mid suffix (pos + 6) (fuel - 1) extra
                    (safe_char_of_int cp :: acc_mid) (safe_char_of_int cp :: acc_full) endpos out_s
              | _ -> ()
            end
          end
          else if esc_code = 0x55 then begin
            if pos + 10 > len_mid then ()
            else begin
              lemma_byte_index_at_middle prefix mid suffix (pos + 2);
              lemma_byte_index_at_middle prefix mid suffix (pos + 3);
              lemma_byte_index_at_middle prefix mid suffix (pos + 4);
              lemma_byte_index_at_middle prefix mid suffix (pos + 5);
              lemma_byte_index_at_middle prefix mid suffix (pos + 6);
              lemma_byte_index_at_middle prefix mid suffix (pos + 7);
              lemma_byte_index_at_middle prefix mid suffix (pos + 8);
              lemma_byte_index_at_middle prefix mid suffix (pos + 9);
              match hex_val_opt (fs_byte_index mid (pos + 2)),
                    hex_val_opt (fs_byte_index mid (pos + 3)),
                    hex_val_opt (fs_byte_index mid (pos + 4)),
                    hex_val_opt (fs_byte_index mid (pos + 5)),
                    hex_val_opt (fs_byte_index mid (pos + 6)),
                    hex_val_opt (fs_byte_index mid (pos + 7)),
                    hex_val_opt (fs_byte_index mid (pos + 8)),
                    hex_val_opt (fs_byte_index mid (pos + 9)) with
              | Some h0, Some h1, Some h2, Some h3, Some h4, Some h5, Some h6, Some h7 ->
                let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) + (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536)
                       + (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) + (h6 `op_Multiply` 16) + h7) in
                if not (valid_codepoint cp) then ()
                else
                  lemma_parse_string_body_shift prefix mid suffix (pos + 10) (fuel - 1) extra
                    (safe_char_of_int cp :: acc_mid) (safe_char_of_int cp :: acc_full) endpos out_s
              | _ -> ()
            end
          end
          else ()
        end
      end
      else if code = 0x0A || code = 0x0D then ()
      else if code < 0x80 then
        lemma_parse_string_body_shift prefix mid suffix (pos + 1) (fuel - 1) extra
          (ch :: acc_mid) (ch :: acc_full) endpos out_s
      else begin
        lemma_cp_at_at_middle prefix mid suffix pos;
        let (cp, adv) = fs_cp_at mid pos in
        let advance : nat = if adv = 0 then 1 else adv in
        lemma_parse_string_body_shift prefix mid suffix (pos + advance) (fuel - 1) extra
          (safe_char_of_int cp :: acc_mid) (safe_char_of_int cp :: acc_full) endpos out_s
      end
    end
  end
#pop-options

// -- scan_string_fast, FAILURE-shift for msg fixed to "has escapes" --
// -- the specific failure parse_string_literal's own match dispatches
// -- on. Both other failure messages contradict the fixed literal by
// -- simple string mismatch -- no headroom hypothesis needed.
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_scan_string_fast_shift_hasescapes
    (prefix mid suffix : string) (pos fuel extra : nat) (endpos : nat)
  : Lemma
      (requires
        scan_string_fast mid pos fuel == ParseFail "has escapes" endpos /\
        endpos < fs_byte_length mid)
      (ensures
        scan_string_fast (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) (fuel + extra)
          == ParseFail "has escapes" (fs_byte_length prefix + endpos))
      (decreases fuel)
let rec lemma_scan_string_fast_shift_hasescapes prefix mid suffix pos fuel extra endpos =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if pos >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix pos;
      let ch = fs_byte_index mid pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x22 then ()
      else if code = 0x5C then ()
      else if code = 0x0A || code = 0x0D then ()
      else
        lemma_scan_string_fast_shift_hasescapes prefix mid suffix (pos + 1) (fuel - 1) extra endpos
    end
  end
#pop-options

// -- parse_string_literal, FAST-PATH success case: direct corollary of
// -- the success-shift lemma plus fs_byte_sub_concat_*, exactly
// -- sub-lemma 6's (lemma_parse_iri_raw_fastpath_shift) pattern.
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_parse_string_literal_fastpath_shift (prefix mid suffix : string) (pos end_pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x22 /\
        scan_string_fast mid (pos + 1) (fs_byte_length mid - pos) == ParseOk () end_pos /\
        end_pos <= fs_byte_length mid)
      (ensures
        (match parse_string_literal mid pos,
               parse_string_literal (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk s_mid endpos_mid, ParseOk s_full endpos_full ->
           s_full == s_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_string_literal_fastpath_shift prefix mid suffix pos end_pos =
  let p = fs_byte_length prefix in
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  lemma_byte_index_at_middle prefix mid suffix pos;
  let fuel_mid = fs_byte_length mid - pos in
  lemma_scan_string_fast_shift_headroom prefix mid suffix (pos + 1) fuel_mid (fs_byte_length suffix) end_pos;
  let start = pos + 1 in
  let str_len = end_pos - 1 - start in
  if str_len > 0 && start + str_len <= fs_byte_length mid then begin
    fs_byte_sub_concat_right prefix (mid ^ suffix) (p + start) str_len;
    fs_byte_sub_concat_left mid suffix start str_len
  end else ()
#pop-options

// -- parse_string_literal, ESCAPE-PATH success case: separate lemma
// -- (not a single outer-match capstone) per the file-end FINDING's own
// -- recorded next-step suggestion -- each path gets its OWN narrow
// -- `requires` pinning which `scan_string_fast` outcome fired; a caller
// -- dispatches itself, matching how `parse_string_literal` itself
// -- dispatches.
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_parse_string_literal_escapepath_shift (prefix mid suffix : string) (pos fk endpos : nat) (out_s : string)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x22 /\
        scan_string_fast mid (pos + 1) (fs_byte_length mid - pos) == ParseFail "has escapes" fk /\
        fk < fs_byte_length mid /\
        parse_string_body mid (pos + 1) [] (fs_byte_length mid - pos) == ParseOk out_s endpos /\
        endpos <= fs_byte_length mid /\
        (fs_byte_length suffix = 0 \/ not (Spec.is_continuation (fs_byte_at suffix 0))))
      (ensures
        (match parse_string_literal mid pos,
               parse_string_literal (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk s_mid endpos_mid, ParseOk s_full endpos_full ->
           s_full == s_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_string_literal_escapepath_shift prefix mid suffix pos fk endpos out_s =
  let p = fs_byte_length prefix in
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  lemma_byte_index_at_middle prefix mid suffix pos;
  let fuel_mid = fs_byte_length mid - pos in
  let start = pos + 1 in
  lemma_scan_string_fast_shift_hasescapes prefix mid suffix start fuel_mid (fs_byte_length suffix) fk;
  lemma_parse_string_body_shift prefix mid suffix start fuel_mid (fs_byte_length suffix) [] [] endpos out_s
#pop-options

// -- parse_lang_tag: @lang-subtag, via ptake_while1_pos / ptake_while_scan.

// ptake_while_scan: position-only scanner, generic over `pred`, SUCCEEDS
// at fuel=0 (returns pos unconditionally) -- same headroom need as
// ptake_while_acc (sub-lemma 4), but position-only so simpler to state
// (no accumulator).
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_ptake_while_scan_shift_headroom
    (pred : FStar.Char.char -> bool) (prefix mid suffix : string)
    (pos fuel extra : nat) (endpos : nat)
  : Lemma
      (requires
        ptake_while_scan pred mid pos fuel == endpos /\
        endpos < fs_byte_length mid /\
        fuel + pos >= endpos + 1)
      (ensures
        ptake_while_scan pred (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) (fuel + extra)
          == fs_byte_length prefix + endpos)
      (decreases fuel)
let rec lemma_ptake_while_scan_shift_headroom pred prefix mid suffix pos fuel extra endpos =
  let p = fs_byte_length prefix in
  if fuel = 0 then ()
  else begin
    let len_mid = fs_byte_length mid in
    if pos >= len_mid then ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix pos;
      let ch = fs_byte_index mid pos in
      if pred ch then
        lemma_ptake_while_scan_shift_headroom pred prefix mid suffix (pos + 1) (fuel - 1) extra endpos
      else ()
    end
  end
#pop-options

// ptake_while1_pos wrapper: discharges the headroom side condition
// automatically from its own `fuel = len - pos + 1` formula, exactly
// lemma_pws_shift's pattern. Then a direct corollary via
// fs_byte_sub_concat_left/_right, exactly sub-lemma 6's pattern.
// Scope: SUCCESS case only.
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_ptake_while1_pos_shift
    (pred : FStar.Char.char -> bool) (prefix mid suffix : string) (pos endpos : nat)
  : Lemma
      (requires
        pos <= fs_byte_length mid /\
        endpos > pos /\
        endpos < fs_byte_length mid /\
        ptake_while_scan pred mid pos (fs_byte_length mid - pos + 1) == endpos)
      (ensures
        (match ptake_while1_pos pred mid pos,
               ptake_while1_pos pred (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk s_mid endpos_mid, ParseOk s_full endpos_full ->
           s_full == s_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_ptake_while1_pos_shift pred prefix mid suffix pos endpos =
  let p = fs_byte_length prefix in
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  let fuel_mid = fs_byte_length mid - pos + 1 in
  lemma_ptake_while_scan_shift_headroom pred prefix mid suffix pos fuel_mid (fs_byte_length suffix) endpos;
  fs_byte_sub_concat_right prefix (mid ^ suffix) (p + pos) (endpos - pos);
  fs_byte_sub_concat_left mid suffix pos (endpos - pos)
#pop-options

// parse_lang_tag itself: '@' byte-check plus is_alpha check on the next
// byte, then ptake_while1_pos is_lang_char. Success case only.
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_parse_lang_tag_shift (prefix mid suffix : string) (pos endpos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x40 /\
        pos + 1 < fs_byte_length mid /\
        is_alpha (fs_byte_index mid (pos + 1)) /\
        endpos > pos + 1 /\
        endpos < fs_byte_length mid /\
        ptake_while_scan is_lang_char mid (pos + 1) (fs_byte_length mid - (pos + 1) + 1) == endpos)
      (ensures
        (match parse_lang_tag mid pos,
               parse_lang_tag (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk s_mid endpos_mid, ParseOk s_full endpos_full ->
           s_full == s_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_lang_tag_shift prefix mid suffix pos endpos =
  lemma_byte_index_at_middle prefix mid suffix pos;
  lemma_byte_index_at_middle prefix mid suffix (pos + 1);
  lemma_ptake_while1_pos_shift is_lang_char prefix mid suffix (pos + 1) endpos
#pop-options

// -- parse_datatype: ^^<iri>, via parse_iri -- reuses sub-lemma 7
// -- (lemma_parse_iri_shift) directly.
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_parse_datatype_shift (prefix mid suffix : string) (pos gt_pos : nat)
  : Lemma
      (requires
        pos + 2 <= fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x5E /\
        FStar.Char.int_of_char (fs_byte_index mid (pos + 1)) = 0x5E /\
        (pos + 2) < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid (pos + 2)) = 0x3C /\
        scan_iri_end mid (pos + 3) (fs_byte_length mid - (pos + 2)) == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid /\
        (match parse_iri_raw mid (pos + 2) with
         | ParseOk iri_mid _ -> is_iri iri_mid
         | ParseFail _ _ -> False))
      (ensures
        (match parse_datatype mid pos,
               parse_datatype (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk s_mid endpos_mid, ParseOk s_full endpos_full ->
           s_full == s_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_datatype_shift prefix mid suffix pos gt_pos =
  lemma_byte_index_at_middle prefix mid suffix pos;
  lemma_byte_index_at_middle prefix mid suffix (pos + 1);
  lemma_parse_iri_shift prefix mid suffix (pos + 2) gt_pos
#pop-options

(** ========================================================================
 * STAGE 3, ITEM 3 (task #48 ordered work list item 3): `parse_graph_
 * label` / `parse_opt_graph_label` (`Parser.NQuads.fst`) -- template
 * repetition over sub-lemma 6/sub-lemma 5 as the banner predicted.
 * Scope: the IRI (`<...>`) branch only -- `parse_graph_label`'s `_:`
 * branch calls `parse_bnode`, whose full wrapper Item 1 left as
 * mechanical remaining work (its scan-level locality fact IS proved;
 * only the outer byte-dispatch composition is not), so the bnode graph-
 * label branch inherits that same gap rather than a new one.
 *
 * VERIFIED, first attempt except `lemma_skip_eol_shift` (below, one
 * restatement -- an omitted empty-`suffix` case, not a proof-technique
 * failure):
 *   - `lemma_parse_graph_label_iri_shift` -- direct corollary of
 *     sub-lemma 6 (`lemma_parse_iri_raw_fastpath_shift`), `<` branch
 *     only, matching `parse_graph_label`'s own manual `is_iri` check.
 *   - `lemma_parse_opt_graph_label_iri_shift` -- `pws` (reusing sub-
 *     lemma 5, `lemma_pws_shift`, directly) then dispatch to the IRI
 *     branch above.
 *   - `lemma_parse_opt_graph_label_none_dot_shift` -- the "no graph
 *     label" success case (next non-ws byte is `.`), `pws` plus one
 *     byte-agreement check, no further recursion.
 * ======================================================================== *)
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_parse_graph_label_iri_shift (prefix mid suffix : string) (pos gt_pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos) = 0x3C /\
        scan_iri_end mid (pos + 1) (fs_byte_length mid - pos) == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid /\
        (match parse_iri_raw mid pos with
         | ParseOk iri_mid _ -> is_iri iri_mid
         | ParseFail _ _ -> False))
      (ensures
        (match parse_graph_label mid pos,
               parse_graph_label (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk g_mid endpos_mid, ParseOk g_full endpos_full ->
           g_full == g_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_graph_label_iri_shift prefix mid suffix pos gt_pos =
  lemma_byte_index_at_middle prefix mid suffix pos;
  lemma_parse_iri_raw_fastpath_shift prefix mid suffix pos gt_pos
#pop-options

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_parse_opt_graph_label_iri_shift
    (prefix mid suffix : string) (pos pos1 gt_pos : nat)
  : Lemma
      (requires
        pos <= fs_byte_length mid /\
        pws mid pos == ParseOk () pos1 /\
        pos1 < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos1) = 0x3C /\
        scan_iri_end mid (pos1 + 1) (fs_byte_length mid - pos1) == ParseOk gt_pos gt_pos /\
        gt_pos < fs_byte_length mid /\
        (match parse_iri_raw mid pos1 with
         | ParseOk iri_mid _ -> is_iri iri_mid
         | ParseFail _ _ -> False))
      (ensures
        (match parse_opt_graph_label mid pos,
               parse_opt_graph_label (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk g_mid endpos_mid, ParseOk g_full endpos_full ->
           g_full == g_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_opt_graph_label_iri_shift prefix mid suffix pos pos1 gt_pos =
  lemma_pws_shift prefix mid suffix pos pos1;
  lemma_byte_index_at_middle prefix mid suffix pos1;
  lemma_parse_graph_label_iri_shift prefix mid suffix pos1 gt_pos
#pop-options

#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_opt_graph_label_none_dot_shift
    (prefix mid suffix : string) (pos pos1 : nat)
  : Lemma
      (requires
        pos <= fs_byte_length mid /\
        pws mid pos == ParseOk () pos1 /\
        pos1 < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos1) = 0x2E)
      (ensures
        (match parse_opt_graph_label mid pos,
               parse_opt_graph_label (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk g_mid endpos_mid, ParseOk g_full endpos_full ->
           g_full == g_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_opt_graph_label_none_dot_shift prefix mid suffix pos pos1 =
  lemma_pws_shift prefix mid suffix pos pos1;
  lemma_byte_index_at_middle prefix mid suffix pos1
#pop-options

(** ========================================================================
 * STAGE 3, ITEM 4 (task #48 ordered work list item 4): comment/blank-
 * line/error-recovery scanners in `parse_nquads_acc` -- PARTIAL, with a
 * sharp, specific FINDING for the part not done (this is NOT "template
 * repetition" as the banner estimated; a genuinely new difficulty class
 * was found).
 *
 * DONE: `lemma_skip_eol_shift` -- `skip_eol` (`Parser.NTriples.fst`) is
 * straight-line (one or two conditional byte reads, no internal
 * recursion), so a direct shift lemma is possible, with one non-local
 * edge exactly like Item 2's `parse_literal` finding: if `mid` ends in
 * a bare CR (`pos + 1 == fs_byte_length mid`) and `suffix` is non-empty
 * with LF as its first byte, embedding would fuse a CRLF pair that does
 * not exist in `mid` alone. Scoped out via the same style of extra
 * hypothesis Item 1/2 used (`pos + 1 < fs_byte_length mid \/ suffix
 * empty \/ suffix's first byte is not LF`).
 *
 * NOT DONE, WITH A NEW OBSTACLE CLASS: `skip_comment` and the inline
 * `skip_line` (the local `let rec skip_line` inside `parse_nquads_acc`'s
 * `ParseFail` branch) both wrap their ACTUAL scanning loop in a LOCAL,
 * unexported `let rec` (`skip_to_eol` inside `skip_comment`; `skip_line`
 * itself is local to `parse_nquads_acc`). This is a DIFFERENT difficulty
 * class from anything Items 1-3 hit (not `fs_cp_at` continuation-byte
 * risk, not an accumulator, not a non-local edge case): a local `let
 * rec` bound inside another function's body has NO qualifiable name
 * outside that function, so an EXTERNAL Locality.fst lemma cannot state
 * "at the intermediate recursive step, the local scanner is at position
 * X with fuel Y" -- there is nothing to write on the left of `==` for
 * that intermediate state. `skip_comment`'s OWN top-level name only
 * unfolds to ONE call into the (already fully-applied) local recursion;
 * calling `skip_comment` again at a shifted position does not correspond
 * to advancing that recursion by one step (it re-checks for a leading
 * `#`, a different operation entirely). Z3's bounded fuel-driven
 * unfolding can verify the property for any FIXED small number of
 * recursion steps but not for an arbitrary (symbolic-length) comment or
 * error line, which is exactly the unbounded case this whole file exists
 * to handle by explicit external induction. CONFIRMED not just
 * "harder than expected" -- checked against F*'s actual name-resolution
 * rules (a `let rec` bound inside a `let ... in` body is not projectable
 * via any qualified name from another module) before writing this
 * FINDING, not inferred from a failed attempt.
 *
 * THE CLEAN FIX (source-level, out of scope for THIS proof-only,
 * additive-only landing): lift `skip_to_eol` (inside `skip_comment`) and
 * `skip_line` (inside `parse_nquads_acc`) to top-level named functions
 * in `Parser.NTriples.fst` / `Parser.NQuads.fst` respectively (identical
 * bodies, just given a `val`+top-level `let rec` instead of a local
 * binding) -- behaviour-preserving, but a change to those files' surface
 * (new exported names, however small) rather than an addition to this
 * proof-only module, and those files have their own broader consumer
 * set this worktree did not budget time to re-verify. A future session
 * with that scope authorised can lift both, then apply EXACTLY this
 * file's own `scan_iri_end`/`ptake_while_scan` template to the lifted
 * functions (they are structurally identical to those two: `skip_to_
 * eol` is `ptake_while_scan` with a negated/different stop predicate;
 * `skip_line` is nearly identical again, needing one extra `skip_eol`
 * call composed in via `lemma_skip_eol_shift` above at its stopping
 * point).
 * ======================================================================== *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_skip_eol_shift (prefix mid suffix : string) (pos : nat)
  : Lemma
      (requires
        pos < fs_byte_length mid /\
        (pos + 1 < fs_byte_length mid \/
         fs_byte_length suffix = 0 \/
         fs_byte_at suffix 0 <> 0x0A))
      (ensures
        skip_eol (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos)
          == fs_byte_length prefix + skip_eol mid pos)
let lemma_skip_eol_shift prefix mid suffix pos =
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  lemma_byte_index_at_middle prefix mid suffix pos;
  let ch = fs_byte_index mid pos in
  let code = FStar.Char.int_of_char ch in
  if code = 0x0D then begin
    if pos + 1 < fs_byte_length mid then
      lemma_byte_index_at_middle prefix mid suffix (pos + 1)
    else if fs_byte_length suffix = 0 then ()
    else begin
      fs_byte_index_eq (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos + 1);
      fs_byte_at_concat prefix (mid ^ suffix) (fs_byte_length prefix + pos + 1);
      fs_byte_at_concat mid suffix (pos + 1);
      fs_byte_index_eq suffix 0
    end
  end else ()
#pop-options

(** ========================================================================
 * ITEM 4 FOLLOW-UP (same task #48 ordered work list item 4): the source-
 * level lift this banner's own "THE CLEAN FIX" paragraph called for has
 * now landed (`nt_skip_to_eol` top-level in Parser.NTriples.fst,
 * `nq_skip_line` top-level in Parser.NQuads.fst -- both lifted verbatim
 * out of their local `let rec` bindings, `input`/`len` made explicit
 * parameters in place of closure capture, five identical local
 * `skip_line` copies in Parser.NQuads.fst's sibling per-line walkers
 * deduplicated to the ONE `nq_skip_line`). The obstacle this banner
 * diagnosed (a local `let rec` has no qualified name an external lemma
 * can state an intermediate-step equation about) is gone for both
 * scanners; the two shift lemmas below are the direct payoff, using
 * EXACTLY sub-lemma 2/3's template (`lemma_scan_iri_end_shift`/
 * `_headroom`): a `rec` lemma mirroring the scanner's own recursion
 * branch-for-branch, `lemma_byte_index_at_middle` for the per-position
 * byte-read agreement, an `extra:nat` fuel-headroom parameter threaded
 * unchanged through the recursion (needed for the same reason sub-lemma
 * 3 needed one: `skip_comment`/the per-line walkers call these scanners
 * with fuel `len - pos`, which differs between `mid` and the embedded
 * `full` by exactly `fs_byte_length suffix`).
 *
 * `lemma_nt_skip_to_eol_shift`: same shape as `lemma_scan_iri_end_shift_
 * headroom` with one CORRECTED difference from the first attempt at this
 * lemma (caught by the verifier, not by inspection -- recorded so a
 * future session does not re-make it). `nt_skip_to_eol` returns the STOP
 * POSITION directly (no `ParseOk`/`ParseFail` wrapper), so unlike `scan_
 * iri_end` (whose `fuel = 0` case ALWAYS fails, making sub-lemma 3's
 * `fuel = 0` case vacuous for free) this scanner returns `p`
 * UNCONDITIONALLY at `fuel = 0` -- a value indistinguishable, by return
 * value alone, from a genuine terminator find. The first attempt assumed
 * `full`'s side hits an "identical unconditional unfolding" at `fuel =
 * 0`, which is FALSE under headroom: `full` runs with `fuel + extra`, so
 * when `mid`'s `fuel` reaches `0` with `extra > 0`, `full`'s own fuel is
 * still `extra > 0` -- it does NOT stop, it keeps scanning, breaking the
 * mirrored-step assumption outright (caught as "Could not prove post-
 * condition" at the WHOLE function body, not a specific branch). FIX:
 * add `p + fuel > fs_byte_length mid` to the `requires` -- exactly the
 * one-unit-of-headroom relationship `skip_comment`'s own call site
 * already has (`nt_skip_to_eol input len (pos+1) (len-pos)` gives `p +
 * fuel = len + 1`), so no real caller is excluded. This makes the `fuel
 * = 0` branch vacuous FOR THE RIGHT REASON: `p + 0 > fs_byte_length mid`
 * forces `p > fs_byte_length mid`, and `mid`'s `fuel = 0` unfolding
 * returns `p` unconditionally, forcing `stop_pos = p`, contradicting the
 * `stop_pos < fs_byte_length mid` hypothesis -- vacuous, not assumed.
 * The extra hypothesis is invariant under the recursive step for free
 * (`(p+1) + (fuel-1) == p + fuel`, plain `nat` arithmetic), so it needs
 * no separate threading beyond being stated once. `p >= len_mid` stays
 * vacuous exactly as before (`stop_pos = p >= len_mid` contradicts `<`).
 *
 * `lemma_nq_skip_line_shift`: one layer past `nt_skip_to_eol`'s shape --
 * `nq_skip_line`'s OWN terminating case calls `skip_eol input p` rather
 * than returning `p` directly (matching the two-scanner composition
 * `skip_comment`'s caller already does by hand: scan to the terminator,
 * then skip over it). Composes DIRECTLY with the file's own already-DONE
 * `lemma_skip_eol_shift` at the SAME position `p` the induction's base
 * case lands on -- no new scanning argument, just one more lemma call at
 * the leaf. Inherits `lemma_skip_eol_shift`'s own non-local CRLF-fusion
 * edge case (a bare CR ending `mid` exactly, with `suffix` starting with
 * LF, would fuse a CRLF pair that does not exist in `mid` alone); scoped
 * out here with the SAME style of extra hypothesis Items 1/2/4's `skip_
 * eol` sub-lemma used, but position-INDEPENDENT (`fs_byte_length suffix
 * = 0 \/ fs_byte_at suffix 0 <> 0x0A`, without the `pos + 1 < fs_byte_
 * length mid` disjunct) since the induction discovers WHERE the
 * terminator is found rather than being told in advance -- a hypothesis
 * that must hold for every possible landing position, not one specific
 * one, so only the two suffix-only disjuncts are available. The
 * `stop_pos < fs_byte_length mid` scoping additionally (as a byproduct,
 * not a separate choice) excludes the terminator sitting at `mid`'s
 * very last byte position mapping to `skip_eol` returning exactly `fs_
 * byte_length mid` -- a known sound-but-narrow realisation, same
 * category as the file's other scoped edge cases, not attempted further
 * here (guard-depth rule). Carries the SAME `p + f > fs_byte_length mid`
 * sufficient-fuel fix `lemma_nt_skip_to_eol_shift` needed, for the
 * identical reason: `nq_skip_line`'s `f = 0` case also returns `p`
 * unconditionally, not a wrapped failure, so it is not automatically
 * vacuous under fuel headroom without it.
 * ======================================================================== *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_nt_skip_to_eol_shift (prefix mid suffix : string) (p fuel extra : nat) (stop_pos : nat)
  : Lemma
      (requires
        p + fuel > fs_byte_length mid /\
        nt_skip_to_eol mid (fs_byte_length mid) p fuel == stop_pos /\
        stop_pos < fs_byte_length mid)
      (ensures
        nt_skip_to_eol (prefix ^ (mid ^ suffix)) (fs_byte_length (prefix ^ (mid ^ suffix)))
          (fs_byte_length prefix + p) (fuel + extra)
          == fs_byte_length prefix + stop_pos)
      (decreases fuel)
let rec lemma_nt_skip_to_eol_shift prefix mid suffix p fuel extra stop_pos =
  if fuel = 0 then
    // p + 0 > fs_byte_length mid (from requires), so p > fs_byte_length
    // mid. nt_skip_to_eol mid len_mid p 0 == p (definitional unfold on
    // the concrete literal fuel=0), forcing stop_pos == p via the
    // requires equation -- but stop_pos < fs_byte_length mid < p is a
    // contradiction. Vacuous (NOT the "full's side unfolds identically"
    // argument the first attempt at this lemma wrongly used -- that
    // broke under headroom; see this lemma's own banner above).
    ()
  else begin
    let len_mid = fs_byte_length mid in
    if p >= len_mid then
      // nt_skip_to_eol mid len_mid p fuel == p (the p>=len_mid base
      // case), forcing stop_pos == p -- contradicts stop_pos < len_mid
      // from the requires. Vacuous.
      ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix p;
      let c = fs_byte_index mid p in
      let cc = FStar.Char.int_of_char c in
      if cc = 0x0A || cc = 0x0D then
        // Base case: nt_skip_to_eol mid len_mid p fuel == p, forcing
        // stop_pos == p. Same byte agreement on full's side takes the
        // SAME branch, so nt_skip_to_eol full len_full (plen+p)
        // (fuel+extra) == plen+p -- matches the goal.
        ()
      else
        // Recursive case: both sides advance (p+1, fuel-1); nat
        // arithmetic gives plen + (p+1) == (plen+p) + 1. `extra` is
        // threaded unchanged, same as sub-lemma 3.
        lemma_nt_skip_to_eol_shift prefix mid suffix (p + 1) (fuel - 1) extra stop_pos
    end
  end
#pop-options

#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_nq_skip_line_shift (prefix mid suffix : string) (p f extra : nat) (stop_pos : nat)
  : Lemma
      (requires
        p + f > fs_byte_length mid /\
        nq_skip_line mid (fs_byte_length mid) p f == stop_pos /\
        stop_pos < fs_byte_length mid /\
        (fs_byte_length suffix = 0 \/ fs_byte_at suffix 0 <> 0x0A))
      (ensures
        nq_skip_line (prefix ^ (mid ^ suffix)) (fs_byte_length (prefix ^ (mid ^ suffix)))
          (fs_byte_length prefix + p) (f + extra)
          == fs_byte_length prefix + stop_pos)
      (decreases f)
let rec lemma_nq_skip_line_shift prefix mid suffix p f extra stop_pos =
  if f = 0 then
    // Same fix as lemma_nt_skip_to_eol_shift's fuel=0 case: p + 0 >
    // fs_byte_length mid forces p > fs_byte_length mid, contradicting
    // stop_pos = p < fs_byte_length mid. Vacuous.
    ()
  else begin
    let len_mid = fs_byte_length mid in
    if p >= len_mid then
      // nq_skip_line mid len_mid p f == p, forcing stop_pos == p --
      // contradicts stop_pos < len_mid. Vacuous.
      ()
    else begin
      fs_byte_length_concat mid suffix;
      fs_byte_length_concat prefix (mid ^ suffix);
      lemma_byte_index_at_middle prefix mid suffix p;
      let c = fs_byte_index mid p in
      let cc = FStar.Char.int_of_char c in
      if cc = 0x0A || cc = 0x0D then
        // Base case: nq_skip_line mid len_mid p f == skip_eol mid p
        // (mid's own definitional unfolding), forcing stop_pos ==
        // skip_eol mid p via the requires equation. Compose with the
        // already-DONE lemma_skip_eol_shift at this SAME position p --
        // its own requires needs p < fs_byte_length mid (have it, this
        // branch) and the suffix-only disjunct (have it, this lemma's
        // own requires) regardless of p, so it applies unconditionally
        // here.
        lemma_skip_eol_shift prefix mid suffix p
      else
        // Recursive case, identical shape to lemma_nt_skip_to_eol_
        // shift's.
        lemma_nq_skip_line_shift prefix mid suffix (p + 1) (f - 1) extra stop_pos
    end
  end
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
 *
 * STATUS UPDATE (SAME landing, later in the same session -- this
 * banner's predictions above are now PARTLY OVERTAKEN and kept only for
 * the reasoning trail; do not read the SUMMARY line above as current):
 *
 *   - `pws`: DONE (`lemma_pws_shift`). Routes through the ACCUMULATOR
 *     combinator `ptake_while_acc`, not the position-only
 *     `ptake_while_scan`/`_pos` this banner's SAME-SHAPE claim assumed
 *     -- still closed, using the Stage-2 "equal accumulators" technique
 *     one stage early (see `lemma_ptake_while_acc_pos_shift_headroom`'s
 *     own banner for why that needed a different fuel precondition than
 *     `scan_iri_end`'s).
 *   - `parse_iri_raw` fast path: DONE (`lemma_parse_iri_raw_fastpath_
 *     shift`), as predicted.
 *   - `parse_iri` (success case): DONE (`lemma_parse_iri_shift`), as
 *     predicted.
 *   - `parse_subject`/`parse_object`, `<` (IRI) branch only: DONE
 *     (`lemma_parse_subject_iri_shift` / `lemma_parse_object_iri_shift`).
 *     The `_` (blank-node) branch is NOT done -- it needs a CODEPOINT-
 *     level (not byte-level) locality fact for `fs_cp_at` under
 *     embedding, which does not exist in `Parser.FastString.Axioms.fst`
 *     today; this is a genuinely different argument from everything in
 *     this file, not predicted by this banner.
 *   - `parse_iri_body_acc`: DONE (`lemma_parse_iri_body_acc_shift`) --
 *     the "new difficulty"/"FStar.String.concat wall" THIS BANNER
 *     PREDICTED did NOT materialise for a LOCALITY lemma specifically:
 *     no concat algebra was needed at all, only "both runs build an
 *     EQUAL accumulator", which the shared/congruent-accumulator
 *     technique gives directly (see that lemma's own banner for the
 *     full argument). The `FStar.String.concat` wall this banner and
 *     `RDF.NTriples.RoundTrip.fst`/`Parser.FastString.Axioms.fst`
 *     reference is real for a VALUE-level round-trip theorem
 *     (recovering `s` from `concat (decode (encode s))`-style
 *     identities) -- it was never actually a locality-lemma obstacle,
 *     and this landing is the evidence.
 *   - `parse_iri_raw` FULL (fast path + escape path unified into one
 *     lemma): ATTEMPTED, NOT closed after three restructured attempts
 *     -- see the FINDING banner immediately above this one for the
 *     three statements tried and the concrete next-step suggestion.
 *     Downstream callers needing only the fast path already have it.
 *   - `parse_literal` (object literal branch: language tags, `^^`
 *     datatype IRIs, quoted-string escape decoding): NOT attempted.
 *     Shares `parse_iri_body_acc`'s accumulator shape, so the SAME
 *     "equal accumulators, no concat algebra" technique this landing
 *     validated should apply -- the most promising unstarted next step
 *     for `parse_object`'s remaining branch.
 *   - Stage 3 (`parse_nquad`/`parse_triple` line-level shift,
 *     `parse_nquads_acc_concat_line`, `theorem_stream_eq_batch`): NOT
 *     attempted this landing. `RDF.NQuads.Streaming.fst`'s task brief
 *     gates Stage 3 on Stages 1-2 covering "the parse path of a WHOLE
 *     LINE" -- they do not yet (blank-node and literal branches are
 *     still open, per the two items above), so per the brief's own
 *     condition Stage 3 was correctly not started. `parse_nquad`
 *     (Parser.NQuads.fst:103) also needs `parse_opt_graph_label`/
 *     `parse_graph_label` (its own `<`/`_:` dispatch, not yet covered)
 *     and `parse_nquads_acc`'s comment/blank-line/error-recovery
 *     scanners (`skip_comment`/`skip_eol`/the inline `skip_line`) before
 *     a full-line shift lemma is even statable.
 * ======================================================================== *)

(** ========================================================================
 * STAGE 3, ITEM 5 (task #48 ordered work list item 5): whole-line shift
 * lemma for `parse_nquad`, composing the branch lemmas above.
 *
 * SCOPE. All-IRI (subject/predicate/object), NO graph label, SUCCESS
 * case -- the slice of `parse_nquad` that Items 1-4's currently-covered
 * branches actually support end to end. `lemma_pws_noop` is one small
 * new fact this composition needed (`pws` is a no-op at a position whose
 * byte already fails `is_nt_ws` -- a single-step unfold, not an
 * induction) to bridge `parse_opt_graph_label`'s own trailing `pws`
 * result into `parse_nquad`'s SECOND `pws` call immediately after it
 * (which re-skips whitespace that is already gone, so must itself be a
 * no-op on both `mid` and the embedding).
 *
 * VERIFIED ON THE FIRST ATTEMPT: `lemma_parse_nquad_iri_nograph_shift`
 * -- nine intermediate byte positions and three `scan_iri_end` witnesses
 * (subject/predicate/object), all explicit parameters, composing
 * `lemma_pws_shift` (sub-lemma 5) + `lemma_parse_subject_iri_shift`
 * (sub-lemma 8) + `lemma_parse_iri_shift` (sub-lemma 7) +
 * `lemma_parse_object_iri_shift` (sub-lemma 9) +
 * `lemma_parse_opt_graph_label_none_dot_shift` (Item 3) +
 * `lemma_pws_noop` -- IN SEQUENCE, no new induction. This is a genuine
 * "whole N-Quads line" locality theorem for the scoped shape, not a
 * further sub-piece: `parse_nquad mid pos` and `parse_nquad (prefix ^
 * (mid ^ suffix)) (fs_byte_length prefix + pos)` produce the identical
 * triple and graph option, at the correctly shifted end position.
 *
 * WHAT THIS DOES NOT YET GIVE (Item 6, `parse_nquads_acc_concat_line`,
 * `RDF.NQuads.Streaming.fst`'s own stated target). That theorem is
 * about `parse_nquads_acc` -- the MULTI-LINE loop, which also has to
 * handle comment lines, blank lines, parse failures (the `skip_line`
 * error-recovery path), and non-IRI subject/object/graph shapes (bnode,
 * literal) for EVERY line in `complete`, not just one line of one
 * specific shape. Item 4's FINDING already identifies `skip_comment`/
 * `skip_line`'s local-`let rec` obstacle as blocking the comment-line
 * and error-recovery cases outright (a source-level fix, not a proof
 * technique); Items 1-2's remaining wrapper gaps (`parse_bnode`,
 * `parse_literal`) block the non-IRI subject/object cases. So Item 6 is
 * gated on genuinely more work than this session's remaining budget,
 * exactly as `RDF.NQuads.Streaming.fst`'s own FINDING independently
 * concluded from a different entry point ("per-combinator locality
 * induction over Parser.NTriples.fst's recursive-descent call graph...
 * confirmed twice now, by two different sessions"). This landing adds a
 * THIRD independent confirmation, now with five concrete named
 * remaining pieces (bnode wrapper, literal wrapper, skip_comment lift,
 * skip_line lift, non-IRI graph-label branch) rather than one vague
 * "per-combinator induction" -- each individually tractable by the
 * templates this file has now validated seven times over (Items 1-5),
 * but the FULL composition remains a separate landing's work, not a
 * same-session extension. Items 6 (`parse_nquads_acc_concat_line`), 7
 * (`theorem_stream_eq_batch` single-chunk), and 8 (`theorem_stream_eq_
 * batch` general induction) are NOT attempted this landing -- correctly
 * not started, per the same gating logic the banner above already
 * established, now updated to reflect Item 5's real (if scoped)
 * completion rather than treating "whole line" as entirely unstarted.
 * ======================================================================== *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val lemma_pws_noop (mid : string) (pos : nat)
  : Lemma (requires pos < fs_byte_length mid /\ not (is_nt_ws (fs_byte_index mid pos)))
          (ensures pws mid pos == ParseOk () pos)
let lemma_pws_noop mid pos = ()
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_nquad_iri_nograph_shift
    (prefix mid suffix : string) (pos : nat)
    (pos1 gt_subj pos2 pos3 gt_pred pos4 pos5 gt_obj pos6 pos7 : nat)
  : Lemma
      (requires
        pos <= fs_byte_length mid /\
        pws mid pos == ParseOk () pos1 /\
        (* subject: IRI branch *)
        pos1 < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos1) = 0x3C /\
        scan_iri_end mid (pos1 + 1) (fs_byte_length mid - pos1) == ParseOk gt_subj gt_subj /\
        gt_subj < fs_byte_length mid /\
        (match parse_iri_raw mid pos1 with ParseOk iri_mid _ -> is_iri iri_mid | ParseFail _ _ -> False) /\
        (match parse_subject mid pos1 with ParseOk _ p -> pos2 = p | ParseFail _ _ -> False) /\
        pos2 <= fs_byte_length mid /\
        pws mid pos2 == ParseOk () pos3 /\
        (* predicate: IRI *)
        pos3 < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos3) = 0x3C /\
        scan_iri_end mid (pos3 + 1) (fs_byte_length mid - pos3) == ParseOk gt_pred gt_pred /\
        gt_pred < fs_byte_length mid /\
        (match parse_iri_raw mid pos3 with ParseOk iri_mid _ -> is_iri iri_mid | ParseFail _ _ -> False) /\
        (match parse_iri mid pos3 with ParseOk _ p -> pos4 = p | ParseFail _ _ -> False) /\
        pos4 <= fs_byte_length mid /\
        pws mid pos4 == ParseOk () pos5 /\
        (* object: IRI *)
        pos5 < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos5) = 0x3C /\
        scan_iri_end mid (pos5 + 1) (fs_byte_length mid - pos5) == ParseOk gt_obj gt_obj /\
        gt_obj < fs_byte_length mid /\
        (match parse_iri_raw mid pos5 with ParseOk iri_mid _ -> is_iri iri_mid | ParseFail _ _ -> False) /\
        (match parse_object mid pos5 with ParseOk _ p -> pos6 = p | ParseFail _ _ -> False) /\
        (* opt graph label: none, dot found directly after ws *)
        pos6 <= fs_byte_length mid /\
        pws mid pos6 == ParseOk () pos7 /\
        pos7 < fs_byte_length mid /\
        FStar.Char.int_of_char (fs_byte_index mid pos7) = 0x2E /\
        (match parse_iri mid pos3 with ParseOk pred _ -> is_iri pred | ParseFail _ _ -> False))
      (ensures
        (match parse_nquad mid pos,
               parse_nquad (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk (t_mid, g_mid) endpos_mid, ParseOk (t_full, g_full) endpos_full ->
           t_full == t_mid /\ g_full == g_mid /\
           endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_nquad_iri_nograph_shift
    prefix mid suffix pos pos1 gt_subj pos2 pos3 gt_pred pos4 pos5 gt_obj pos6 pos7 =
  lemma_pws_shift prefix mid suffix pos pos1;
  lemma_byte_index_at_middle prefix mid suffix pos1;
  lemma_parse_subject_iri_shift prefix mid suffix pos1 gt_subj;
  lemma_pws_shift prefix mid suffix pos2 pos3;
  lemma_byte_index_at_middle prefix mid suffix pos3;
  lemma_parse_iri_shift prefix mid suffix pos3 gt_pred;
  lemma_pws_shift prefix mid suffix pos4 pos5;
  lemma_byte_index_at_middle prefix mid suffix pos5;
  lemma_parse_object_iri_shift prefix mid suffix pos5 gt_obj;
  lemma_parse_opt_graph_label_none_dot_shift prefix mid suffix pos6 pos7;
  lemma_pws_noop mid pos7;
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  lemma_pws_shift prefix mid suffix pos7 pos7;
  lemma_byte_index_at_middle prefix mid suffix pos7
#pop-options

(** ========================================================================
 * STAGE 3, ITEM 1 CLOSED (task #48 ordered work list item 1, deferred at
 * this file's line-2148-ish "STATUS UPDATE" banner as "mechanical
 * repetition of sub-lemma 6/8/9's own template", confirmed here):
 * `lemma_parse_bnode_shift` -- the `parse_bnode` wrapper (the `_:` prefix
 * check, the start-char ASCII-vs-codepoint dispatch, the body scan via
 * Item 1's own `lemma_scan_bnode_body_cp_shift_headroom`, the trailing
 * `.` trim, and the final `fs_byte_sub` label extraction), chained
 * exactly as the banner predicted -- no new proof idea, only composing
 * already-verified pieces.
 *
 * STYLE NOTE (why this is one flat lemma, not several, unlike the
 * fast-path/escape-path SPLIT this file used for `parse_string_literal`
 * and the DEFERRED capstone for `parse_iri_raw`): `parse_bnode`'s body is
 * STRAIGHT-LINE code (`if`/`let`/`match` in sequence) with exactly ONE
 * embedded recursive call (`scan_bnode_body_cp`, already fully closed by
 * `lemma_scan_bnode_body_cp_shift_headroom`) -- there is no OUTER match
 * over TWO SEPARATE recursive functions' results the way the abandoned
 * `parse_iri_raw` capstone needed (that capstone failed composing a
 * fast-path lemma and an escape-path lemma BEHIND one dispatch; here
 * there is only one scan to dispatch on, already covered end to end).
 * All witnesses (`start_cp`/`start_adv`/`after_first`/`end_pos`/
 * `final_end`) are EXPLICIT PARAMETERS, not derived inside the proof via
 * pattern-matching an abstract `ParseOk`/`ParseFail` -- exactly
 * `lemma_parse_nquad_iri_nograph_shift`'s own style immediately above,
 * which verified first attempt for the same reason (explicit witnesses
 * sidestep the "unconstrained second field of an abstractly-matched
 * constructor" trap the `lemma_scan_iri_end_result_eq` FINDING records).
 *
 * SCOPE. Success case only; the trailing-`.`-trim branch is included
 * (both the "trim" and "no trim" sub-cases, via the `final_end`
 * parameter's own disjunctive `requires`), matching `parse_bnode`'s own
 * full success surface, not a narrowed slice of it.
 * ------------------------------------------------------------------------ *)
#push-options "--z3rlimit 400 --fuel 6 --ifuel 6"
val lemma_parse_bnode_shift
    (prefix mid suffix : string) (pos : nat)
    (start_cp start_adv after_first end_pos final_end : nat)
  : Lemma
      (requires
        pos + 2 <= fs_byte_length mid /\
        fs_byte_at mid pos = 0x5F /\
        fs_byte_at mid (pos + 1) = 0x3A /\
        pos + 2 < fs_byte_length mid /\
        (fs_byte_length suffix = 0 \/ not (Spec.is_continuation (fs_byte_at suffix 0))) /\
        (let start_pos = pos + 2 in
         let b0 = fs_byte_at mid start_pos in
         ((b0 < 0x80 /\ start_cp == b0 /\ start_adv == 1) \/
          (b0 >= 0x80 /\ fs_cp_at mid start_pos == (start_cp, start_adv)))) /\
        is_bnode_start_cp start_cp /\
        after_first == pos + 2 + start_adv /\
        fs_byte_length mid > after_first /\
        scan_bnode_body_cp mid after_first (fs_byte_length mid - after_first + 1) == end_pos /\
        end_pos < fs_byte_length mid /\
        (let start_pos = pos + 2 in
         ((end_pos > start_pos /\ fs_byte_at mid (end_pos - 1) = 0x2E /\ final_end == end_pos - 1) \/
          ((end_pos <= start_pos \/ fs_byte_at mid (end_pos - 1) <> 0x2E) /\ final_end == end_pos))) /\
        final_end > pos + 2 /\ final_end <= fs_byte_length mid)
      (ensures
        (match parse_bnode mid pos,
               parse_bnode (prefix ^ (mid ^ suffix)) (fs_byte_length prefix + pos) with
         | ParseOk b_mid endpos_mid, ParseOk b_full endpos_full ->
           b_full == b_mid /\ endpos_full == fs_byte_length prefix + endpos_mid
         | _, _ -> False))
let lemma_parse_bnode_shift prefix mid suffix pos start_cp start_adv after_first end_pos final_end =
  let p = fs_byte_length prefix in
  let start_pos = pos + 2 in
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  lemma_byte_at_at_middle prefix mid suffix pos;
  lemma_byte_at_at_middle prefix mid suffix (pos + 1);
  lemma_byte_at_at_middle prefix mid suffix start_pos;
  let b0 = fs_byte_at mid start_pos in
  if b0 >= 0x80 then lemma_cp_at_at_middle prefix mid suffix start_pos else ();
  let fuel_mid = fs_byte_length mid - after_first + 1 in
  lemma_scan_bnode_body_cp_shift_headroom prefix mid suffix after_first fuel_mid (fs_byte_length suffix) end_pos;
  lemma_byte_at_at_middle prefix mid suffix (end_pos - 1);
  if final_end > start_pos && final_end <= fs_byte_length mid then begin
    fs_byte_sub_concat_right prefix (mid ^ suffix) (p + start_pos) (final_end - start_pos);
    fs_byte_sub_concat_left mid suffix start_pos (final_end - start_pos)
  end else ()
#pop-options

