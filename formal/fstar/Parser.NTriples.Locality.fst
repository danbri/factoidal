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
