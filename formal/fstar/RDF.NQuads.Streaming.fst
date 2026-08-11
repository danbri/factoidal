module RDF.NQuads.Streaming

(* ============================================================================
 * RDF.NQuads.Streaming -- streaming N-Quads ingestion, task #48.
 *
 * THE QUESTION THIS ANSWERS. The owner's "can we prove we can stream a
 * terabyte N-Quads file into a consumer" question, made precise: a consumer
 * folds over arbitrary byte-chunk boundaries (as bytes arrive off a socket
 * or a file reader, with NO guarantee a chunk boundary lands on a line
 * boundary) and the claim is that this produces the same `rdf_dataset` as
 * parsing the whole input at once. Line-based format first (N-Quads), per
 * the migration plan's constraint 3 (docs/designissues/
 * 2026-08-09-sparql-e2e-proofs-plan.md, "Fast-path re-founding constraints").
 *
 * STRATEGY CHOSEN: A common line-splitter first (task brief's Strategy B),
 * BUT built on `FStar.String.list_of_string` / `string_of_list` at the
 * CODEPOINT level, NOT on `Parser.FastString`'s byte-indexed `fs_byte_sub`.
 * Reason, found while designing this module (not assumed going in): the
 * only way to prove "slice s at k, slice s from k, concatenate the two
 * slices back, get s again" through `fs_byte_sub` requires
 * `Parser.FastString.fsti`'s `fs_byte_sub_eq` bridging lemma, which routes
 * through `Parser.FastString.Spec.utf8_decode_all (Parser.FastString.Spec.
 * utf8_bytes s)` -- and recovering `s` from THAT composition is exactly the
 * "SINGLE-DECODER ROUND TRIP" theorem `Parser.FastString.Spec.fst`'s own
 * banner (bottom of file) documents as ATTEMPTED and PARKED after three
 * tries (issue #374): `utf8_decode_all (utf8_bytes s) == FStar.String.
 * list_of_string s` stalls on an Error 19 unfold obstruction that "three
 * tries is this task's own stop rule" left unresolved. Re-attempting that
 * exact parked theorem was not going to succeed inside THIS task's own
 * guard-depth-3 budget either, so this module avoids the wall entirely by
 * never calling `fs_byte_sub` for the split.
 *
 * `FStar.String.list_of_string` / `string_of_list` carry their OWN,
 * already-proved, unconditional round-trip lemmas in ulib itself
 * (`string_of_list_of_string`, `list_of_string_of_list` --
 * FStar.String.fsti lines 44-47) plus `list_of_concat` (length/list
 * homomorphism for `^`, FStar.String.fsti line 120) -- no parked gap
 * anywhere in that toolchain. `split_complete_lines` below is built
 * entirely on those, plus a hand-rolled single-pass walk over `list
 * FStar.Char.char` (mirroring `Parser.FastString.Spec.fst`'s own
 * `take_bytes`/`drop_bytes` style precedent: hand-written structural
 * recursion, not `FStar.List.Tot.Base.splitAt`, per
 * `skills/fstar-module-style/SKILL.md`'s fixed-fuel/extraction-semantics
 * caveat on that combinator).
 *
 * FUEL NOTE (task brief's explicit ask). `feed_chunk` and `finish` each
 * call `Parser.NQuads.parse_nquads_acc` on a FRESH, SELF-CONTAINED string
 * (the "complete lines" prefix, or the final carry) with fuel `fs_byte_length
 * <that string> + 1` -- exactly the same fuel discipline
 * `Parser.NQuads.parse_nquads`/`parse_nquads_strict` already use for a
 * whole document (Parser.NQuads.fst lines 269-273, 521-525). Fuel is
 * NEVER threaded across chunk boundaries and never guessed: each call gets
 * its own freshly-computed, provably-sufficient budget (the same argument
 * that makes fuel = len+1 sufficient for `parse_nquads` applies verbatim
 * to any substring, since `parse_nquads_acc`'s recursion always strictly
 * advances `pos` by at least 1 or returns, so the number of iterations is
 * bounded by the string's own length regardless of what string it is).
 * This is the "restructure around inputs where fuel suffices" branch of
 * the task brief's fuel-note choice, made trivial by never processing a
 * SLICE at a nonzero starting position with a fuel budget sized for a
 * DIFFERENT (larger) string -- every `parse_nquads_acc` call here starts
 * at position 0 of its own argument string with that argument's own
 * length-derived fuel.
 *
 * STATUS (2026-08-11 landing). Checkpoint 1 (`split_complete_lines` + its
 * FULL defining-lemma kit) is VERIFIED below: reconstruction (`complete ^
 * carry == s`, `split_complete_lines_reconstruct`), the "carry never holds
 * a complete line" invariant (`split_complete_lines_carry_no_nl`), and
 * BOTH carry-composition facts the task brief names by name --
 * `split_complete_lines_extend_carry` ("a chunk with no newline extends
 * carry") and `split_complete_lines_ends_in_newline` ("a chunk ending in
 * newline empties carry"). `stream_state` / `feed_chunk` / `finish` /
 * `stream_parse` are DEFINED (they typecheck and compose
 * `split_complete_lines` with the EXISTING, unmodified `Parser.NQuads.
 * parse_nquads_acc`), so the streaming API shape from the task brief
 * exists and is exercised, and `stream_parse [c]` reduces definitionally
 * to a concrete two-call pipeline (`stream_parse_single_chunk_shape`, a
 * rewrite lemma -- not yet an equivalence with the batch parser).
 *
 * FINDING, LANDED (not a gap -- fixed in this session, kept here because
 * the next agent extending this file will hit the same wall otherwise):
 * `FStar.String.string_of_list` does NOT get ordinary SMT congruence.
 * Given `h : p == []` in scope, `assert (string_of_list p == "")` fails
 * (Error 19) even with `assert_norm (string_of_list [] == "")` ALSO
 * established -- confirmed via a standalone probe (three earlier attempts
 * at `split_complete_lines_no_newline`/`_ends_in_newline` stalled on
 * exactly this before the cause was isolated). `list_of_string`/
 * `string_of_list` carry F*'s "special normalizer status"
 * (`FStar.String.fsti`'s own banner) rather than plain uninterpreted-
 * function status, so Z3's E-graph congruence closure -- which would make
 * this automatic for an ordinary function symbol -- does not fire. The
 * fix, `cong_string_of_list` below: a one-line helper `Lemma (requires a
 * == b) (ensures string_of_list a == string_of_list b) = ()`, proved by
 * F*'s TYPE-CHECKER-level substitution (not Z3 congruence) and then
 * usable as an ordinary lemma call at every site that needs to carry a
 * list-level equality through `string_of_list`.
 *
 * The full `theorem_stream_eq_batch` (streaming == batch parse) is NOT
 * proved in this landing -- see the FINDING at the bottom of this file for
 * exactly why and what it needs. Narrowest verified checkpoint: the lemma
 * kit around `split_complete_lines`. Next narrowest UNPROVED statement:
 * `parse_nquads_acc_concat_line` (stated in the FINDING, not as a `val`
 * with no body -- this file adds no `assume val` and no admitted lemma).
 * ============================================================================ *)

open FStar.List.Tot

(* ------------------------------------------------------------------------
 * Newline test -- N-Quads statements are terminated by '\n' (0x0A); a
 * trailing '\r' before it (CRLF) is not itself a line terminator in this
 * module's model, matching `Parser.NQuads.fst`'s own `skip_eol` treating
 * '\r' as part of "empty line" handling but locating lines by '\n'. Only
 * '\n' is treated as the line-completing character here, deliberately
 * narrow: a chunk boundary landing between '\r' and '\n' of a CRLF pair
 * is handled correctly by this choice (the '\r' just rides along in
 * `carry` until the '\n' arrives), whereas splitting on '\r' too would
 * risk cutting a CRLF pair in half across chunks. See also `Parser.NQuads
 * .parse_nquads_acc`'s own comment-line/empty-line branch, which checks
 * `code = 0x0A || code = 0x0D` only to decide "is this an empty line",
 * never to locate a line boundary for resumption -- consistent with using
 * only 0x0A here.
 * ------------------------------------------------------------------------ *)
let is_nl (c : FStar.Char.char) : bool = FStar.Char.int_of_char c = 0x0A

(* `FStar.String.string_of_list` carries F*'s "special normalizer status"
   (FStar.String.fsti's own banner: "handled by F*'s normalizers") rather
   than being encoded as an ordinary uninterpreted SMT function symbol --
   confirmed by a standalone probe before landing this module: `assert
   (string_of_list a == string_of_list b)` from a HYPOTHESIS `h : a == b`
   in scope does NOT discharge via Z3 (Error 19), even though `assert (a
   == b)` from the very same `h` discharges trivially, and even though
   `assert_norm (string_of_list [] == "")` (a fully LITERAL argument)
   discharges fine on its own -- ordinary congruence closure ("equal
   arguments give an equal result for the same function") simply isn't
   available for this primitive once the argument is a variable rather
   than a literal, unlike a normal SMT function symbol. This tiny helper
   is the fix: `h : a == b` is used at TYPE-CHECKING time (F*'s own
   unifier substitutes `b` for `a` in the goal via the equality's
   witness) rather than being handed to Z3 as an SMT hypothesis, so `()`
   discharges it regardless of `string_of_list`'s SMT encoding. Every
   downstream lemma that needs to carry a proven `list`-level equality
   through `string_of_list` goes through this, instead of re-deriving
   the same workaround ad hoc. *)
val cong_string_of_list (a b : list FStar.Char.char)
  : Lemma (requires a == b)
          (ensures FStar.String.string_of_list a == FStar.String.string_of_list b)
let cong_string_of_list a b = ()

(* ------------------------------------------------------------------------
 * Single-pass line-boundary walk over a codepoint list.
 *
 * `complete` accumulates every character up to and including the LAST
 * newline seen so far (grows only when a newline is appended). `pending`
 * accumulates the characters of the CURRENT, not-yet-terminated line (no
 * newline inside it, ever -- see `split_lines_acc_pending_no_nl` below).
 * Both grow by `@ [hd]` (append at the end) rather than `hd :: acc` +
 * final reverse -- deliberately, so the RECONSTRUCTION invariant
 * (`complete @ pending @ tl == l`, `split_lines_acc_reconstruct` below) is
 * the walk's OWN loop invariant, provable by unfolding one step at a time
 * with `List.Tot.append_assoc`, rather than needing a separate "reverse
 * distributes over append" lemma at the end. O(n^2) in the worst case
 * (repeated `@ [hd]`) -- deliberately SPEC-shaped per the task brief ("no
 * performance tricks"), not the extraction target.
 * ------------------------------------------------------------------------ *)
let rec split_lines_acc (l : list FStar.Char.char) (complete : list FStar.Char.char) (pending : list FStar.Char.char)
  : Tot (list FStar.Char.char * list FStar.Char.char) (decreases l) =
  match l with
  | [] -> (complete, pending)
  | hd :: tl ->
    let pending' = pending @ [hd] in
    if is_nl hd then split_lines_acc tl (complete @ pending') []
    else split_lines_acc tl complete pending'

(* Reconstruction: at every step, what has been consumed into `complete`
   and `pending` plus what remains (`tl`/`l`) is exactly the original
   input -- the walk never drops or duplicates a character. *)
val split_lines_acc_reconstruct (l complete pending : list FStar.Char.char)
  : Lemma (requires True)
          (ensures (let (c, p) = split_lines_acc l complete pending in c @ p == complete @ pending @ l))
          (decreases l)
let rec split_lines_acc_reconstruct l complete pending =
  match l with
  | [] -> ()
  | hd :: tl ->
    let pending' = pending @ [hd] in
    if is_nl hd then begin
      split_lines_acc_reconstruct tl (complete @ pending') [];
      // IH: split_lines_acc tl (complete @ pending') [] gives (c,p) with
      // c @ p == (complete @ pending') @ [] @ tl == complete @ pending' @ tl.
      // Need: complete @ pending' @ tl == complete @ pending @ l
      //   where l == hd :: tl and pending' == pending @ [hd].
      List.Tot.append_assoc pending [hd] tl;
      List.Tot.append_assoc complete pending (hd :: tl);
      List.Tot.append_assoc complete (pending @ [hd]) tl
    end else begin
      split_lines_acc_reconstruct tl complete pending';
      // IH: c @ p == complete @ pending' @ tl == complete @ (pending @ [hd]) @ tl
      // Need: == complete @ pending @ l == complete @ pending @ (hd :: tl)
      List.Tot.append_assoc pending [hd] tl;
      List.Tot.append_assoc complete pending (hd :: tl)
    end

(* `pending` never contains a newline: every character appended to it is
   checked by `is_nl` and, if true, immediately flushed into `complete`
   with `pending` reset to `[]` in the SAME step -- so between any two
   steps, `pending` holds only non-newline characters. Stated as: no
   element of the FINAL `pending` half is a newline, given the STARTING
   `pending` argument already satisfies that (the recursion's own
   invariant; `split_complete_lines` below calls it with `pending = []`,
   vacuously satisfying the hypothesis). *)
val split_lines_acc_pending_no_nl (l complete pending : list FStar.Char.char)
  : Lemma (requires (forall c. List.Tot.memP c pending ==> ~ (is_nl c)))
          (ensures (let (_, p) = split_lines_acc l complete pending in
                    forall c. List.Tot.memP c p ==> ~ (is_nl c)))
          (decreases l)
let rec split_lines_acc_pending_no_nl l complete pending =
  match l with
  | [] -> ()
  | hd :: tl ->
    let pending' = pending @ [hd] in
    if is_nl hd then
      split_lines_acc_pending_no_nl tl (complete @ pending') []
    else begin
      // pending' == pending @ [hd]; every c in pending' is either in
      // pending (no-nl by hypothesis) or is hd itself (no-nl since this
      // branch is `not (is_nl hd)`).
      List.Tot.append_memP_forall pending [hd];
      assert (forall c. List.Tot.memP c pending' ==> List.Tot.memP c pending \/ List.Tot.memP c [hd]);
      assert (forall c. List.Tot.memP c [hd] ==> c == hd);
      split_lines_acc_pending_no_nl tl complete pending'
    end

(* ------------------------------------------------------------------------
 * String-level wrapper. `split_complete_lines s = (complete, carry)`:
 * `complete` is the prefix of `s` up to and including its LAST newline;
 * `carry` is the remainder (contains no newline, by
 * `split_complete_lines_carry_no_nl` below).
 * ------------------------------------------------------------------------ *)
val split_complete_lines (s : string) : Tot (string * string)
let split_complete_lines s =
  let (c, p) = split_lines_acc (FStar.String.list_of_string s) [] [] in
  (FStar.String.string_of_list c, FStar.String.string_of_list p)

(* Reconstruction at the string level: complete ^ carry == s. *)
val split_complete_lines_reconstruct (s : string)
  : Lemma (let (complete, carry) = split_complete_lines s in complete ^ carry == s)
let split_complete_lines_reconstruct s =
  let l = FStar.String.list_of_string s in
  split_lines_acc_reconstruct l [] [];
  let (c, p) = split_lines_acc l [] [] in
  // c @ p == [] @ [] @ l == l  (from reconstruct, complete = pending = [])
  assert (c @ p == l);
  let complete = FStar.String.string_of_list c in
  let carry = FStar.String.string_of_list p in
  FStar.String.list_of_concat complete carry;
  FStar.String.list_of_string_of_list c;
  FStar.String.list_of_string_of_list p;
  // list_of_string (complete ^ carry) == list_of_string complete @ list_of_string carry
  //                                    == c @ p == l == list_of_string s
  assert (FStar.String.list_of_string (complete ^ carry) == l);
  FStar.String.string_of_list_of_string (complete ^ carry);
  FStar.String.string_of_list_of_string s
  // complete ^ carry == string_of_list (list_of_string (complete^carry))
  //                   == string_of_list l == string_of_list (list_of_string s) == s

(* The carry never contains a complete line: no character in it is a
   newline. *)
val split_complete_lines_carry_no_nl (s : string)
  : Lemma (let (_, carry) = split_complete_lines s in
           forall c. List.Tot.memP c (FStar.String.list_of_string carry) ==> ~ (is_nl c))
let split_complete_lines_carry_no_nl s =
  let l = FStar.String.list_of_string s in
  split_lines_acc_pending_no_nl l [] [];
  let (_, p) = split_lines_acc l [] [] in
  FStar.String.list_of_string_of_list p

(* ------------------------------------------------------------------------
 * The two carry-composition facts the task brief names explicitly.
 * ------------------------------------------------------------------------ *)

(* If `s` contains no newline at all, splitting it produces an empty
   `complete` and the whole string as carry. Corollary used for "a chunk
   with no newline extends carry": feeding a newline-free chunk never
   flushes anything into `complete`, no matter what carry already holds
   (see `split_complete_lines_extend_carry` below, which specialises this
   to the `carry ^ chunk` shape `feed_chunk` actually uses). *)
val split_lines_acc_no_nl (l complete pending : list FStar.Char.char)
  : Lemma (requires (forall c. List.Tot.memP c l ==> ~ (is_nl c)))
          (ensures (let (c, p) = split_lines_acc l complete pending in
                     c == complete /\ p == pending @ l))
          (decreases l)
let rec split_lines_acc_no_nl l complete pending =
  match l with
  | [] -> append_l_nil pending
  | hd :: tl ->
    // hd is in l, so by hypothesis ~(is_nl hd) -- the `if` takes the
    // else branch unconditionally.
    assert (List.Tot.memP hd l);
    assert (~ (is_nl hd));
    split_lines_acc_no_nl tl complete (pending @ [hd]);
    append_assoc pending [hd] tl

val split_complete_lines_no_newline (s : string)
  : Lemma (requires (forall c. List.Tot.memP c (FStar.String.list_of_string s) ==> ~ (is_nl c)))
          (ensures (let (complete, carry) = split_complete_lines s in complete == "" /\ carry == s))
let split_complete_lines_no_newline s =
  split_lines_acc_no_nl (FStar.String.list_of_string s) [] [];
  List.Tot.append_nil_l (FStar.String.list_of_string s);
  let (c, p) = split_lines_acc (FStar.String.list_of_string s) [] [] in
  assert (c == [] /\ p == FStar.String.list_of_string s);
  // "carry == s" side: ordinary congruence on `p == list_of_string s`
  // works fine (string_of_list_of_string s finishes it).
  FStar.String.string_of_list_of_string s;
  // "complete == \"\"" side needs the `cong_string_of_list` workaround
  // (see that helper's banner): `string_of_list` does not get ordinary
  // SMT congruence from a variable known to equal `[]`.
  cong_string_of_list c [];
  assert_norm (FStar.String.string_of_list ([] <: list FStar.Char.char) == "")

(* "A chunk with no newline extends carry": splitting (carry ^ chunk),
   where `carry` already has no newline (the streaming invariant --
   `split_complete_lines_carry_no_nl` establishes it fresh out of every
   prior split, and `initial_state.carry = ""` trivially has none) and
   `chunk` has no newline either, yields `("", carry ^ chunk)` -- nothing
   is flushed, the new carry is exactly the concatenation. *)
val split_complete_lines_extend_carry (carry chunk : string)
  : Lemma (requires (forall c. List.Tot.memP c (FStar.String.list_of_string carry) ==> ~ (is_nl c)) /\
                    (forall c. List.Tot.memP c (FStar.String.list_of_string chunk) ==> ~ (is_nl c)))
          (ensures (let (complete, carry') = split_complete_lines (carry ^ chunk) in
                    complete == "" /\ carry' == carry ^ chunk))
let split_complete_lines_extend_carry carry chunk =
  FStar.String.list_of_concat carry chunk;
  List.Tot.append_memP_forall (FStar.String.list_of_string carry) (FStar.String.list_of_string chunk);
  assert (forall x. List.Tot.memP x (FStar.String.list_of_string (carry ^ chunk)) ==> ~ (is_nl x));
  split_complete_lines_no_newline (carry ^ chunk)

(* "A chunk ending in newline empties carry": if the LAST character of
   `s` is a newline, splitting `s` produces the whole string as `complete`
   and an empty carry. Stated over the list form (`l <> []` and its last
   element is a newline) since that is what the single-pass walk actually
   tracks; the string-level corollary follows via list_of_string. *)
val split_lines_acc_ends_in_newline (l complete pending : list FStar.Char.char)
  : Lemma (requires Cons? l /\ is_nl (List.Tot.last l))
          (ensures (let (c, p) = split_lines_acc l complete pending in p == []))
          (decreases l)
let rec split_lines_acc_ends_in_newline l complete pending =
  match l with
  | [hd] ->
    // last [hd] == hd, so is_nl hd holds; pending' = pending @ [hd];
    // the walk takes the newline branch and recurses on [] with
    // pending reset to [] -- base case of split_lines_acc returns that
    // [] immediately.
    ()
  | hd :: (tl : list FStar.Char.char) ->
    // Cons? tl (since l has >= 2 elements here), last l == last tl.
    let pending' = pending @ [hd] in
    if is_nl hd then
      split_lines_acc_ends_in_newline tl (complete @ pending') []
    else
      split_lines_acc_ends_in_newline tl complete pending'

val split_complete_lines_ends_in_newline (s : string)
  : Lemma (requires FStar.String.length s > 0 /\
                    is_nl (List.Tot.last (FStar.String.list_of_string s)))
          (ensures (let (complete, carry) = split_complete_lines s in carry == "" /\ complete == s))
let split_complete_lines_ends_in_newline s =
  let l = FStar.String.list_of_string s in
  // FStar.String.length s > 0 means strlen s = List.length l > 0, so l is Cons.
  (match l with
   | [] -> ()
   | _ :: _ -> ());
  split_lines_acc_ends_in_newline l [] [];
  split_lines_acc_reconstruct l [] [];
  let (c, p) = split_lines_acc l [] [] in
  // p == [] (just proved); c @ p == [] @ [] @ l == l, so c == l.
  assert (p == []);
  assert (c @ [] == l);
  append_l_nil c;
  assert (c == l);
  FStar.String.string_of_list_of_string s;
  // string_of_list c == string_of_list l == string_of_list (list_of_string s)
  // == s -- ordinary congruence on `c == l` works fine here (only the
  // "== \"\"" side needed the `cong_string_of_list` workaround below).
  cong_string_of_list p [];
  assert_norm (FStar.String.string_of_list ([] <: list FStar.Char.char) == "")

(* ============================================================================
 * Streaming API shape (task brief's sketch). `stream_state` carries the
 * bytes-after-the-last-complete-line seen so far; `feed_chunk` folds one
 * new chunk in; `finish` drains whatever partial line remains at end of
 * stream; `stream_parse` folds a whole chunk LIST. Each call to
 * `Parser.NQuads.parse_nquads_acc` below runs on a FRESH, self-contained
 * string with its OWN length-derived fuel (see the FUEL NOTE in the module
 * banner) -- `dataset_finalise` (which reverses each graph once, restoring
 * insertion order) is applied EXACTLY ONCE, at the very end of the whole
 * fold, matching `Parser.NQuads.parse_nquads`'s own placement -- applying
 * it per-chunk would scramble the O(1)-prepend accumulation order
 * `Parser.NQuads.dataset_add_quad`'s own comment documents.
 * ============================================================================ *)

type stream_state = { carry : string }
let initial_state : stream_state = { carry = "" }

let feed_chunk (st : stream_state) (chunk : string) (ds : RDF.Graph.Executable.rdf_dataset)
  : RDF.Graph.Executable.rdf_dataset * stream_state =
  let combined = st.carry ^ chunk in
  let (complete, carry') = split_complete_lines combined in
  let ds' = Parser.NQuads.parse_nquads_acc complete 0 ds (Parser.FastString.fs_byte_length complete + 1) in
  (ds', { carry = carry' })

let finish (st : stream_state) (ds : RDF.Graph.Executable.rdf_dataset) : RDF.Graph.Executable.rdf_dataset =
  Parser.NQuads.parse_nquads_acc st.carry 0 ds (Parser.FastString.fs_byte_length st.carry + 1)

let rec stream_parse_acc (chunks : list string) (ds : RDF.Graph.Executable.rdf_dataset) (st : stream_state)
  : Tot RDF.Graph.Executable.rdf_dataset (decreases chunks) =
  match chunks with
  | [] -> RDF.Graph.Executable.dataset_finalise (finish st ds)
  | c :: rest ->
    let (ds', st') = feed_chunk st c ds in
    stream_parse_acc rest ds' st'

let stream_parse (chunks : list string) : RDF.Graph.Executable.rdf_dataset =
  stream_parse_acc chunks RDF.Graph.Executable.empty_dataset initial_state

(* Batch reference point, for the (not-yet-proved) equivalence theorem:
   the SAME function `Parser.NQuads.parse_nquads` already is. Named here
   so the eventual theorem statement (see FINDING below) has a fixed name
   to cite; it is not a new definition. *)
let batch_parse (s : string) : RDF.Graph.Executable.rdf_dataset = Parser.NQuads.parse_nquads s

(* Left identity of `^` for strings: `"" ^ c == c`. Not automatic (`^`
   doesn't reduce for a symbolic `c`) -- proved the same way as
   `split_complete_lines_reconstruct` above, via `list_of_string`/
   `string_of_list` round trips, since `FStar.String` exposes no direct
   `strcat`-identity lemma of its own. *)
val empty_string_concat_left (c : string)
  : Lemma ("" ^ c == c)
let empty_string_concat_left c =
  FStar.String.list_of_concat "" c;
  assert_norm (FStar.String.list_of_string "" == []);
  cong_string_of_list (FStar.String.list_of_string "" @ FStar.String.list_of_string c)
                       (FStar.String.list_of_string c)
                       ;
  FStar.String.string_of_list_of_string ("" ^ c);
  FStar.String.string_of_list_of_string c

(* One concrete rewrite of `stream_parse [c]` down to its two constituent
   calls, for a single chunk starting from the empty state -- confirms the
   pipeline in the module banner's STATUS note actually reduces the way
   it is described (definitional unfolding + `initial_state.carry = ""`
   collapsing `"" ^ c` to `c` via `empty_string_concat_left`), independent
   of the unproved equivalence with `batch_parse`. *)
val stream_parse_single_chunk_shape (c : string)
  : Lemma (stream_parse [c] ==
           RDF.Graph.Executable.dataset_finalise
             (let (complete, carry) = split_complete_lines c in
              let ds1 = Parser.NQuads.parse_nquads_acc complete 0 RDF.Graph.Executable.empty_dataset
                          (Parser.FastString.fs_byte_length complete + 1) in
              Parser.NQuads.parse_nquads_acc carry 0 ds1 (Parser.FastString.fs_byte_length carry + 1)))
let stream_parse_single_chunk_shape c =
  empty_string_concat_left c

(* ============================================================================
 * PHASE 2 CHECKPOINT (task #48, 2026-08-11 landing): LINE-LEVEL LOCALITY
 * over byte reads -- prerequisite (2) from the FINDING below, narrowed to
 * exactly what the FINDING's own item 1 (`fs_byte_index_concat`, now
 * derivable now that prerequisite (1) `fs_byte_index_eq` has landed in
 * `Parser.FastString.fsti`) buys for free, PLUS the three-way "line
 * embedded in a larger string" shape `parse_nquads_acc_concat_line`
 * actually needs. This is checkpoint (a) from the task brief: the
 * shift/locality lemma stated over BYTE READS, not over string identity
 * -- exactly the register `RDF.NTriples.RoundTrip.fst`'s own FINDING
 * (Part 6 banner, "THE WALL, precisely") says is the only one that works
 * for a SYMBOLIC argument (`"" ^ s == s` / `(a^b)^c == a^(b^c)` both FAIL
 * for symbolic strings via plain `()`; position/byte-value facts do not
 * have that problem, since they bottom out in `nat`/`FStar.Char.char`
 * equalities that Z3 chains by ordinary transitivity).
 *
 * `lemma_fs_byte_index_concat`: the FINDING's item 1, done. A direct
 * corollary of the ALREADY-PROVED `Parser.FastString.Axioms.
 * fs_byte_at_concat` (byte-VALUE agreement across a concat split) plus
 * `Parser.FastString.fs_byte_index_eq` (the now-landed prerequisite (1)
 * bridging lemma, applied three times: once to the concatenation, once
 * to each operand) -- no new axiom, no Spec-level reasoning needed here,
 * since `fs_byte_at_concat` already did that work.
 *
 * `lemma_byte_index_at_middle`: checkpoint (a) itself. For a THREE-way
 * split `prefix ^ (mid ^ suffix)` (the shape `lemma_extract_middle` in
 * `RDF.NTriples.RoundTrip.fst` uses for the analogous `fs_byte_sub`
 * extraction), reading byte `i < length mid` at the SHIFTED position
 * `length prefix + i` inside the combined string agrees with reading
 * byte `i` of `mid` alone -- two applications of `lemma_fs_byte_index_
 * concat` (first peeling `prefix` off the outside, landing in the
 * "right operand, shifted" branch since `length prefix + i >= length
 * prefix`; then peeling `suffix` off `mid ^ suffix`, landing in the
 * "left operand" branch since `i < length mid`), chained by ordinary
 * SMT transitivity on the `FStar.Char.char` equalities both calls
 * produce. This is exactly "a chunk with a complete line embedded at
 * position `length prefix` reads the same bytes, at every position
 * inside that line, as the line read standalone" -- the LINE-level
 * locality fact prerequisite (2) opens with, stated the way the FINDING
 * requires: over byte reads, never over `^`/string identity.
 *
 * WHAT THIS DOES NOT CLOSE (still prerequisite (2)'s much larger
 * remainder): byte-read agreement is necessary but not sufficient for
 * `parse_nquads_acc_concat_line` -- the recursive-descent PARSER
 * (`parse_subject`/`parse_iri`/`parse_object` and their full call graph
 * through `Parser.Combinators.fst`) must be shown to take the SAME
 * control-flow branches and produce the SAME extracted VALUES when run
 * on `mid` embedded inside a larger string as it does on `mid` alone --
 * a per-combinator induction across `Parser.NTriples.fst` (1300+ lines),
 * not a corollary of the byte-read fact alone. `RDF.NTriples.RoundTrip
 * .fst`'s own Part 6 banner ("NEXT NARROWEST UNPROVED STATEMENT") probed
 * EXACTLY this shape one layer down (a "`scan_iri_end` commutes with
 * prefixing" shift lemma for ONE combinator) in the SAME 2026-08-11
 * session this checkpoint reuses `fs_byte_index_eq` from, and reports it
 * as "a genuinely separate multi-step induction ... that a 3-attempt
 * guard does not clear" even for a single combinator, let alone the full
 * `parse_subject`/`parse_iri`/`parse_object` call graph this module's
 * `parse_nquads_acc_concat_line` needs. Given that finding from the same
 * landing this checkpoint builds on, re-attempting the full per-
 * combinator induction here was assessed as certain to hit the identical
 * wall inside a 3-attempt budget, so it was not attempted directly --
 * per the task brief's own instruction ("do NOT burn the session on
 * attempt 4+"), the honest deliverable is this narrower, fully verified
 * checkpoint plus this sharpened pointer to the remaining work, not a
 * partial/stalled attempt at the full induction.
 * ============================================================================ *)

val lemma_fs_byte_index_concat (a b : string) (i : nat)
  : Lemma (requires i < Parser.FastString.fs_byte_length (a ^ b))
          (ensures (if i < Parser.FastString.fs_byte_length a
                    then Parser.FastString.fs_byte_index (a ^ b) i
                         == Parser.FastString.fs_byte_index a i
                    else Parser.FastString.fs_byte_index (a ^ b) i
                         == Parser.FastString.fs_byte_index b (i - Parser.FastString.fs_byte_length a)))
let lemma_fs_byte_index_concat a b i =
  Parser.FastString.Axioms.fs_byte_at_concat a b i;
  Parser.FastString.fs_byte_index_eq (a ^ b) i;
  // The `else` branch's `i - fs_byte_length a` is only well-typed as `nat`
  // once `i < fs_byte_length a` is refuted -- branching here (rather than
  // calling both `fs_byte_index_eq` instances unconditionally, as an
  // earlier draft of this proof did) lets F*'s refinement on `i` in the
  // `else` arm carry that fact, matching `fs_byte_at_concat`'s own
  // case split.
  if i < Parser.FastString.fs_byte_length a then
    Parser.FastString.fs_byte_index_eq a i
  else
    Parser.FastString.fs_byte_index_eq b (i - Parser.FastString.fs_byte_length a)

val lemma_byte_index_at_middle (prefix mid suffix : string) (i : nat)
  : Lemma (requires i < Parser.FastString.fs_byte_length mid)
          (ensures Parser.FastString.fs_byte_index (prefix ^ (mid ^ suffix))
                     (Parser.FastString.fs_byte_length prefix + i)
                   == Parser.FastString.fs_byte_index mid i)
let lemma_byte_index_at_middle prefix mid suffix i =
  Parser.FastString.Axioms.fs_byte_length_concat mid suffix;
  Parser.FastString.Axioms.fs_byte_length_concat prefix (mid ^ suffix);
  lemma_fs_byte_index_concat prefix (mid ^ suffix) (Parser.FastString.fs_byte_length prefix + i);
  lemma_fs_byte_index_concat mid suffix i

(* Right identity of `^` for strings: `c ^ "" == c`. Symmetric derivation
   to `empty_string_concat_left` above. *)
val empty_string_concat_right (c : string)
  : Lemma (c ^ "" == c)
let empty_string_concat_right c =
  FStar.String.list_of_concat c "";
  assert_norm (FStar.String.list_of_string "" == []);
  List.Tot.append_l_nil (FStar.String.list_of_string c);
  cong_string_of_list (FStar.String.list_of_string c @ FStar.String.list_of_string "")
                       (FStar.String.list_of_string c)
                       ;
  FStar.String.string_of_list_of_string (c ^ "");
  FStar.String.string_of_list_of_string c

(* ============================================================================
 * ITEM 4 (task #48 ordered work list item 4): `parse_nquads_acc_concat_line`
 * -- the two BOUNDARY cases, both FULLY GENERAL (no per-line/per-shape
 * restriction on the OTHER argument), landed this session; the interior
 * (both `complete` and `carry` non-empty) case is a FINDING below, not
 * closed.
 *
 * WHY THESE TWO CASES NEED NO SHAPE RESTRICTION AT ALL (the pleasant
 * surprise this landing found). Every OTHER lemma in this file/
 * `Parser.NTriples.Locality.fst` needs an embedding argument (byte-read
 * agreement propagated through a recursive-descent parse) BECAUSE one
 * string is a PROPER, NON-EMPTY middle piece of a larger one, with real
 * bytes on both sides that the recursion must be shown to treat
 * identically. Both cases below instead have ONE OF THE TWO OPERANDS BE
 * THE EMPTY STRING -- and `parse_nquads_acc s pos ds fuel`'s OWN
 * definition (`Parser.NQuads.fst`) returns `ds` UNCHANGED, UNCONDITIONALLY
 * on ANY content, the moment `pos >= fs_byte_length s` -- which is exactly
 * `pos = 0 >= fs_byte_length "" = 0`. So `parse_nquads_acc "" 0 X (n+1) ==
 * X` for ANY `X`/`n`, by ONE step of DEFINITIONAL unfolding, no embedding,
 * no per-line reasoning, no scan witnesses. Combined with the `^`-identity
 * laws (`""^c==c`, `c^""==c`), the two cases below are PURE ALGEBRA over
 * that one fact plus string identity -- they hold for ANY `complete`/
 * `carry` content whatsoever, well-formed or not, single-line or
 * multi-line, any subject/object/graph shape, any escapes.
 * ============================================================================ *)

#push-options "--fuel 2 --ifuel 2"
val parse_nquads_acc_concat_line_empty_complete (carry : string) (ds : RDF.Graph.Executable.rdf_dataset)
  : Lemma
      (ensures
        Parser.NQuads.parse_nquads_acc carry 0
          (Parser.NQuads.parse_nquads_acc "" 0 ds (Parser.FastString.fs_byte_length "" + 1))
          (Parser.FastString.fs_byte_length carry + 1)
        == Parser.NQuads.parse_nquads_acc ("" ^ carry) 0 ds
             (Parser.FastString.fs_byte_length ("" ^ carry) + 1))
let parse_nquads_acc_concat_line_empty_complete carry ds =
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_left carry
#pop-options

#push-options "--fuel 2 --ifuel 2"
val parse_nquads_acc_concat_line_empty_carry (complete : string) (ds : RDF.Graph.Executable.rdf_dataset)
  : Lemma
      (ensures
        Parser.NQuads.parse_nquads_acc "" 0
          (Parser.NQuads.parse_nquads_acc complete 0 ds (Parser.FastString.fs_byte_length complete + 1))
          (Parser.FastString.fs_byte_length "" + 1)
        == Parser.NQuads.parse_nquads_acc (complete ^ "") 0 ds
             (Parser.FastString.fs_byte_length (complete ^ "") + 1))
let parse_nquads_acc_concat_line_empty_carry complete ds =
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_right complete
#pop-options

(* ============================================================================
 * ITEM 5 (task #48 ordered work list item 5): `theorem_stream_eq_batch`,
 * SINGLE CHUNK -- landed UNCONDITIONALLY (no per-line/shape restriction,
 * inherited from item 4's two boundary cases being shape-free) for the
 * scope every real single-chunk call satisfies whenever the chunk does
 * not end mid-line: `c` has NO newline at all (`split_complete_lines`
 * puts everything in `carry`, `complete = ""` -- item 4's first case), OR
 * `c` ENDS in a newline (`complete = c`, `carry = ""` -- item 4's second
 * case). This is `stream_parse [c] == batch_parse c` for exactly those
 * `c` -- a real, if scope-limited, streaming/batch equivalence with NO
 * hypothesis on `c`'s internal RDF content (well-formed or not, single-
 * line or multi-line, any escapes) -- only on where the chunk boundary
 * falls relative to `c`'s OWN newlines.
 *
 * WHAT REMAINS OPEN (the genuinely hard case, and the general multi-
 * chunk theorem, item 6): `c` containing ONE OR MORE newlines WITHOUT
 * ending in one -- i.e. `split_complete_lines c` yields a NON-EMPTY
 * `complete` AND a NON-EMPTY `carry`. See the FINDING at the bottom of
 * this file for the precise obstruction (now sharpened past the
 * 2026-08-11 landing's own FINDING): it is not "harder embedding", it is
 * a DIFFERENT, PROVABLY UNAVOIDABLE further primitive (`lemma_parse_
 * nquads_acc_restart`, named and analysed in that FINDING) that
 * `parse_nquads_acc_concat_line`'s INTERIOR case needs and item 4's two
 * boundary cases structurally cannot supply (they work BECAUSE one side
 * is empty, sidestepping exactly the primitive the interior case needs).
 * ============================================================================ *)
#push-options "--fuel 2 --ifuel 2"
val theorem_stream_eq_batch_single_chunk_no_newline (c : string)
  : Lemma
      (requires (forall ch. List.Tot.memP ch (FStar.String.list_of_string c) ==> ~ (is_nl ch)))
      (ensures stream_parse [c] == batch_parse c)
let theorem_stream_eq_batch_single_chunk_no_newline c =
  stream_parse_single_chunk_shape c;
  split_complete_lines_no_newline c;
  // split_complete_lines c == ("", c): fst == "", snd == c.
  parse_nquads_acc_concat_line_empty_complete (snd (split_complete_lines c)) RDF.Graph.Executable.empty_dataset;
  empty_string_concat_left (snd (split_complete_lines c))
#pop-options

#push-options "--fuel 2 --ifuel 2"
val theorem_stream_eq_batch_single_chunk_ends_in_newline (c : string)
  : Lemma
      (requires FStar.String.length c > 0 /\ is_nl (List.Tot.last (FStar.String.list_of_string c)))
      (ensures stream_parse [c] == batch_parse c)
let theorem_stream_eq_batch_single_chunk_ends_in_newline c =
  stream_parse_single_chunk_shape c;
  split_complete_lines_ends_in_newline c;
  // split_complete_lines c == (c, ""): fst == c, snd == "".
  parse_nquads_acc_concat_line_empty_carry (fst (split_complete_lines c)) RDF.Graph.Executable.empty_dataset;
  empty_string_concat_right (fst (split_complete_lines c))
#pop-options

(* Unified statement: either boundary condition suffices. `batch_parse`
   already IS `Parser.NQuads.parse_nquads`, which itself applies
   `dataset_finalise` (Parser.NQuads.fst's own `parse_nquads`) -- so the
   clean top-level equation is `stream_parse [c] == batch_parse c`
   directly (no extra `dataset_finalise` wrapper needed at this level;
   the two lemmas above expose the intermediate un-wrapped form for
   composability with item 4, this wrapper restates it against the named
   `batch_parse` entry point the module banner promised). *)
val theorem_stream_eq_batch_single_chunk (c : string)
  : Lemma
      (requires
        (forall ch. List.Tot.memP ch (FStar.String.list_of_string c) ==> ~ (is_nl ch)) \/
        (FStar.String.length c > 0 /\ is_nl (List.Tot.last (FStar.String.list_of_string c))))
      (ensures stream_parse [c] == batch_parse c)
let theorem_stream_eq_batch_single_chunk c =
  if FStar.String.length c = 0 then begin
    // c = "" has no newline (vacuously) -- take the no-newline branch;
    // batch_parse "" == dataset_finalise (parse_nquads_acc "" 0 empty 1)
    // == dataset_finalise empty_dataset by the same unfolding, matching
    // stream_parse [""] via the no-newline case directly.
    theorem_stream_eq_batch_single_chunk_no_newline c
  end else if is_nl (List.Tot.last (FStar.String.list_of_string c)) then
    theorem_stream_eq_batch_single_chunk_ends_in_newline c
  else
    theorem_stream_eq_batch_single_chunk_no_newline c

(* ============================================================================
 * ITEM 6 (task #48 ordered work list item 6): `theorem_stream_eq_batch`,
 * GENERAL (arbitrary chunk list) -- NOT proved this landing. FINDING,
 * sharpened past both the module banner's own FINDING and `Parser.
 * NTriples.Locality.fst`'s "STATUS UPDATE" banner (now a THIRD
 * independent confirmation, from a third entry point: item 4/5's
 * boundary-case proof above, which shows PRECISELY where the "no
 * restriction needed" argument stops working).
 *
 * WHAT WOULD BE NEEDED, NAMED PRECISELY. Item 4's two boundary cases
 *(`complete=""` / `carry=""`) close because `parse_nquads_acc`'s `pos >=
 * length` base case fires UNCONDITIONALLY on the empty side, needing no
 * per-line reasoning about the OTHER (non-empty) side's content at all.
 * The moment BOTH `complete` and `carry` are non-empty -- the case a real
 * chunk boundary landing MID-DOCUMENT (not just mid-LINE) produces, and
 * exactly the case the general multi-chunk fold needs at every internal
 * boundary -- this shortcut is unavailable, and the proof needs a
 * genuinely different primitive:
 *
 *   val lemma_parse_nquads_acc_restart (a b : string) (ds : rdf_dataset) (fuel : nat)
 *     : Lemma (parse_nquads_acc (a ^ b) (fs_byte_length a) ds fuel
 *              == parse_nquads_acc b 0 ds fuel)
 *
 * i.e. "`b` embedded at the offset right after `a` behaves like `b` run
 * standalone from position 0" -- NOT a corollary of the two boundary
 * cases (those degenerate exactly BECAUSE one operand is empty; this
 * lemma is about TWO non-empty strings, `a` playing prefix, `b` playing
 * the whole remainder with nothing after it). `parse_nquads_acc_concat_
 * line`'s general (interior) case reduces to `lemma_parse_nquads_acc_
 * restart` plus a fuel-monotonicity fact ("extra fuel is harmless once
 * `pos >= length` is reached before fuel exhausts" -- itself a short,
 * mechanical induction in the SAME style as this landing's `Parser.
 * NTriples.Locality.fst` `_headroom` lemmas, NOT the blocking piece).
 *
 * THE ACTUAL BLOCKER, diagnosed precisely (not "harder embedding"):
 * proving `lemma_parse_nquads_acc_restart` for `b` of UNRESTRICTED
 * (arbitrary-shape, arbitrary-escape) N-Quads content requires, at every
 * position inside `b` where `parse_nquads_acc`'s recursion attempts a
 * quad (`parse_nquad`), a FORWARD lemma: "GIVEN `parse_nquad b p ==
 * ParseOk (t,g) p'` (success, of WHATEVER shape it turns out to be),
 * THEN the embedded call succeeds identically" -- with the shape
 * discovered BY THE PROOF, not supplied by an external caller (unlike
 * every lemma THIS session's items 1-3 added, which all take the
 * relevant scan/branch witnesses as EXPLICIT PARAMETERS the caller
 * already possesses from having matched on a CONCRETE line). Attempting
 * such a forward lemma reduces, in the IRI-subject/predicate/object
 * sub-case, to EXACTLY the abandoned `parse_iri_raw` FULL capstone in
 * `Parser.NTriples.Locality.fst` (fast path vs. escape path unified
 * behind one outer dispatch) -- the SAME "Could not prove post-
 * condition" wall that capstone's three restructured attempts did not
 * clear, for the SAME underlying reason (an internal `scan_iri_end`
 * outcome, not a directly-observable byte, is what must be dispatched
 * on to know which of two DIFFERENT already-proved lemmas applies).
 * `parse_object`'s literal branch has the identical shape one level
 * further in (`scan_string_fast` fast path vs. `parse_string_body`
 * escape path). This is now confirmed from THREE independent entry
 * points across two sessions: `RDF.NTriples.RoundTrip.fst`'s Part 6
 * probe (one combinator), this file's ORIGINAL 2026-08-11 FINDING (the
 * whole-line locality gate), and `Parser.NTriples.Locality.fst`'s own
 * abandoned capstone (the closest anyone has gotten, with the exact
 * three failed restatements on record) -- not a fresh guess.
 *
 * A TRACTABLE PATH, if a future session wants item 6 without clearing
 * that wall: restrict `b` (and every non-boundary `complete`) to chunks
 * whose EVERY quad line matches ONE fixed, WITNESSED shape (e.g. all-
 * IRI-nograph, no escapes -- `Parser.NTriples.Locality.fst`'s `lemma_
 * parse_nquad_iri_nograph_shift`/`lemma_parse_nquad_shift_generic`
 * already cover this), with witnesses threaded through the chunk list
 * as an explicit parallel witness list (structural induction on that
 * list, not on the chunks' own byte content) -- sidesteps the forward-
 * dispatch problem entirely because the shape is never "discovered", it
 * is supplied. NOT attempted this landing: session budget was spent
 * landing items 1-5 (real, verified, no-restriction-needed results) over
 * a same-session attempt at this narrower-but-still-substantial
 * generalisation.
 * ============================================================================ *)

(* ============================================================================
 * FINDING (guard-depth-3 stop, per CLAUDE.md/subagent-prompting discipline)
 * -- `theorem_stream_eq_batch` is NOT proved in this landing, ORIGINALLY.
 *
 * STATUS UPDATE (same-session closing landing, later 2026-08-11): the
 * DIAGNOSIS below (item 2, "a per-combinator induction across a 1300+
 * line module ... does not fit a 3-attempt guard") is CONFIRMED, but NOT
 * the whole story -- `Parser.NTriples.Locality.fst`'s SAME-session
 * closing landing DID close item 2 for a SCOPED but real slice (all-IRI
 * subject/predicate/object, no graph label, plus separately the bnode/
 * plain-literal/@lang branches for `parse_subject`/`parse_object`), via
 * `lemma_parse_nquad_shift_generic`. Building on that, THIS file's ITEM 4
 * (`parse_nquads_acc_concat_line`, below the `PHASE 2 CHECKPOINT` banner)
 * and ITEM 5 (`theorem_stream_eq_batch_single_chunk`) are now CLOSED --
 * unconditionally (no shape restriction at all) for chunks that do not
 * end mid-line, which turned out not to need item 2's per-combinator
 * induction at all (the empty-string boundary case sidesteps it
 * entirely; see item 4's own banner for why). ITEM 6 (general multi-
 * chunk) remains open, now with a SHARPER named obstruction (`lemma_
 * parse_nquads_acc_restart`) than this original FINDING's "per-
 * combinator induction" framing -- see item 6's own banner. The
 * remainder of THIS banner (items 1/2's own text) is KEPT VERBATIM below
 * as the original diagnosis trail; read it alongside items 4-6 above,
 * not in place of them.
 *
 * WHAT IT NEEDS. `stream_parse [c] == batch_parse c` (the single-chunk
 * case, the base case any general fold theorem inducts on) reduces, via
 * `stream_parse_single_chunk_shape` above and `split_complete_lines_
 * reconstruct` (`complete ^ carry == c`), to exactly one missing lemma:
 *
 *   val parse_nquads_acc_concat_line (complete carry : string) (ds : rdf_dataset)
 *     : Lemma (requires (* complete is "" or ends in a newline -- exactly
 *                          split_complete_lines's own postcondition *))
 *             (ensures
 *               Parser.NQuads.parse_nquads_acc carry 0
 *                 (Parser.NQuads.parse_nquads_acc complete 0 ds (fs_byte_length complete + 1))
 *                 (fs_byte_length carry + 1)
 *               == Parser.NQuads.parse_nquads_acc (complete ^ carry) 0 ds
 *                    (fs_byte_length (complete ^ carry) + 1))
 *
 * i.e. "processing `complete` then `carry` separately, chaining the
 * dataset, gives the same result as processing `complete ^ carry` in one
 * pass" -- the fundamental split/monoid law the whole streaming design
 * rests on. THREE ATTEMPTS at a DIRECT proof were not made in this
 * landing -- the obstruction was diagnosed up front (not discovered by
 * trial and error) and is large enough that spending the 3-attempt budget
 * on it would not have produced a partial win worth keeping:
 *
 * `parse_nquads_acc` dispatches its control flow on `FStar.Char.int_of_char
 * (Parser.FastString.fs_byte_index input pos)` and, deeper inside
 * `Parser.NQuads.parse_nquad`, calls `Parser.NTriples.parse_subject` /
 * `parse_iri` / `parse_object` -- each a further recursive-descent walk
 * (escape sequences, IRI validation, language tags, datatypes;
 * `Parser.NTriples.fst` is 1300+ lines) that itself calls `fs_byte_index`
 * / `fs_byte_at` / `fs_byte_sub` at MANY internal positions. Proving
 * `parse_nquads_acc_concat_line` requires, at minimum:
 *
 *   1. `fs_byte_index_concat` -- CLOSED this session (phase 2 landing,
 *      below the FINDING). Prerequisite (1), `fs_byte_index_eq` in
 *      `Parser.FastString.fsti`/`.fst`, landed in the SAME 2026-08-11
 *      session as `RDF.NTriples.RoundTrip.fst`'s checkpoint (a) (see
 *      that module's banner) -- it was NOT re-derived here, it was
 *      already on `claude/main` when this worktree was cut. With it in
 *      hand, `fs_byte_index_concat` is a three-line corollary of the
 *      ALREADY-PROVED `fs_byte_at_concat` (`Parser.FastString.Axioms.
 *      fst`) plus `fs_byte_index_eq` applied to both sides -- see
 *      `lemma_fs_byte_index_concat` and its three-way-split corollary
 *      `lemma_byte_index_at_middle` immediately above this FINDING
 *      (PHASE 2 CHECKPOINT banner has the full derivation). Both verify
 *      clean, no new axiom.
 *   2. A LOCALITY lemma for `parse_subject` / `parse_iri` / `parse_object`
 *      (and their full call graph through `Parser.Combinators.fst`'s
 *      `ptake_while` / `pquoted_string` / etc.): that each behaves
 *      IDENTICALLY on `complete ^ carry` at any position `p < fs_byte_length
 *      complete` as it does on `complete` alone -- both control flow
 *      (which branch is taken) AND extracted VALUES (every `fs_byte_sub`
 *      call inside a still-open line targets a range wholly inside
 *      `complete`, so `fs_byte_sub_concat_left` supplies the value
 *      equality, and now item 1's `lemma_byte_index_at_middle` supplies
 *      the byte-index agreement that lets the SAME branches even be
 *      reached). STILL OPEN -- this is a per-combinator induction across
 *      a 1300+ line module, not a single lemma, and it is now backed by
 *      independent evidence that it does not fit a 3-attempt guard: the
 *      SAME 2026-08-11 session that landed `fs_byte_index_eq` also
 *      probed EXACTLY this shape one layer down, for a SINGLE combinator
 *      (`scan_iri_end`), in `RDF.NTriples.RoundTrip.fst`'s Part 6 banner
 *      ("NEXT NARROWEST UNPROVED STATEMENT" / "THE WALL, precisely") --
 *      and reports it as requiring a "genuinely separate multi-step
 *      induction ... that a 3-attempt guard does not clear," even before
 *      reaching `parse_object`'s literal-with-escapes branch or
 *      `parse_iri_raw`'s `%`-escape handling. The honest size estimate
 *      is a SEPARATE landing, not a same-session extension of this one
 *      -- confirmed twice now, by two different sessions approaching it
 *      from two different entry points (round-trip vs. streaming).
 *
 * NARROWEST VERIFIED CHECKPOINT (phase 1): `split_complete_lines` and its
 * five lemmas above (`split_complete_lines_reconstruct`, `_carry_no_nl`,
 * `_no_newline`, `_extend_carry`, `_ends_in_newline`), plus `stream_parse_
 * single_chunk_shape`'s definitional rewrite.
 *
 * NARROWEST VERIFIED CHECKPOINT (phase 2, this landing):
 * `lemma_fs_byte_index_concat` and `lemma_byte_index_at_middle` (PHASE 2
 * CHECKPOINT banner above) -- item 1 above, CLOSED.
 *
 * All of the above verify under `make RDF.NQuads.Streaming.fst.checked`
 * with no admits, no `--lax`, no new `assume val`.
 *
 * NEXT NARROWEST UNPROVED STATEMENT: item 2 above -- the per-combinator
 * locality induction over `Parser.NTriples.fst`'s recursive-descent call
 * graph. Gating step before `parse_nquads_acc_concat_line` (and hence
 * `theorem_stream_eq_batch`) can be attempted meaningfully; not started
 * here, see item 2's text for why and for the concrete pointer
 * (`RDF.NTriples.RoundTrip.fst`'s Part 6 banner) to where a future
 * session should pick this up.
 * ============================================================================ *)

(* ============================================================================
 * ITEM 6 CONTINUED (task #48, 2026-08-11 SECOND landing, general multi-
 * chunk `theorem_stream_eq_batch`): two new self-contained primitives, then
 * the CONDITIONED general restart theorem the FAILURE-BRANCH of this task's
 * own brief sanctions ("premise: every complete line parses successfully;
 * boolean/witness-supplied premise" is an ACCEPTABLE landing) -- NOT the
 * unconditional `lemma_parse_nquads_acc_restart` named in the FINDING
 * above, which still needs the full per-combinator forward-dispatch
 * capstone that FINDING (and `Parser.NTriples.Locality.fst`'s own
 * abandoned `parse_iri_raw` capstone) diagnoses as not fitting a
 * guard-depth-3 budget. This landing does not re-attempt that wall.
 *
 * TWO NEW PRIMITIVES, why they are new (not already in `Parser.NTriples.
 * Locality.fst`):
 *
 * `lemma_skip_comment_shift` -- fills EXACTLY the gap that file's own
 * Stage 3 Item 4 banner named ("comment/blank-line/error-recovery
 * scanners... `skip_comment`/`skip_line`'s local-`let rec` obstacle") and
 * then partially closed (lifting `nt_skip_to_eol`/`nq_skip_line` to
 * top-level, proving THEIR shift lemmas) without composing the FINAL
 * one-line wrapper for `skip_comment` itself. `skip_comment`'s own body
 * (`Parser.NTriples.fst`) is `if pos>=len then pos else if byte=='#' then
 * nt_skip_to_eol input len (pos+1) (len-pos) else pos` -- a direct
 * corollary of the already-proved `Parser.NTriples.Locality.
 * lemma_nt_skip_to_eol_shift`, taking the scan's own termination witness
 * (`stop_pos`) as an explicit parameter (this file's own established
 * style, matching `lemma_scan_iri_end_shift`'s `gt_pos` parameter)
 * rather than trying to derive it internally. `skip_comment`'s internal
 * call always has ONE UNIT of fuel headroom BY CONSTRUCTION (`p+fuel =
 * (pos+1)+(len-pos) = len+1 > len`, unconditionally, no monotonicity
 * argument needed) -- `lemma_nt_skip_to_eol_shift`'s own `p+fuel >
 * fs_byte_length mid` hypothesis is satisfied for free.
 *
 * `lemma_nq_skip_line_shift_exact` -- `Parser.NTriples.Locality.
 * lemma_nq_skip_line_shift` (the fail-branch scanner shift, already
 * proved there) takes a FREE fuel parameter `f` and requires `p + f >
 * fs_byte_length mid` STRICTLY. `parse_nquads_acc`'s REAL call site
 * (`nq_skip_line input len pos1 (len - pos1)`, `Parser.NQuads.fst`'s
 * fail branch) gives `p + f = pos1 + (len - pos1) = len` EXACTLY -- one
 * short of that lemma's own precondition, so it cannot be invoked
 * directly at the real call site. Rather than a separate fuel-
 * monotonicity bridging lemma (extra fuel is harmless once a stop is
 * reached with positive fuel to spare -- itself provable, but an extra
 * moving part), this landing proves a SELF-CONTAINED variant with the
 * fuel PINNED to `fs_byte_length mid - p` throughout (matching the real
 * call site exactly, both on `mid` and on the embedding, so the
 * `p + f > len` inequality is never needed: the `decreases` metric is
 * `fs_byte_length mid - p` itself, and the `p >= fs_byte_length mid`
 * vacuous case is handled by the SAME contradiction argument
 * `lemma_nq_skip_line_shift`'s own proof uses, just derived from the
 * metric hitting 0 rather than from a separate `f = 0` guard). Same
 * proof technique as the borrowed lemma (byte-agreement via
 * `lemma_byte_index_at_middle`, composing the already-proved `Parser.
 * NTriples.Locality.lemma_skip_eol_shift` at the newline-found leaf), no
 * new axiom, no new difficulty class -- a fuel-bookkeeping variant of an
 * already-proved lemma, not a fresh induction.
 * ============================================================================ *)

#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_skip_comment_shift (prefix mid suffix : string) (pos stop_pos : nat)
  : Lemma
      (requires
        pos < Parser.FastString.fs_byte_length mid /\
        FStar.Char.int_of_char (Parser.FastString.fs_byte_index mid pos) = 0x23 /\
        Parser.NTriples.nt_skip_to_eol mid (Parser.FastString.fs_byte_length mid) (pos + 1)
          (Parser.FastString.fs_byte_length mid - pos) == stop_pos /\
        stop_pos < Parser.FastString.fs_byte_length mid)
      (ensures
        Parser.NTriples.skip_comment (prefix ^ (mid ^ suffix)) (Parser.FastString.fs_byte_length prefix + pos)
        == Parser.FastString.fs_byte_length prefix + stop_pos)
let lemma_skip_comment_shift prefix mid suffix pos stop_pos =
  Parser.FastString.Axioms.fs_byte_length_concat mid suffix;
  Parser.FastString.Axioms.fs_byte_length_concat prefix (mid ^ suffix);
  lemma_byte_index_at_middle prefix mid suffix pos;
  Parser.NTriples.Locality.lemma_nt_skip_to_eol_shift prefix mid suffix (pos + 1)
    (Parser.FastString.fs_byte_length mid - pos) (Parser.FastString.fs_byte_length suffix) stop_pos
#pop-options

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_nq_skip_line_shift_exact (prefix mid suffix : string) (p stop_pos : nat)
  : Lemma
      (requires
        p <= Parser.FastString.fs_byte_length mid /\
        Parser.NQuads.nq_skip_line mid (Parser.FastString.fs_byte_length mid) p
          (Parser.FastString.fs_byte_length mid - p) == stop_pos /\
        stop_pos < Parser.FastString.fs_byte_length mid /\
        (Parser.FastString.fs_byte_length suffix = 0 \/ Parser.FastString.fs_byte_at suffix 0 <> 0x0A))
      (ensures
        Parser.NQuads.nq_skip_line (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length (prefix ^ (mid ^ suffix)))
          (Parser.FastString.fs_byte_length prefix + p)
          ((Parser.FastString.fs_byte_length mid - p) + Parser.FastString.fs_byte_length suffix)
        == Parser.FastString.fs_byte_length prefix + stop_pos)
      (decreases (Parser.FastString.fs_byte_length mid - p))
let rec lemma_nq_skip_line_shift_exact prefix mid suffix p stop_pos =
  let len_mid = Parser.FastString.fs_byte_length mid in
  Parser.FastString.Axioms.fs_byte_length_concat mid suffix;
  Parser.FastString.Axioms.fs_byte_length_concat prefix (mid ^ suffix);
  if p >= len_mid then ()
  else begin
    lemma_byte_index_at_middle prefix mid suffix p;
    let c = Parser.FastString.fs_byte_index mid p in
    let cc = FStar.Char.int_of_char c in
    if cc = 0x0A || cc = 0x0D then
      Parser.NTriples.Locality.lemma_skip_eol_shift prefix mid suffix p
    else
      lemma_nq_skip_line_shift_exact prefix mid suffix (p + 1) stop_pos
  end
#pop-options

(* ============================================================================
 * FINDING (guard-depth-3 stop, second landing, 2026-08-11): a
 * `lemma_parse_nquads_acc_restart` instance for the NARROWEST possible
 * multi-line scope ("mid" = blank lines only, no comments, no quads --
 * `forall q < fs_byte_length mid, pws mid q lands strictly inside mid on
 * a byte in {0x0A, 0x0D}`) was ATTEMPTED and NOT CLOSED after three
 * restructured attempts, each verified NOT to be a quick rejection but a
 * genuine multi-minute z3 search (10-16 minutes of 100% z3 CPU each,
 * confirmed via `ps` on the live `z3-4.13.3` child process, not a
 * trivially-false query):
 *
 *   1. Direct proof (induction on fuel, mirroring `parse_nquads_acc`'s
 *      own branch order, composing `Parser.NTriples.Locality.
 *      lemma_pws_shift` + `lemma_skip_eol_shift` with `suffix = ""`,
 *      rewritten to `prefix ^ mid` via `empty_string_concat_right` +
 *      ordinary congruence). Failed: "Assertion failed" pointing at
 *      `Parser.NTriples.Locality.fst`'s OWN `lemma_skip_eol_shift`
 *      `requires` span -- traced to a missing `fs_byte_length_empty ()`
 *      call (needed so Z3 knows `fs_byte_length "" = 0` to discharge
 *      that lemma's `suffix`-empty disjunct) -- a real bug, fixed.
 *   2. Same, with the missing `fs_byte_length_empty ()` call added.
 *      Failed differently: "Could not prove post-condition" against the
 *      lemma's own `ensures`, generic span -- diagnosed as the
 *      `prefix ^ (mid ^ "")` vs `prefix ^ mid` congruence rewrite not
 *      reliably propagating through THREE further function layers
 *      (`pws`, `fs_byte_index`, `skip_eol`, then `parse_nquads_acc`
 *      itself) from one base `mid ^ "" == mid` fact alone.
 *   3. Same, with EXPLICIT intermediate `assert`s restating each
 *      Locality lemma's conclusion directly in `prefix ^ mid` form
 *      (forcing the congruence rewrite at each layer by hand rather
 *      than relying on it propagating unaided). Failed again: generic
 *      "Assertion failed" pointing at the enclosing `Tot`/termination
 *      machinery in `Prims.fst`, after ~16 minutes of continuous z3
 *      search at `--z3rlimit 300` -- consistent with the query
 *      exhausting the resource limit during search rather than being
 *      quickly refuted, i.e. genuinely hard for the solver, not wrong
 *      by a small fixable margin.
 *
 * DIAGNOSIS (why, not just that): the three attempts' escalating
 * failure modes (missing-fact -> congruence-propagation -> resource-
 * exhaustion) point at the HYPOTHESIS SHAPE itself, not any one
 * `assert`. `forall (q:nat). q < fs_byte_length mid ==> (match pws mid q
 * with ParseOk () q1 -> ... | ParseFail _ _ -> True)` has NO natural SMT
 * trigger term for E-matching (the quantified body's head is a `match`
 * on a function application, not a flat predicate over `q`) -- every
 * lemma already verified in this file and in `Parser.NTriples.
 * Locality.fst` states its per-position facts via EXPLICIT WITNESS
 * PARAMETERS (`gt_pos`, `stop_pos`, `pos1`...`pos8`, etc.), never via a
 * bare `forall` over an opaque parser's output. This landing's `forall`
 * hypothesis is the FIRST use of that shape in either file, and the
 * failure pattern (increasingly expensive, ultimately resource-
 * exhausting z3 searches) is consistent with poor or absent
 * quantifier instantiation forcing Z3 to fall back to expensive
 * heuristics rather than a clean single ground substitution.
 *
 * THE FIX A FUTURE SESSION SHOULD TRY FIRST (not attempted here --
 * guard-depth-3 exhausted on the `forall` formulation itself): restate
 * `lemma_parse_nquads_acc_restart_blanks_only` WITHOUT a universally
 * quantified hypothesis at all, following this file's and `Parser.
 * NTriples.Locality.fst`'s own established style throughout -- thread
 * an EXPLICIT WITNESS per recursive step instead. Concretely, parameterize
 * the lemma by an explicit `stop_pos` witness for `pws`'s landing
 * position AND for `skip_eol`'s landing position AT THE CALL SITE (the
 * caller already knows these concretely, from having matched `mid`'s
 * actual content one line at a time), rather than deriving them from a
 * `forall` instantiated inside the proof. This exactly mirrors how
 * `lemma_skip_comment_shift`/`lemma_nq_skip_line_shift_exact` above
 * (THIS landing, verified clean) already take their termination
 * positions as explicit parameters rather than discovering them --
 * apply the SAME discipline one level up, at the `parse_nquads_acc`
 * recursion itself, not just at the scanner level.
 *
 * WHAT IS VERIFIED FROM THIS SECOND LANDING (both self-contained, no
 * admits, no `--lax`, no new `assume val`, both under `make verify-RDF.
 * NQuads.Streaming`):
 *   - `lemma_skip_comment_shift` -- closes the exact gap `Parser.
 *     NTriples.Locality.fst`'s Stage 3 Item 4 banner named and left
 *     unclosed after lifting `nt_skip_to_eol` to top level (the final
 *     one-line composition into `skip_comment` itself).
 *   - `lemma_nq_skip_line_shift_exact` -- resolves the fuel-tightness
 *     gap between `Parser.NTriples.Locality.lemma_nq_skip_line_shift`'s
 *     strict `p + f > fs_byte_length mid` precondition and
 *     `parse_nquads_acc`'s real fail-branch call site (`p + f =
 *     fs_byte_length mid` exactly).
 *
 * NEITHER PRIMITIVE ALONE CLOSES `lemma_parse_nquads_acc_restart` OR
 * `theorem_stream_eq_batch` (general) -- they are INGREDIENTS for the
 * per-line induction over `parse_nquads_acc`'s recursion (comment-line
 * and fail-line legs respectively), which itself needs the `forall`-free
 * restructuring above before any of the three legs (comment, blank,
 * quad) can be assembled into that induction. The general
 * `theorem_stream_eq_batch` remains NOT PROVED after this landing --
 * narrower in scope than the original FINDING hoped to close, but with
 * two more real, reusable, verified primitives and a sharper, tested
 * (not speculated) diagnosis of why the natural next attempt (a `forall`
 * over reachable positions) does not work, so the next session does not
 * re-spend a guard-depth-3 budget re-discovering this.
 * ============================================================================ *)

(* ============================================================================
 * WITNESS-STRUCTURE RESTART LEMMA (task #48, third landing, 2026-08-11):
 * the blank-lines-only restart, restated WITHOUT the `forall` hypothesis the
 * FINDING above diagnoses as the actual obstruction. Every fact about
 * `mid`'s line structure is supplied by the CALLER as an explicit per-line
 * witness record (three `nat` fields -- the same three positions
 * `parse_nquads_acc`'s own blank-line branch computes internally, named
 * `pos`/`pos1`/`pos2` there), chained into a `list blank_line_witness`. The
 * induction below is STRUCTURAL on that list (pattern-matching `[]` /
 * `w :: rest`, one cons cell per step) -- never a `forall` over positions.
 * This is the FIX the FINDING's own diagnosis names: every OTHER lemma in
 * this file and in `Parser.NTriples.Locality.fst` that verifies takes its
 * per-position facts as explicit parameters (`stop_pos`, `gt_pos`, ...),
 * never as a `forall`-quantified hypothesis with an opaque `match` in its
 * body; this section applies that same idiom one level up, at the
 * `parse_nquads_acc` recursion itself.
 *
 * SCOPE, one deliberate narrowing kept OUT of `blank_line_wf` for THIS
 * landing (documented, not silent): each witness requires `lw_wsend + 1 <
 * fs_byte_length mid`, i.e. the line's terminator byte is never the very
 * last byte of `mid`. This sidesteps `lemma_skip_eol_shift`'s CRLF-fusion
 * side condition (a bare CR ending `mid` exactly could fuse with an LF
 * starting `suffix`, which is not a real CRLF pair in `mid` alone) without
 * threading a `suffix`-dependent disjunction through every witness --
 * exactly the same category of scoped exclusion `lemma_nq_skip_line_shift`
 * itself already carries (`stop_pos < fs_byte_length mid`, excluding the
 * terminator landing at `mid`'s very last position). A chain whose FINAL
 * blank line's newline sits at `mid`'s last one or two bytes is outside
 * this witness structure's coverage; extending it (an extra `suffix`-aware
 * disjunct on the CHAIN's last entry only) is future work, not attempted
 * here per the guard-depth rule.
 * ============================================================================ *)

(* One line's classification. Only `LK_Blank` is populated by a proof this
   landing -- `LK_Comment` / `LK_QuadOk` / `LK_QuadFail` are declared so the
   type is extensible per the task's "extend kind by kind" plan, but no
   constructor here changes `blank_line_witness`'s shape; each kind gets its
   OWN witness record as it lands (comment needs a `stop_pos` matching
   `lemma_skip_comment_shift`'s own parameter; quad-failure needs `nq_skip_
   line`'s `stop_pos`, matching `lemma_nq_skip_line_shift_exact`; quad-
   success needs the parsed `(triple * option iri)` and end position). *)
type line_kind =
  | LK_Blank
  | LK_Comment
  | LK_QuadOk
  | LK_QuadFail

(* A single BLANK line's witness: `lw_pos` is the position `parse_nquads_acc`
   enters its loop at (before whitespace-skipping); `lw_wsend` is where `pws`
   lands (the byte `parse_nquads_acc` dispatches on); `lw_eolend` is where
   `skip_eol` lands after consuming the line terminator -- exactly the three
   positions `parse_nquads_acc`'s own blank-line branch computes internally.
   All three are explicit `nat` fields the CALLER supplies, never derived
   inside a proof from a `forall`. *)
noeq type blank_line_witness = {
  lw_pos    : nat;
  lw_wsend  : nat;
  lw_eolend : nat;
}

(* Well-formedness of ONE blank-line witness against a concrete string
   `mid`: `pws` actually lands where the witness claims; the landing byte is
   a line terminator (0x0A or 0x0D -- matching `parse_nquads_acc`'s OWN
   dispatch test, not just `is_nl`'s narrower 0x0A-only check); `skip_eol`
   actually lands where the witness claims; the line makes PROGRESS
   (`lw_eolend > lw_wsend`, matching `parse_nquads_acc`'s own `if pos2 =
   pos1 then ds` no-progress guard -- a witness for a no-progress "line"
   cannot arise from a real call, so this predicate excludes it
   structurally); and the SCOPE narrowing from this section's banner
   (`lw_wsend + 1 < fs_byte_length mid`). *)
let blank_line_wf (mid : string) (w : blank_line_witness) : Type0 =
  w.lw_pos <= w.lw_wsend /\
  w.lw_wsend + 1 < Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid w.lw_pos == Parser.Combinators.ParseOk () w.lw_wsend /\
  (let c = Parser.FastString.fs_byte_index mid w.lw_wsend in
   let cc = FStar.Char.int_of_char c in
   cc = 0x0A \/ cc = 0x0D) /\
  Parser.NTriples.skip_eol mid w.lw_wsend == w.lw_eolend /\
  w.lw_eolend > w.lw_wsend

(* Single-step shift: ONE blank line, embedded at `lw_pos` inside the
   three-way-split `prefix ^ (mid ^ suffix)`, advances `parse_nquads_acc`'s
   own recursion by exactly one step, landing at `lw_eolend` (shifted by
   `fs_byte_length prefix`, same as every other lemma in this file) with
   the SAME dataset and `fuel - 1`. Proof: apply `lemma_pws_shift` (already
   proved, `Parser.NTriples.Locality.fst`) to get the shifted `pws` landing,
   `lemma_byte_index_at_middle` (this file, PHASE 2 CHECKPOINT) for the
   dispatch byte, `lemma_skip_eol_shift` (already proved) for the shifted
   `skip_eol` landing -- then let Z3 chain those three flat `nat`/`char`
   equalities through ONE unfolding of `parse_nquads_acc`'s own defining
   equation, exactly the technique `parse_nquads_acc_concat_line_empty_
   complete`/`_empty_carry` above already use for a one-step unfold. *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_blank_step_shift
    (prefix mid suffix : string) (w : blank_line_witness)
    (ds : RDF.Graph.Executable.rdf_dataset) (fuel : nat)
  : Lemma
      (requires blank_line_wf mid w /\ fuel > 0)
      (ensures
        Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + w.lw_pos) ds fuel
        == Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + w.lw_eolend) ds (fuel - 1))
let lemma_parse_nquads_acc_blank_step_shift prefix mid suffix w ds fuel =
  Parser.FastString.Axioms.fs_byte_length_concat mid suffix;
  Parser.FastString.Axioms.fs_byte_length_concat prefix (mid ^ suffix);
  Parser.NTriples.Locality.lemma_pws_shift prefix mid suffix w.lw_pos w.lw_wsend;
  lemma_byte_index_at_middle prefix mid suffix w.lw_wsend;
  Parser.NTriples.Locality.lemma_skip_eol_shift prefix mid suffix w.lw_wsend
#pop-options

(* A CHAIN of blank-line witnesses: recursively defined (never a `forall`)
   so both ADJACENCY (one line's landing position is exactly the next
   line's starting position) and PER-ENTRY well-formedness unfold by
   pattern match, one cons cell at a time -- the same shape the induction
   below consumes. `blank_chain_end` computes where the chain leaves off
   (the position right after its last line's terminator), by the same
   structural recursion. *)
let rec blank_chain_wf (mid : string) (start_pos : nat) (ws : list blank_line_witness)
  : Tot Type0 (decreases ws) =
  match ws with
  | [] -> True
  | w :: rest -> w.lw_pos == start_pos /\ blank_line_wf mid w /\ blank_chain_wf mid w.lw_eolend rest

let rec blank_chain_end (start_pos : nat) (ws : list blank_line_witness)
  : Tot nat (decreases ws) =
  match ws with
  | [] -> start_pos
  | w :: rest -> blank_chain_end w.lw_eolend rest

(* The restart lemma itself, blank-lines-only sub-case: a whole CHAIN of
   blank lines, embedded inside `prefix ^ (mid ^ suffix)` starting at
   `start_pos`, is skipped by `parse_nquads_acc` in exactly `length ws`
   steps, dataset UNCHANGED, landing at `blank_chain_end start_pos ws`
   (shifted by `fs_byte_length prefix`) with `fuel - length ws` fuel
   remaining. Structural induction on `ws`, ONE `blank_line_witness` per
   step -- `lemma_parse_nquads_acc_blank_step_shift` supplies the single
   step, the recursive call supplies the rest, transitivity chains them.
   No `forall` anywhere in this lemma or its dependencies. *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_skip_blanks
    (prefix mid suffix : string) (ds : RDF.Graph.Executable.rdf_dataset)
    (start_pos : nat) (ws : list blank_line_witness) (fuel : nat)
  : Lemma
      (requires blank_chain_wf mid start_pos ws /\ fuel >= List.Tot.length ws)
      (ensures
        Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + start_pos) ds fuel
        == Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + blank_chain_end start_pos ws) ds
             (fuel - List.Tot.length ws))
      (decreases ws)
let rec lemma_parse_nquads_acc_skip_blanks prefix mid suffix ds start_pos ws fuel =
  match ws with
  | [] -> ()
  | w :: rest ->
    lemma_parse_nquads_acc_blank_step_shift prefix mid suffix w ds fuel;
    lemma_parse_nquads_acc_skip_blanks prefix mid suffix ds w.lw_eolend rest (fuel - 1)
#pop-options

(* ============================================================================
 * KIND 2 (task #48 ordered work list, "extend kind by kind"): COMMENT
 * lines. Same witness-parameter idiom as the blank-line kind above, one
 * layer deeper (`skip_comment` composes `nt_skip_to_eol` then `skip_eol`,
 * matching `parse_nquads_acc`'s own comment branch: `pos2 = skip_comment
 * input pos1; pos3 = skip_eol input pos2`). Reuses `lemma_skip_comment_
 * shift` (already proved, this file's PHASE-2-adjacent primitives above)
 * for the `nt_skip_to_eol` composition and `lemma_skip_eol_shift` (already
 * proved, `Parser.NTriples.Locality.fst`) for the trailing EOL skip -- no
 * new scanning argument, purely a `parse_nquads_acc`-level composition of
 * two already-closed primitives, same shape as the blank-line kind's
 * `lemma_parse_nquads_acc_blank_step_shift`.
 * ============================================================================ *)

(* A single COMMENT line's witness: `cw_pos` is `parse_nquads_acc`'s entry
   position; `cw_wsend` is where `pws` lands (the `#` byte); `cw_commentend`
   is where `skip_comment` lands (== `nt_skip_to_eol mid (fs_byte_length mid)
   (cw_wsend + 1) (fs_byte_length mid - cw_wsend)`, matching `lemma_skip_
   comment_shift`'s own `stop_pos` parameter); `cw_eolend` is where the
   trailing `skip_eol` lands. Same SCOPE narrowing as the blank-line kind
   (`cw_commentend + 1 < fs_byte_length mid`), for the same reason
   (sidesteps `lemma_skip_eol_shift`'s CRLF-fusion side condition without a
   `suffix`-dependent disjunct). *)
noeq type comment_line_witness = {
  cw_pos        : nat;
  cw_wsend      : nat;
  cw_commentend : nat;
  cw_eolend     : nat;
}

let comment_line_wf (mid : string) (w : comment_line_witness) : Type0 =
  w.cw_pos <= w.cw_wsend /\
  w.cw_wsend < Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid w.cw_pos == Parser.Combinators.ParseOk () w.cw_wsend /\
  FStar.Char.int_of_char (Parser.FastString.fs_byte_index mid w.cw_wsend) = 0x23 /\
  Parser.NTriples.nt_skip_to_eol mid (Parser.FastString.fs_byte_length mid) (w.cw_wsend + 1)
    (Parser.FastString.fs_byte_length mid - w.cw_wsend) == w.cw_commentend /\
  w.cw_commentend < Parser.FastString.fs_byte_length mid /\
  w.cw_commentend + 1 < Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.skip_eol mid w.cw_commentend == w.cw_eolend /\
  w.cw_eolend > w.cw_wsend

(* Single-step shift, comment-line kind: same shape as `lemma_parse_
   nquads_acc_blank_step_shift`, composing `lemma_skip_comment_shift`
   (this file) and `lemma_skip_eol_shift` (`Parser.NTriples.Locality.fst`)
   instead of `lemma_pws_shift` + `lemma_skip_eol_shift` directly -- one
   extra scanner layer, same one-step-unfold technique. *)
#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_comment_step_shift
    (prefix mid suffix : string) (w : comment_line_witness)
    (ds : RDF.Graph.Executable.rdf_dataset) (fuel : nat)
  : Lemma
      (requires comment_line_wf mid w /\ fuel > 0)
      (ensures
        Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + w.cw_pos) ds fuel
        == Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + w.cw_eolend) ds (fuel - 1))
let lemma_parse_nquads_acc_comment_step_shift prefix mid suffix w ds fuel =
  Parser.FastString.Axioms.fs_byte_length_concat mid suffix;
  Parser.FastString.Axioms.fs_byte_length_concat prefix (mid ^ suffix);
  Parser.NTriples.Locality.lemma_pws_shift prefix mid suffix w.cw_pos w.cw_wsend;
  lemma_byte_index_at_middle prefix mid suffix w.cw_wsend;
  lemma_skip_comment_shift prefix mid suffix w.cw_wsend w.cw_commentend;
  Parser.NTriples.Locality.lemma_skip_eol_shift prefix mid suffix w.cw_commentend
#pop-options

(* ============================================================================
 * KIND 3 (task #48 ordered work list, "extend kind by kind"): QUAD-FAILURE
 * lines -- a line that is neither blank nor a comment, but on which
 * `Parser.NQuads.parse_nquad` fails (malformed subject/predicate/object/
 * graph-label/terminator), so `parse_nquads_acc`'s error-recovery branch
 * (`nq_skip_line`) fires. Reuses `lemma_nq_skip_line_shift_exact` (already
 * proved, this file's Kind-1-adjacent primitives above).
 *
 * WHAT IS A PREMISE HERE, DELIBERATELY (matching the task brief's own
 * "conditioned... premise" acceptable-landing form, stated plainly, not
 * hidden): unlike the blank/comment kinds -- where EVERY fact the step-
 * shift lemma needs is derivable purely from `mid`'s own bytes via already-
 * proved scanner-shift lemmas -- showing that `parse_nquad`, having FAILED
 * on `mid` alone, ALSO fails when `mid` is embedded inside a larger string
 * is exactly the unresolved forward-dispatch obstruction the FINDING above
 * (and `Parser.NTriples.Locality.fst`'s own abandoned `parse_iri_raw`
 * capstone) diagnoses for the SUCCESS case, and failure is no easier: a
 * recursive-descent parser can fail for reasons (running off the end of
 * `mid`, an internal scan landing past `mid`'s boundary) that do NOT
 * reproduce when more bytes follow. This kind's step-shift lemma therefore
 * takes "`parse_nquad` also fails on the embedding, at the shifted
 * position" as an EXPLICIT HYPOTHESIS (`ParseFail?` on both sides) rather
 * than deriving it -- a witness fact the CALLER must already possess (e.g.
 * from having run the concrete embedded parse), never invented internally,
 * consistent with every other witness parameter in this file. *)
noeq type quad_fail_witness = {
  qfw_pos     : nat;
  qfw_wsend   : nat;
  qfw_stopeol : nat;
}

let quad_fail_line_wf (mid : string) (w : quad_fail_witness) : Type0 =
  w.qfw_pos <= w.qfw_wsend /\
  w.qfw_wsend < Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid w.qfw_pos == Parser.Combinators.ParseOk () w.qfw_wsend /\
  (let c = Parser.FastString.fs_byte_index mid w.qfw_wsend in
   let cc = FStar.Char.int_of_char c in
   cc <> 0x23 /\ cc <> 0x0A /\ cc <> 0x0D) /\
  Parser.Combinators.ParseFail? (Parser.NQuads.parse_nquad mid w.qfw_wsend) /\
  Parser.NQuads.nq_skip_line mid (Parser.FastString.fs_byte_length mid) w.qfw_wsend
    (Parser.FastString.fs_byte_length mid - w.qfw_wsend) == w.qfw_stopeol /\
  w.qfw_stopeol < Parser.FastString.fs_byte_length mid /\
  w.qfw_stopeol > w.qfw_wsend

#push-options "--z3rlimit 150 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_quad_fail_step_shift
    (prefix mid suffix : string) (w : quad_fail_witness)
    (ds : RDF.Graph.Executable.rdf_dataset) (fuel : nat)
  : Lemma
      (requires
        quad_fail_line_wf mid w /\
        fuel > 0 /\
        (Parser.FastString.fs_byte_length suffix = 0 \/
         Parser.FastString.fs_byte_at suffix 0 <> 0x0A) /\
        Parser.Combinators.ParseFail?
          (Parser.NQuads.parse_nquad (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + w.qfw_wsend)))
      (ensures
        Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + w.qfw_pos) ds fuel
        == Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + w.qfw_stopeol) ds (fuel - 1))
let lemma_parse_nquads_acc_quad_fail_step_shift prefix mid suffix w ds fuel =
  Parser.FastString.Axioms.fs_byte_length_concat mid suffix;
  Parser.FastString.Axioms.fs_byte_length_concat prefix (mid ^ suffix);
  Parser.NTriples.Locality.lemma_pws_shift prefix mid suffix w.qfw_pos w.qfw_wsend;
  lemma_byte_index_at_middle prefix mid suffix w.qfw_wsend;
  lemma_nq_skip_line_shift_exact prefix mid suffix w.qfw_wsend w.qfw_stopeol
#pop-options

(* ============================================================================
 * KIND 4 (task #48 ordered work list, "extend kind by kind"): QUAD-SUCCESS
 * lines -- a line on which `Parser.NQuads.parse_nquad` SUCCEEDS. Composes
 * `lemma_parse_nquad_shift_generic` (already proved, `Parser.NTriples.
 * Locality.fst`, Stage 3 Item 3) exactly as the task named it.
 *
 * WHAT IS A PREMISE HERE, DELIBERATELY (same disclosure as Kind 3): `lemma_
 * parse_nquad_shift_generic` ITSELF takes the embedded (full-string)
 * success facts for `parse_subject`/`parse_iri`/`parse_object`/`parse_opt_
 * graph_label` as EXTERNAL hypotheses, not derived internally -- it
 * composes per-shape sub-lemmas (IRI/bnode/literal shift lemmas) that live
 * in `Parser.NTriples.Locality.fst`, chosen by the CALLER based on the
 * line's concrete subject/object shape (exactly the "witness/premise-
 * supplied" acceptable-landing form, one layer down). This step-shift
 * lemma inherits that same shape: the four embedded sub-parse equalities
 * are its own explicit `requires`, supplied by whichever caller already
 * discharged them via the appropriate per-shape lemma for THIS concrete
 * line -- never re-derived here.
 *
 * SCOPE narrowing for the TRAILING (post-quad) segment, kept deliberately
 * simple for this landing: no comment immediately follows the quad's `.`
 * (`fs_byte_index mid qow_wsend2 <> 0x23`) -- `skip_comment`'s `else pos`
 * branch then fires UNCONDITIONALLY (no `lemma_skip_comment_shift` call
 * needed, unlike the comment kind above), so only the trailing `skip_eol`
 * needs a shift lemma. A witness whose quad line IS followed by a trailing
 * `# ...` comment is outside this lemma's coverage; extending it is a
 * direct composition with `lemma_skip_comment_shift` (Kind 2's own
 * primitive), not attempted here per the guard-depth rule. *)
noeq type quad_ok_witness = {
  qow_entry   : nat;
  qow_subj    : RDF.Term.subject;
  qow_pos2    : nat;
  qow_pos3    : nat;
  qow_pred    : RDF.Term.wf_iri;
  qow_pos4    : nat;
  qow_pos5    : nat;
  qow_obj     : RDF.Term.rdf_term;
  qow_pos6    : nat;
  qow_graph   : option RDF.Term.iri;
  qow_pos7    : nat;
  qow_pos8    : nat;
  qow_wsend2  : nat;
  qow_eolend2 : nat;
}

let quad_ok_line_wf (mid : string) (w : quad_ok_witness) : Type0 =
  w.qow_entry <= Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid w.qow_entry == Parser.Combinators.ParseOk () w.qow_entry /\
  Parser.NTriples.parse_subject mid w.qow_entry == Parser.Combinators.ParseOk w.qow_subj w.qow_pos2 /\
  w.qow_pos2 <= Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid w.qow_pos2 == Parser.Combinators.ParseOk () w.qow_pos3 /\
  Parser.NTriples.parse_iri mid w.qow_pos3 == Parser.Combinators.ParseOk w.qow_pred w.qow_pos4 /\
  w.qow_pos4 <= Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid w.qow_pos4 == Parser.Combinators.ParseOk () w.qow_pos5 /\
  Parser.NTriples.parse_object mid w.qow_pos5 == Parser.Combinators.ParseOk w.qow_obj w.qow_pos6 /\
  w.qow_pos6 <= Parser.FastString.fs_byte_length mid /\
  Parser.NQuads.parse_opt_graph_label mid w.qow_pos6 == Parser.Combinators.ParseOk w.qow_graph w.qow_pos7 /\
  w.qow_pos7 <= Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid w.qow_pos7 == Parser.Combinators.ParseOk () w.qow_pos8 /\
  w.qow_pos8 < Parser.FastString.fs_byte_length mid /\
  FStar.Char.int_of_char (Parser.FastString.fs_byte_index mid w.qow_pos8) = 0x2E /\
  RDF.Term.is_iri w.qow_pred /\
  w.qow_pos8 + 1 <= Parser.FastString.fs_byte_length mid /\
  Parser.NTriples.pws mid (w.qow_pos8 + 1) == Parser.Combinators.ParseOk () w.qow_wsend2 /\
  w.qow_wsend2 < Parser.FastString.fs_byte_length mid /\
  w.qow_wsend2 + 1 < Parser.FastString.fs_byte_length mid /\
  FStar.Char.int_of_char (Parser.FastString.fs_byte_index mid w.qow_wsend2) <> 0x23 /\
  Parser.NTriples.skip_eol mid w.qow_wsend2 == w.qow_eolend2

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_quad_ok_step_shift
    (prefix mid suffix : string) (w : quad_ok_witness)
    (ds : RDF.Graph.Executable.rdf_dataset) (fuel : nat)
  : Lemma
      (requires
        quad_ok_line_wf mid w /\
        fuel > 0 /\
        Parser.NTriples.parse_subject (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + w.qow_entry)
          == Parser.Combinators.ParseOk w.qow_subj (Parser.FastString.fs_byte_length prefix + w.qow_pos2) /\
        Parser.NTriples.parse_iri (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + w.qow_pos3)
          == Parser.Combinators.ParseOk w.qow_pred (Parser.FastString.fs_byte_length prefix + w.qow_pos4) /\
        Parser.NTriples.parse_object (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + w.qow_pos5)
          == Parser.Combinators.ParseOk w.qow_obj (Parser.FastString.fs_byte_length prefix + w.qow_pos6) /\
        Parser.NQuads.parse_opt_graph_label (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + w.qow_pos6)
          == Parser.Combinators.ParseOk w.qow_graph (Parser.FastString.fs_byte_length prefix + w.qow_pos7))
      (ensures
        (match Parser.NQuads.parse_nquad mid w.qow_entry with
         | Parser.Combinators.ParseOk (t, g) _ ->
           Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + w.qow_entry) ds fuel
           == Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
                (Parser.FastString.fs_byte_length prefix +
                  (if w.qow_eolend2 > w.qow_entry then w.qow_eolend2
                   else if w.qow_wsend2 > w.qow_entry then w.qow_wsend2
                   else w.qow_pos8 + 1))
                (Parser.NQuads.dataset_add_quad ds t g) (fuel - 1)
         | _ -> False))
let lemma_parse_nquads_acc_quad_ok_step_shift prefix mid suffix w ds fuel =
  Parser.FastString.Axioms.fs_byte_length_concat mid suffix;
  Parser.FastString.Axioms.fs_byte_length_concat prefix (mid ^ suffix);
  Parser.NTriples.Locality.lemma_parse_nquad_shift_generic prefix mid suffix
    w.qow_entry w.qow_entry w.qow_subj w.qow_pos2 w.qow_pos3 w.qow_pred w.qow_pos4
    w.qow_pos5 w.qow_obj w.qow_pos6 w.qow_graph w.qow_pos7 w.qow_pos8;
  lemma_byte_index_at_middle prefix mid suffix w.qow_pos8;
  Parser.NTriples.Locality.lemma_pws_shift prefix mid suffix (w.qow_pos8 + 1) w.qow_wsend2;
  lemma_byte_index_at_middle prefix mid suffix w.qow_wsend2;
  Parser.NTriples.Locality.lemma_skip_eol_shift prefix mid suffix w.qow_wsend2
#pop-options

(* ============================================================================
 * `lemma_parse_nquads_acc_restart` (task #48 ordered work list item 5/6,
 * the FINDING's own named target) -- the CONDITIONED realisation the task
 * brief's own failure branch sanctions ("premise: every complete line
 * parses successfully / boolean/witness-supplied premise is an ACCEPTABLE
 * landing"). Generalises the blank-only chain (`lemma_parse_nquads_acc_
 * skip_blanks` above) to a MIXED-KIND chain: `line_witness` is a sum of
 * all four per-line witness types (Kinds 1-4 above), one constructor per
 * kind, so a single `list line_witness` can describe an ARBITRARY
 * multi-line region -- blank lines, comments, failing lines, and
 * successful quads in any order -- with the SAME structural-induction
 * discipline (never a `forall`) as every lemma in this file. The `ds`
 * transform per line (`lw_ds_step`) is `dataset_add_quad` for a quad-
 * success line, identity for the other three kinds -- matching `parse_
 * nquads_acc`'s own four branches exactly.
 * ============================================================================ *)

noeq type line_witness =
  | LW_Blank    : blank_line_witness -> line_witness
  | LW_Comment  : comment_line_witness -> line_witness
  | LW_QuadFail : quad_fail_witness -> line_witness
  | LW_QuadOk   : quad_ok_witness -> line_witness

(* Entry position: where `parse_nquads_acc` must be called for this line to
   be the NEXT line processed. *)
let lw_pos (w : line_witness) : nat =
  match w with
  | LW_Blank b -> b.lw_pos
  | LW_Comment c -> c.cw_pos
  | LW_QuadFail f -> f.qfw_pos
  | LW_QuadOk q -> q.qow_entry

(* Landing position after this ONE line is fully processed -- exactly what
   each kind's own step-shift lemma proves `parse_nquads_acc` advances to. *)
let lw_end (w : line_witness) : nat =
  match w with
  | LW_Blank b -> b.lw_eolend
  | LW_Comment c -> c.cw_eolend
  | LW_QuadFail f -> f.qfw_stopeol
  | LW_QuadOk q ->
    (if q.qow_eolend2 > q.qow_entry then q.qow_eolend2
     else if q.qow_wsend2 > q.qow_entry then q.qow_wsend2
     else q.qow_pos8 + 1)

(* Per-line well-formedness against the FIXED three-way split `prefix ^
   (mid ^ suffix)` -- the blank/comment kinds only need `mid`-local facts
   (their own `_line_wf` predicates); the quad-fail/quad-ok kinds ALSO need
   their disclosed embedding premises (Kind 3/4's own banners), stated here
   at THIS line's own local position within the SHARED `mid` (no separate
   prefix per chain entry is needed -- every line in the chain embeds into
   the SAME fixed `prefix`/`suffix`, only its own position within `mid`
   differs, exactly as `lemma_parse_nquads_acc_skip_blanks` already
   established for the blank-only case). *)
let lw_wf (prefix mid suffix : string) (w : line_witness) : Type0 =
  match w with
  | LW_Blank b -> blank_line_wf mid b
  | LW_Comment c -> comment_line_wf mid c
  | LW_QuadFail f ->
    quad_fail_line_wf mid f /\
    (Parser.FastString.fs_byte_length suffix = 0 \/
     Parser.FastString.fs_byte_at suffix 0 <> 0x0A) /\
    Parser.Combinators.ParseFail?
      (Parser.NQuads.parse_nquad (prefix ^ (mid ^ suffix))
         (Parser.FastString.fs_byte_length prefix + f.qfw_wsend))
  | LW_QuadOk q ->
    quad_ok_line_wf mid q /\
    Parser.NTriples.parse_subject (prefix ^ (mid ^ suffix))
      (Parser.FastString.fs_byte_length prefix + q.qow_entry)
      == Parser.Combinators.ParseOk q.qow_subj (Parser.FastString.fs_byte_length prefix + q.qow_pos2) /\
    Parser.NTriples.parse_iri (prefix ^ (mid ^ suffix))
      (Parser.FastString.fs_byte_length prefix + q.qow_pos3)
      == Parser.Combinators.ParseOk q.qow_pred (Parser.FastString.fs_byte_length prefix + q.qow_pos4) /\
    Parser.NTriples.parse_object (prefix ^ (mid ^ suffix))
      (Parser.FastString.fs_byte_length prefix + q.qow_pos5)
      == Parser.Combinators.ParseOk q.qow_obj (Parser.FastString.fs_byte_length prefix + q.qow_pos6) /\
    Parser.NQuads.parse_opt_graph_label (prefix ^ (mid ^ suffix))
      (Parser.FastString.fs_byte_length prefix + q.qow_pos6)
      == Parser.Combinators.ParseOk q.qow_graph (Parser.FastString.fs_byte_length prefix + q.qow_pos7)

(* What this ONE line does to the dataset: `dataset_add_quad` for a
   quad-success line (using `mid`'s OWN `parse_nquad` result, matching
   `lemma_parse_nquads_acc_quad_ok_step_shift`'s ensures exactly), identity
   for the other three kinds -- matching `parse_nquads_acc`'s own four
   branches (only the `ParseOk (t,graph_opt) pos2` branch calls `dataset_
   add_quad`). *)
let lw_ds_step (mid : string) (w : line_witness) (ds : RDF.Graph.Executable.rdf_dataset)
  : RDF.Graph.Executable.rdf_dataset =
  match w with
  | LW_Blank _ -> ds
  | LW_Comment _ -> ds
  | LW_QuadFail _ -> ds
  | LW_QuadOk q ->
    (match Parser.NQuads.parse_nquad mid q.qow_entry with
     | Parser.Combinators.ParseOk (t, g) _ -> Parser.NQuads.dataset_add_quad ds t g
     | _ -> ds)

(* Single-step shift, ANY kind: dispatches to the matching per-kind lemma
   proved above. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_line_step_shift
    (prefix mid suffix : string) (w : line_witness)
    (ds : RDF.Graph.Executable.rdf_dataset) (fuel : nat)
  : Lemma
      (requires lw_wf prefix mid suffix w /\ fuel > 0)
      (ensures
        Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + lw_pos w) ds fuel
        == Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + lw_end w) (lw_ds_step mid w ds) (fuel - 1))
let lemma_parse_nquads_acc_line_step_shift prefix mid suffix w ds fuel =
  match w with
  | LW_Blank b -> lemma_parse_nquads_acc_blank_step_shift prefix mid suffix b ds fuel
  | LW_Comment c -> lemma_parse_nquads_acc_comment_step_shift prefix mid suffix c ds fuel
  | LW_QuadFail f -> lemma_parse_nquads_acc_quad_fail_step_shift prefix mid suffix f ds fuel
  | LW_QuadOk q -> lemma_parse_nquads_acc_quad_ok_step_shift prefix mid suffix q ds fuel
#pop-options

(* A CHAIN of mixed-kind line witnesses -- same recursive (never `forall`)
   shape as `blank_chain_wf`/`blank_chain_end` above, generalised to
   `line_witness`. *)
let rec chain_wf (prefix mid suffix : string) (start_pos : nat) (ws : list line_witness)
  : Tot Type0 (decreases ws) =
  match ws with
  | [] -> True
  | w :: rest -> lw_pos w == start_pos /\ lw_wf prefix mid suffix w /\ chain_wf prefix mid suffix (lw_end w) rest

let rec chain_end (start_pos : nat) (ws : list line_witness) : Tot nat (decreases ws) =
  match ws with
  | [] -> start_pos
  | w :: rest -> chain_end (lw_end w) rest

let rec chain_ds_fold (mid : string) (ws : list line_witness) (ds : RDF.Graph.Executable.rdf_dataset)
  : Tot RDF.Graph.Executable.rdf_dataset (decreases ws) =
  match ws with
  | [] -> ds
  | w :: rest -> chain_ds_fold mid rest (lw_ds_step mid w ds)

(* THE restart lemma: a whole mixed-kind CHAIN, embedded inside `prefix ^
   (mid ^ suffix)` starting at `start_pos`, is processed by `parse_nquads_
   acc` in exactly `length ws` steps, landing at `chain_end start_pos ws`
   (shifted) with dataset `chain_ds_fold mid ws ds` and `fuel - length ws`
   remaining. Structural induction on `ws`, ONE `line_witness` per step,
   composing `lemma_parse_nquads_acc_line_step_shift`. This is the
   FINDING's own named target, `lemma_parse_nquads_acc_restart`, in the
   CONDITIONED (witness-supplied) form the task brief's own failure branch
   accepts as a legitimate final landing -- not the FINDING's originally-
   envisioned UNCONDITIONAL two-string signature, which still needs the
   full per-combinator forward-dispatch capstone diagnosed as not fitting
   a guard-depth-3 budget. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_restart
    (prefix mid suffix : string) (ds : RDF.Graph.Executable.rdf_dataset)
    (start_pos : nat) (ws : list line_witness) (fuel : nat)
  : Lemma
      (requires chain_wf prefix mid suffix start_pos ws /\ fuel >= List.Tot.length ws)
      (ensures
        Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
          (Parser.FastString.fs_byte_length prefix + start_pos) ds fuel
        == Parser.NQuads.parse_nquads_acc (prefix ^ (mid ^ suffix))
             (Parser.FastString.fs_byte_length prefix + chain_end start_pos ws)
             (chain_ds_fold mid ws ds) (fuel - List.Tot.length ws))
      (decreases ws)
let rec lemma_parse_nquads_acc_restart prefix mid suffix ds start_pos ws fuel =
  match ws with
  | [] -> ()
  | w :: rest ->
    lemma_parse_nquads_acc_line_step_shift prefix mid suffix w ds fuel;
    lemma_parse_nquads_acc_restart prefix mid suffix (lw_ds_step mid w ds) (lw_end w) rest (fuel - 1)
#pop-options

(* A STANDALONE (non-embedded) corollary: running `parse_nquads_acc` on
   `mid` alone, from position 0 with `mid`'s own `fs_byte_length mid + 1`
   fuel (exactly the fuel `Parser.NQuads.parse_nquads`/`batch_parse`/
   `feed_chunk`/`finish` all use for a self-contained string -- the FUEL
   NOTE in this module's own banner), equals `chain_ds_fold mid ws ds`
   whenever `ws` is a chain that covers ALL of `mid` (`chain_end 0 ws ==
   fs_byte_length mid`). Instantiates `lemma_parse_nquads_acc_restart` at
   `prefix = suffix = ""` (so the embedding IS `mid` itself) and rewrites
   `"" ^ (mid ^ "")` down to `mid` via the already-proved `empty_string_
   concat_left`/`_right` -- a single TOP-LEVEL argument rewrite of `parse_
   nquads_acc`'s own first parameter, the same shallow congruence pattern
   `parse_nquads_acc_concat_line_empty_complete`/`_empty_carry` above
   already use successfully (NOT the deep, three-function-layer congruence
   propagation that stalled the FINDING's three earlier attempts -- those
   needed `mid ^ ""` rewritten INSIDE `pws`/`skip_eol`'s own preconditions
   several call-layers deep; this rewrite is one function argument, at the
   top). Once landed at `pos = chain_end 0 ws = fs_byte_length mid`,
   `parse_nquads_acc`'s own `pos >= len` base case returns the accumulated
   dataset UNCHANGED regardless of remaining fuel -- so no fuel-
   monotonicity argument is needed here either. *)
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_full_via_chain
    (mid : string) (ds : RDF.Graph.Executable.rdf_dataset) (ws : list line_witness)
  : Lemma
      (requires
        chain_wf "" mid "" 0 ws /\
        chain_end 0 ws == Parser.FastString.fs_byte_length mid /\
        Parser.FastString.fs_byte_length mid + 1 >= List.Tot.length ws)
      (ensures
        Parser.NQuads.parse_nquads_acc mid 0 ds (Parser.FastString.fs_byte_length mid + 1)
        == chain_ds_fold mid ws ds)
let lemma_parse_nquads_acc_full_via_chain mid ds ws =
  empty_string_concat_left (mid ^ "");
  empty_string_concat_right mid;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  lemma_parse_nquads_acc_restart "" mid "" ds 0 ws (Parser.FastString.fs_byte_length mid + 1)
#pop-options

(* ============================================================================
 * `parse_nquads_acc_concat_line`, GENERAL (INTERIOR) CASE -- the piece the
 * ORIGINAL FINDING (module banner, "WHAT IT NEEDS") named as the whole
 * streaming design's fundamental split/monoid law, and diagnosed as
 * needing a per-combinator forward-dispatch capstone. It does NOT, once
 * both halves are each covered by a witness chain: it is FOUR applications
 * of machinery already proved above (`lemma_parse_nquads_acc_full_via_
 * chain` twice, `lemma_parse_nquads_acc_restart` twice), chained by
 * ORDINARY transitivity -- no new induction, no new scanning argument.
 *
 * THE KEY REALISATION that makes this land without a fuel-monotonicity
 * lemma (which the ORIGINAL FINDING flagged as a separate, if "short
 * mechanical," piece still needed): `lemma_parse_nquads_acc_restart`'s own
 * `requires` only demands fuel be SUFFICIENT (`fuel >= List.Tot.length
 * ws`), and once its landing position reaches `>= fs_byte_length mid`,
 * `parse_nquads_acc`'s `pos >= len` base case returns the accumulated
 * dataset UNCHANGED regardless of exactly how much fuel is left over.  So
 * running `carry`'s chain with WHATEVER fuel remains after `complete`'s
 * chain finishes (generally MORE than `carry`'s own canonical `fs_byte_
 * length carry + 1`, since a chain step consumes far fewer FUEL units
 * than the BYTES its line spans) lands on the exact SAME dataset value
 * as running `carry`'s chain with its own canonical fuel -- both are
 * "sufficient fuel," and sufficiency is all either call needs. No separate
 * monotonicity induction is required; the two calls just need their own
 * independent sufficiency facts checked, then their RESULTS (not their
 * fuel bookkeeping) are equated via ordinary transitivity.
 * ============================================================================ *)
#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val lemma_parse_nquads_acc_concat_line_general
    (complete carry : string) (ds : RDF.Graph.Executable.rdf_dataset)
    (ws_complete ws_carry : list line_witness)
  : Lemma
      (requires
        (* `ws_complete` must be well-formed BOTH standalone (needed to
           relate the goal's LHS, a bare `parse_nquads_acc complete 0 ds
           ...` call, to the chain -- `lemma_parse_nquads_acc_full_via_
           chain`'s own `chain_wf "" complete "" 0 ws` requires exactly the
           EMPTY-suffix form) AND embedded ahead of `carry` (needed for
           `lemma_parse_nquads_acc_restart`'s `chain_wf "" complete carry 0
           ws` on the goal's RHS). These are GENUINELY two different facts
           whenever `ws_complete` contains a quad-fail/quad-ok entry (their
           `ParseFail?`/embedded-success premises are about a DIFFERENT
           string, `complete` alone vs. `complete ^ carry` -- a quad that
           runs out of bytes mid-parse with nothing following could well
           behave differently once more bytes follow), so both are
           required explicitly rather than assumed interchangeable -- for
           an `ws_complete` built entirely from blank/comment entries
           (`lw_wf` for those two kinds never mentions `suffix`) the two
           hypotheses coincide and this is no extra burden. *)
        chain_wf "" complete "" 0 ws_complete /\
        chain_wf "" complete carry 0 ws_complete /\
        chain_end 0 ws_complete == Parser.FastString.fs_byte_length complete /\
        (* Same double-hypothesis reasoning for `ws_carry`: standalone
           (`lemma_parse_nquads_acc_full_via_chain`'s own requires) AND
           embedded after `complete` (`lemma_parse_nquads_acc_restart`'s
           requires on the goal's RHS second half) are two different facts
           whenever `ws_carry` contains a quad-fail/quad-ok entry. *)
        chain_wf "" carry "" 0 ws_carry /\
        chain_wf complete carry "" 0 ws_carry /\
        chain_end 0 ws_carry == Parser.FastString.fs_byte_length carry /\
        Parser.FastString.fs_byte_length complete + 1 >= List.Tot.length ws_complete /\
        Parser.FastString.fs_byte_length carry + 1 >= List.Tot.length ws_carry /\
        Parser.FastString.fs_byte_length complete + Parser.FastString.fs_byte_length carry + 1
          >= List.Tot.length ws_complete + List.Tot.length ws_carry)
      (ensures
        Parser.NQuads.parse_nquads_acc carry 0
          (Parser.NQuads.parse_nquads_acc complete 0 ds (Parser.FastString.fs_byte_length complete + 1))
          (Parser.FastString.fs_byte_length carry + 1)
        == Parser.NQuads.parse_nquads_acc (complete ^ carry) 0 ds
             (Parser.FastString.fs_byte_length (complete ^ carry) + 1))
let lemma_parse_nquads_acc_concat_line_general complete carry ds ws_complete ws_carry =
  Parser.FastString.Axioms.fs_byte_length_concat complete carry;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  let fuel3 = Parser.FastString.fs_byte_length complete + Parser.FastString.fs_byte_length carry + 1 in
  (* Path 1: standalone `complete` then standalone `carry` -- LHS of goal. *)
  lemma_parse_nquads_acc_full_via_chain complete ds ws_complete;
  let ds1 = chain_ds_fold complete ws_complete ds in
  lemma_parse_nquads_acc_full_via_chain carry ds1 ws_carry;
  (* Path 2: `complete ^ carry` processed in one call -- RHS of goal, split
     via two embedded `lemma_parse_nquads_acc_restart` calls (`complete`'s
     own chain first, landing exactly at `fs_byte_length complete` with
     `ds1` and `fuel3 - length ws_complete` fuel remaining -- sufficient
     for `carry`'s own chain by this lemma's third hypothesis -- then
     `carry`'s chain from there, landing at `fs_byte_length (complete ^
     carry)` with `chain_ds_fold carry ws_carry ds1`, i.e. the SAME dataset
     Path 1 reached). *)
  empty_string_concat_left (complete ^ carry);
  lemma_parse_nquads_acc_restart "" complete carry ds 0 ws_complete fuel3;
  empty_string_concat_right carry;
  lemma_parse_nquads_acc_restart complete carry "" ds1 0 ws_carry
    (fuel3 - List.Tot.length ws_complete)
#pop-options

(* ============================================================================
 * `theorem_stream_eq_batch`, SINGLE CHUNK, GENERAL (task #48 item 5,
 * beyond the two boundary cases proved earlier in this file): `stream_
 * parse [c] == batch_parse c` for ANY `c`, given witness chains covering
 * `split_complete_lines c`'s two halves. Direct composition of `stream_
 * parse_single_chunk_shape` (definitional rewrite, proved earlier),
 * `lemma_parse_nquads_acc_concat_line_general` (this landing -- already
 * subsumes the two boundary cases for free: passing `ws_complete = []` or
 * `ws_carry = []` makes `chain_wf`/`chain_end` hold vacuously for an empty
 * string, so this ONE lemma covers "no newline"/"ends in newline"/
 * "interior" uniformly, no case split needed here), and `split_complete_
 * lines_reconstruct` (`complete ^ carry == c`, proved in this file's
 * FIRST landing) -- three already-proved facts chained by transitivity,
 * plus the same shallow top-level `^`-argument rewrite technique used
 * throughout this section (`complete ^ carry` down to `c`, ordinary `^`
 * congruence -- not the `string_of_list`-specific non-congruence the
 * module banner's FINDING documents). *)
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val theorem_stream_eq_batch_single_chunk_general
    (c : string) (ws_complete ws_carry : list line_witness)
  : Lemma
      (requires
        (let (complete, carry) = split_complete_lines c in
         chain_wf "" complete "" 0 ws_complete /\
         chain_wf "" complete carry 0 ws_complete /\
         chain_end 0 ws_complete == Parser.FastString.fs_byte_length complete /\
         chain_wf "" carry "" 0 ws_carry /\
         chain_wf complete carry "" 0 ws_carry /\
         chain_end 0 ws_carry == Parser.FastString.fs_byte_length carry /\
         Parser.FastString.fs_byte_length complete + 1 >= List.Tot.length ws_complete /\
         Parser.FastString.fs_byte_length carry + 1 >= List.Tot.length ws_carry /\
         Parser.FastString.fs_byte_length complete + Parser.FastString.fs_byte_length carry + 1
           >= List.Tot.length ws_complete + List.Tot.length ws_carry))
      (ensures stream_parse [c] == batch_parse c)
let theorem_stream_eq_batch_single_chunk_general c ws_complete ws_carry =
  stream_parse_single_chunk_shape c;
  let (complete, carry) = split_complete_lines c in
  lemma_parse_nquads_acc_concat_line_general complete carry RDF.Graph.Executable.empty_dataset
    ws_complete ws_carry;
  split_complete_lines_reconstruct c
#pop-options

(* ============================================================================
 * FINDING (guard-depth-3 stop, THIRD landing, 2026-08-11): `theorem_
 * stream_eq_batch`, the FULL multi-chunk statement (`stream_parse chunks
 * == batch_parse (concat_all chunks)` for an ARBITRARY `list string`), is
 * NOT proved in this landing. Not attempted directly -- diagnosed up
 * front, per the guard-depth discipline, as needing one further concrete
 * piece beyond everything landed above, not a re-run of any wall already
 * hit.
 *
 * WHAT THIS LANDING DID CLOSE, so the next session does not re-derive it:
 * every piece the FULL theorem's own induction would consume is now
 * proved and available --
 *   - `lemma_parse_nquads_acc_restart` (mixed-kind witness chain,
 *     CONDITIONED form of the FINDING's original named target);
 *   - `lemma_parse_nquads_acc_concat_line_general` (the split/monoid law,
 *     for an ARBITRARY interior split, conditioned on witness chains for
 *     BOTH halves, in BOTH standalone and embedded form);
 *   - `theorem_stream_eq_batch_single_chunk_general` (`stream_parse [c]
 *     == batch_parse c` for ANY `c`, not just the two boundary shapes).
 *
 * WHAT THE FULL THEOREM STILL NEEDS, named precisely (not "harder
 * induction" -- the SPECIFIC missing piece): an induction over `stream_
 * parse_acc`'s own fold (`chunks : list string`), carrying the INVARIANT
 * "the batch parse of every chunk consumed so far equals the streaming
 * state reached so far" --
 *
 *   parse_nquads_acc (concat_all chunks_so_far) 0 empty_dataset
 *     (fs_byte_length (concat_all chunks_so_far) + 1)
 *   == parse_nquads_acc st.carry 0 ds (fs_byte_length st.carry + 1)
 *
 * The INDUCTIVE STEP (folding in one more chunk `c`) needs `lemma_parse_
 * nquads_acc_concat_line_general (concat_all chunks_so_far) c ds ws1 ws2`
 * -- ALREADY PROVED, callable as-is -- but callable only GIVEN witness
 * chains `ws1`/`ws2` for THAT split. `concat_all chunks_so_far` grows with
 * every step and is NOT, in general, `split_complete_lines`-aligned (it is
 * "every complete line processed so far" PLUS the still-pending `st.
 * carry`, per the streaming invariant `split_complete_lines_extend_carry`/
 * `_ends_in_newline` already establish) -- so the missing piece is NOT a
 * new scanning/embedding argument (everything the induction's BODY needs
 * already exists), it is CHAIN BOOKKEEPING across the fold: the induction
 * must carry witness chains AS PART OF ITS OWN INVARIANT (extending it
 * from a bare dataset-equality to "... AND a witness chain covering
 * `concat_all chunks_so_far` exists, in both standalone and embedded-
 * ahead-of-the-next-chunk form"), plus ONE new lemma neither this landing
 * nor any prior one needed: CHAIN CONCATENATION -- "if `ws1` covers `A`
 * (`chain_end 0 ws1 == fs_byte_length A`) and `ws2` covers `B`, then `ws1
 * @ ws2` covers `A ^ B`" (a short structural-induction lemma on `ws1`
 * alone, mirroring `List.Tot.append_assoc`-style reasoning over
 * `chain_wf`/`chain_end`'s own recursive definitions -- estimated
 * mechanical, NOT diagnosed as hitting any prior wall, simply not built
 * in THIS landing's time budget).
 *
 * WHY NOT ATTEMPTED HERE, honestly: the induction, once the chain-
 * concatenation lemma exists, still needs EACH step's witness chains for
 * `c` (the newly-arriving chunk's `complete`/`carry` split) to be SUPPLIED
 * by the caller -- meaning the FULL theorem's honest final form is
 * conditioned on "a witness-chain LIST, one entry per chunk, each
 * covering that chunk's own `split_complete_lines` output" -- a THIRD
 * list-of-lists structure threaded through the fold (chunks x their own
 * witness chains), on top of the chain-concatenation lemma. This is a
 * real, estimably-short next increment (no new wall diagnosed), but is a
 * distinct scoped piece from everything landed in this session and was
 * not started here -- assessed as its own guard-depth-3 unit, not a
 * same-session extension, per the discipline that produced every OTHER
 * clean landing in this file today.
 *
 * NARROWEST VERIFIED CHECKPOINT, this (third) landing: `lemma_parse_
 * nquads_acc_blank_step_shift` / `_comment_step_shift` / `_quad_fail_
 * step_shift` / `_quad_ok_step_shift` (Kinds 1-4), `lemma_parse_nquads_
 * acc_restart` (mixed-kind chain), `lemma_parse_nquads_acc_full_via_
 * chain`, `lemma_parse_nquads_acc_concat_line_general`, `theorem_stream_
 * eq_batch_single_chunk_general` -- all verify clean under `make verify-
 * RDF.NQuads.Streaming` (whole module, dependencies included), no admits,
 * no `--lax`, no new `assume val`, every individual `fstar.exe` run under
 * 25 seconds wall-clock (well inside the "kill any query over 3 minutes"
 * discipline this task set -- z3's own per-query time was never the
 * bottleneck once the hypothesis shape was witness-parameterised, exactly
 * as the module's SECOND-landing FINDING predicted it would be).
 *
 * NEXT NARROWEST UNPROVED STATEMENT: the chain-concatenation lemma above,
 * then the multi-chunk fold induction carrying it plus a per-chunk
 * witness-chain-list invariant. Not started here; no wall diagnosed
 * against it -- purely a scoping decision under the guard-depth-3 /
 * session-budget discipline.
 * ============================================================================ *)

(* ============================================================================
 * MULTI-CHUNK `theorem_stream_eq_batch` (task #48, FOURTH landing,
 * 2026-08-11): closes item 6. Not built the way the THIRD landing's FINDING
 * sketched ("chain-concatenation lemma `ws1 @ ws2` covers `A^B`" as a
 * free-standing piece assembled bottom-up) -- that sketch, worked through
 * fully, turns out to need EVERY per-kind witness POSITION-SHIFTED and its
 * WF-predicate re-derived against a BIGGER `mid` (since `blank_line_wf`/
 * `quad_fail_line_wf`/etc. all state their core facts -- `pws mid ...`,
 * `nq_skip_line mid ...` -- directly against a FIXED `mid`, so growing `mid`
 * means re-deriving every core fact via the shift lemmas, not just
 * relabelling positions) -- buildable in principle (every ingredient is an
 * already-proved shift lemma at `prefix=""` or `suffix=""`), but adds a
 * second full pass through all four kinds beyond what closing the theorem
 * itself needs.
 *
 * THE SHORTER PATH ACTUALLY TAKEN: `lemma_parse_nquads_acc_concat_line_
 * general` (already proved, THIRD landing) takes its SECOND witness chain
 * (`ws_carry`, covering the "carry" argument) as a caller-supplied
 * parameter -- it does not care HOW that chain was built. So instead of
 * constructively ASSEMBLING a chain for the whole remaining tail
 * `carry_k ^ concat_all rest` from smaller per-chunk pieces (which is what
 * needed the shift-heavy reconstruction above), `stream_fold_wf` below asks
 * the CALLER to supply that whole-tail chain directly, once per fold step,
 * ALONGSIDE the per-chunk `complete`-piece chain `wss` already threads
 * through the recursion -- exactly the "witness/premise-supplied" form the
 * task brief's own failure branch sanctions, and no different in KIND from
 * every other witness parameter already in this file (`ws_complete`/
 * `ws_carry` in `theorem_stream_eq_batch_single_chunk_general` are the same
 * shape, just not threaded through a fold). The per-step algebra that
 * CONSUMES both chains (`lemma_parse_nquads_acc_concat_line_general`) is
 * 100% reused, unmodified, from the THIRD landing -- the only genuinely NEW
 * pieces below are `string_concat_assoc` (a `^`-associativity lemma this
 * file had not previously needed, proved the SAME `list_of_string`/
 * `string_of_list` round-trip way as `split_complete_lines_reconstruct`)
 * and the fold induction itself, which is ordinary structural induction on
 * `chunks` composing already-proved facts by transitivity -- no `forall`,
 * no new scanning argument, no new wall.
 * ============================================================================ *)

(* `^` associativity for strings: NOT automatic (plain `()` fails for
   symbolic arguments, per this module's own established pattern -- see the
   module banner and `split_complete_lines_reconstruct`'s own comment) --
   proved via the SAME `list_of_string`/`string_of_list` round-trip
   technique, mirroring `List.Tot.append_assoc` at the list level through
   `list_of_concat`'s two homomorphism facts. *)
val string_concat_assoc (a b c : string)
  : Lemma ((a ^ b) ^ c == a ^ (b ^ c))
let string_concat_assoc a b c =
  FStar.String.list_of_concat a b;
  FStar.String.list_of_concat (a ^ b) c;
  FStar.String.list_of_concat b c;
  FStar.String.list_of_concat a (b ^ c);
  List.Tot.append_assoc (FStar.String.list_of_string a) (FStar.String.list_of_string b) (FStar.String.list_of_string c);
  cong_string_of_list
    ((FStar.String.list_of_string a @ FStar.String.list_of_string b) @ FStar.String.list_of_string c)
    (FStar.String.list_of_string a @ (FStar.String.list_of_string b @ FStar.String.list_of_string c));
  FStar.String.string_of_list_of_string ((a ^ b) ^ c);
  FStar.String.string_of_list_of_string (a ^ (b ^ c))

(* The TOTAL string a chunk list denotes, right-fold order -- matching
   `stream_parse_acc`'s own left-to-right consumption (`c :: rest` processes
   `c` FIRST, then recurses on `rest`), so `concat_all (c :: rest) == c ^
   concat_all rest` unfolds in lock-step with the recursion below. *)
let rec concat_all (chunks : list string) : Tot string (decreases chunks) =
  match chunks with
  | [] -> ""
  | c :: rest -> c ^ concat_all rest

(* Per-fold-step witness data: `ws_c` covers THIS step's own `complete`
   piece (standalone, and embedded ahead of the WHOLE remaining tail --
   `carry' ^ concat_all rest`, not just the next chunk's own carry, since
   that is exactly what `lemma_parse_nquads_acc_concat_line_general` below
   needs for ITS `ws_complete` argument); `ws_t` covers that SAME remaining
   tail (standalone, and embedded right after `complete`) -- the second
   witness chain `concat_line_general` needs as its `ws_carry` argument. Both
   are CALLER-SUPPLIED per step (matching this file's established witness-
   parameter idiom throughout) -- `stream_fold_wf` does not attempt to
   DERIVE `ws_t` from smaller pieces (that is the shift-heavy reconstruction
   the module banner above explains was assessed as a second full pass, not
   attempted this landing); it only checks that whatever the caller supplies
   is well-formed and sufficient, then recurses. *)
let rec stream_fold_wf
    (carry0 : string) (chunks : list string)
    (ws_list : list (list line_witness & list line_witness))
  : Tot Type0 (decreases chunks) =
  match chunks, ws_list with
  | [], [] -> True
  | c :: rest, (ws_c, ws_t) :: wss ->
    (let combined = carry0 ^ c in
     let (complete, carry') = split_complete_lines combined in
     let tail_str = carry' ^ concat_all rest in
     chain_wf "" complete "" 0 ws_c /\
     chain_wf "" complete tail_str 0 ws_c /\
     chain_end 0 ws_c == Parser.FastString.fs_byte_length complete /\
     chain_wf "" tail_str "" 0 ws_t /\
     chain_wf complete tail_str "" 0 ws_t /\
     chain_end 0 ws_t == Parser.FastString.fs_byte_length tail_str /\
     Parser.FastString.fs_byte_length complete + 1 >= List.Tot.length ws_c /\
     Parser.FastString.fs_byte_length tail_str + 1 >= List.Tot.length ws_t /\
     Parser.FastString.fs_byte_length complete + Parser.FastString.fs_byte_length tail_str + 1
       >= List.Tot.length ws_c + List.Tot.length ws_t /\
     stream_fold_wf carry' rest wss)
  | _, _ -> False

(* THE fold invariant: for ANY starting dataset `ds0` and ANY pending
   `carry0`, feeding the remaining `chunks` through `stream_parse_acc`
   lands on exactly the (finalised) result of batch-parsing `carry0 ^
   concat_all chunks` from `ds0` -- structural induction on `chunks`,
   mirroring `stream_parse_acc`'s own recursion one constructor at a time.
   Base case: `feed`'s definition IS `finish`, a one-step unfold plus
   `empty_string_concat_right`. Inductive case: `feed_chunk`'s own
   definition peels off `complete`/`carry'` (no lemma needed, definitional),
   the INDUCTION HYPOTHESIS (applied to `rest`/`carry'`/the post-`complete`
   dataset) handles everything from there on, `lemma_parse_nquads_acc_
   concat_line_general` (THIRD landing, reused verbatim) merges the ONE
   local step back into the big picture, and `string_concat_assoc` +
   `split_complete_lines_reconstruct` + `concat_all`'s own unfolding
   rewrite the two sides' argument strings down to the same thing. *)
#push-options "--z3rlimit 300 --fuel 4 --ifuel 4"
val stream_fold_eq_batch
    (carry0 : string) (chunks : list string)
    (ws_list : list (list line_witness & list line_witness))
    (ds0 : RDF.Graph.Executable.rdf_dataset)
  : Lemma
      (requires stream_fold_wf carry0 chunks ws_list)
      (ensures
        stream_parse_acc chunks ds0 ({ carry = carry0 })
        == RDF.Graph.Executable.dataset_finalise
             (Parser.NQuads.parse_nquads_acc (carry0 ^ concat_all chunks) 0 ds0
                (Parser.FastString.fs_byte_length (carry0 ^ concat_all chunks) + 1)))
      (decreases chunks)
let rec stream_fold_eq_batch carry0 chunks ws_list ds0 =
  match chunks, ws_list with
  | [], [] ->
    empty_string_concat_right carry0
  | c :: rest, (ws_c, ws_t) :: wss ->
    let combined = carry0 ^ c in
    let (complete, carry') = split_complete_lines combined in
    let tail_str = carry' ^ concat_all rest in
    let ds1 = Parser.NQuads.parse_nquads_acc complete 0 ds0 (Parser.FastString.fs_byte_length complete + 1) in
    // feed_chunk {carry=carry0} c ds0 == (ds1, {carry=carry'}) -- definitional,
    // `stream_parse_acc (c::rest) ds0 {carry=carry0} == stream_parse_acc rest ds1 {carry=carry'}`.
    stream_fold_eq_batch carry' rest wss ds1;
    // IH: stream_parse_acc rest ds1 {carry=carry'} ==
    //     dataset_finalise (parse_nquads_acc (carry'^concat_all rest) 0 ds1 (..+1))
    //                    == dataset_finalise (parse_nquads_acc tail_str 0 ds1 (..+1))
    lemma_parse_nquads_acc_concat_line_general complete tail_str ds0 ws_c ws_t;
    // == parse_nquads_acc tail_str 0 (parse_nquads_acc complete 0 ds0 (..+1)) (..+1)
    //    == parse_nquads_acc (complete ^ tail_str) 0 ds0 (fs_byte_length (complete^tail_str)+1)
    split_complete_lines_reconstruct combined;
    // complete ^ carry' == combined == carry0 ^ c
    string_concat_assoc complete carry' (concat_all rest);
    // complete ^ (carry' ^ concat_all rest) == (complete ^ carry') ^ concat_all rest
    string_concat_assoc carry0 c (concat_all rest)
    // carry0 ^ (c ^ concat_all rest) == (carry0 ^ c) ^ concat_all rest
    // Both rewrite (complete ^ tail_str) and (carry0 ^ concat_all (c::rest)) down to
    // the SAME string (carry0 ^ c) ^ concat_all rest -- ordinary `^` congruence
    // (not the `string_of_list`-specific non-congruence this module's FINDING
    // documents) closes the goal from here.
#pop-options

(* Top-level corollary, matching `batch_parse`'s own name: `stream_parse
   chunks == batch_parse (concat_all chunks)` -- instantiate the fold
   invariant at `carry0 = ""`, `ds0 = empty_dataset` (`initial_state`'s own
   fields), and rewrite `"" ^ concat_all chunks == concat_all chunks` via
   `empty_string_concat_left`. This is `theorem_stream_eq_batch`, the task
   #48 FINDING's own named target, in the witness-chain-list CONDITIONED
   form the task brief's failure branch sanctions as an acceptable final
   landing. *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val theorem_stream_eq_batch
    (chunks : list string) (ws_list : list (list line_witness & list line_witness))
  : Lemma
      (requires stream_fold_wf "" chunks ws_list)
      (ensures stream_parse chunks == batch_parse (concat_all chunks))
let theorem_stream_eq_batch chunks ws_list =
  stream_fold_eq_batch "" chunks ws_list RDF.Graph.Executable.empty_dataset;
  empty_string_concat_left (concat_all chunks)
#pop-options

(* ============================================================================
 * `chain_append` (task #48, FIFTH landing, 2026-08-11): the chain-
 * concatenation lemma the THIRD landing's FINDING named ("if `ws_a` covers
 * `mid_a` and `ws_b` covers `mid_b`, an appropriately shifted `ws_a @ ws_b`
 * covers `mid_a ^ mid_b`") -- NOT needed to close `theorem_stream_eq_batch`
 * above (that theorem takes its whole-tail chain as a caller-supplied
 * parameter instead, see that section's own banner), but landed here as
 * the reusable, general piece a future session can use to make that
 * parameter DERIVABLE from smaller per-chunk pieces instead of separately
 * supplied. Built exactly as the FOURTH landing's banner said it could be:
 * every ingredient below is an ALREADY-PROVED shift lemma
 * (`lemma_pws_shift`, `lemma_byte_index_at_middle`, `lemma_skip_eol_shift`,
 * `lemma_skip_comment_shift`, `lemma_nq_skip_line_shift_exact`, `Parser.
 * NTriples.Locality.lemma_parse_nquad_shift_generic`) applied at
 * `prefix=""` (reproving a witness's WF against a BIGGER `mid_a^mid_b`, at
 * its OWN unshifted position, since it is a prefix of the bigger string)
 * or at `suffix=""` (reproving a witness's WF against `mid_a^mid_b` at a
 * position SHIFTED by `fs_byte_length mid_a`, since it starts right after
 * `mid_a`) -- no new proof technique, only new compositions.
 * ============================================================================ *)

(* Position-shift of a single witness: every position field advances by
   `off`; any parsed VALUE payload (subject/predicate/object/graph, quad-
   success kind only) is UNCHANGED -- same parsed value, reached at a
   shifted position. *)
let shift_line_witness (off : nat) (w : line_witness) : line_witness =
  match w with
  | LW_Blank b ->
    LW_Blank ({ lw_pos = off + b.lw_pos; lw_wsend = off + b.lw_wsend; lw_eolend = off + b.lw_eolend })
  | LW_Comment c ->
    LW_Comment ({ cw_pos = off + c.cw_pos; cw_wsend = off + c.cw_wsend;
                  cw_commentend = off + c.cw_commentend; cw_eolend = off + c.cw_eolend })
  | LW_QuadFail f ->
    LW_QuadFail ({ qfw_pos = off + f.qfw_pos; qfw_wsend = off + f.qfw_wsend; qfw_stopeol = off + f.qfw_stopeol })
  | LW_QuadOk q ->
    LW_QuadOk ({ q with
      qow_entry = off + q.qow_entry; qow_pos2 = off + q.qow_pos2; qow_pos3 = off + q.qow_pos3;
      qow_pos4 = off + q.qow_pos4; qow_pos5 = off + q.qow_pos5; qow_pos6 = off + q.qow_pos6;
      qow_pos7 = off + q.qow_pos7; qow_pos8 = off + q.qow_pos8;
      qow_wsend2 = off + q.qow_wsend2; qow_eolend2 = off + q.qow_eolend2 })

val lw_pos_shift (off : nat) (w : line_witness)
  : Lemma (lw_pos (shift_line_witness off w) == off + lw_pos w)
let lw_pos_shift off w =
  match w with
  | LW_Blank _ -> () | LW_Comment _ -> () | LW_QuadFail _ -> () | LW_QuadOk _ -> ()

val lw_end_shift (off : nat) (w : line_witness)
  : Lemma (lw_end (shift_line_witness off w) == off + lw_end w)
let lw_end_shift off w =
  match w with
  | LW_Blank _ -> () | LW_Comment _ -> () | LW_QuadFail _ -> () | LW_QuadOk _ -> ()

(* `lw_wf "" mid_a mid_b w` (a witness already known well-formed EMBEDDED
   ahead of `mid_b`) implies `lw_wf "" (mid_a^mid_b) "" w` (well-formed
   FLAT against the concatenation, no embedding) -- growing `mid` to the
   RIGHT does not move `w`'s own positions (they are all `< fs_byte_length
   mid_a`, a prefix of the bigger string), so no shift, only re-proving each
   core fact at `prefix=""`. For the blank/comment kinds `lw_wf` does not
   even mention `mid_b` (`blank_line_wf`/`comment_line_wf` take only `mid`),
   so the derivation is purely "same fact, bigger string". For quad-fail/
   quad-ok, the disclosed embedded premise in `lw_wf`'s OWN definition
   (`ParseFail?`/success facts against `""^(mid_a^mid_b)`, already required
   by the hypothesis) supplies exactly the one fact that cannot be derived
   (the forward-dispatch obstruction this file's earlier FINDINGs name) --
   everything else is shift-lemma reuse. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_extend_right_blank (mid_a mid_b : string) (b : blank_line_witness)
  : Lemma (requires lw_wf "" mid_a mid_b (LW_Blank b))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (LW_Blank b))
let lw_wf_extend_right_blank mid_a mid_b b =
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_left (mid_a ^ mid_b);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b b.lw_pos b.lw_wsend;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) b.lw_pos == Parser.Combinators.ParseOk () b.lw_wsend);
  lemma_byte_index_at_middle "" mid_a mid_b b.lw_wsend;
  assert (Parser.FastString.fs_byte_index (mid_a ^ mid_b) b.lw_wsend == Parser.FastString.fs_byte_index mid_a b.lw_wsend);
  Parser.NTriples.Locality.lemma_skip_eol_shift "" mid_a mid_b b.lw_wsend;
  assert (Parser.NTriples.skip_eol (mid_a ^ mid_b) b.lw_wsend == b.lw_eolend)
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_extend_right_comment (mid_a mid_b : string) (c : comment_line_witness)
  : Lemma (requires lw_wf "" mid_a mid_b (LW_Comment c))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (LW_Comment c))
let lw_wf_extend_right_comment mid_a mid_b c =
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_left (mid_a ^ mid_b);
  empty_string_concat_right (mid_a ^ mid_b);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b c.cw_pos c.cw_wsend;
  lemma_byte_index_at_middle "" mid_a mid_b c.cw_wsend;
  lemma_skip_comment_shift "" mid_a mid_b c.cw_wsend c.cw_commentend;
  Parser.NTriples.Locality.lemma_skip_eol_shift "" mid_a mid_b c.cw_commentend
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_extend_right_quadfail (mid_a mid_b : string) (f : quad_fail_witness)
  : Lemma (requires lw_wf "" mid_a mid_b (LW_QuadFail f))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (LW_QuadFail f))
let lw_wf_extend_right_quadfail mid_a mid_b f =
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_left (mid_a ^ mid_b);
  empty_string_concat_right (mid_a ^ mid_b);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b f.qfw_pos f.qfw_wsend;
  lemma_byte_index_at_middle "" mid_a mid_b f.qfw_wsend;
  lemma_nq_skip_line_shift_exact "" mid_a mid_b f.qfw_wsend f.qfw_stopeol
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_extend_right_quadok (mid_a mid_b : string) (q : quad_ok_witness)
  : Lemma (requires lw_wf "" mid_a mid_b (LW_QuadOk q))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (LW_QuadOk q))
let lw_wf_extend_right_quadok mid_a mid_b q =
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_left (mid_a ^ mid_b);
  empty_string_concat_right (mid_a ^ mid_b);
  assert ("" ^ ((mid_a ^ mid_b) ^ "") == mid_a ^ mid_b);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b q.qow_entry q.qow_entry;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) q.qow_entry == Parser.Combinators.ParseOk () q.qow_entry);
  assert (Parser.NTriples.parse_subject (mid_a ^ mid_b) q.qow_entry
          == Parser.Combinators.ParseOk q.qow_subj q.qow_pos2);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b q.qow_pos2 q.qow_pos3;
  assert (Parser.NTriples.parse_iri (mid_a ^ mid_b) q.qow_pos3
          == Parser.Combinators.ParseOk q.qow_pred q.qow_pos4);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b q.qow_pos4 q.qow_pos5;
  assert (Parser.NTriples.parse_object (mid_a ^ mid_b) q.qow_pos5
          == Parser.Combinators.ParseOk q.qow_obj q.qow_pos6);
  assert (Parser.NQuads.parse_opt_graph_label (mid_a ^ mid_b) q.qow_pos6
          == Parser.Combinators.ParseOk q.qow_graph q.qow_pos7);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b q.qow_pos7 q.qow_pos8;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) q.qow_pos7 == Parser.Combinators.ParseOk () q.qow_pos8);
  lemma_byte_index_at_middle "" mid_a mid_b q.qow_pos8;
  assert (Parser.FastString.fs_byte_index (mid_a ^ mid_b) q.qow_pos8 == Parser.FastString.fs_byte_index mid_a q.qow_pos8);
  Parser.NTriples.Locality.lemma_pws_shift "" mid_a mid_b (q.qow_pos8 + 1) q.qow_wsend2;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) (q.qow_pos8 + 1) == Parser.Combinators.ParseOk () q.qow_wsend2);
  lemma_byte_index_at_middle "" mid_a mid_b q.qow_wsend2;
  assert (Parser.FastString.fs_byte_index (mid_a ^ mid_b) q.qow_wsend2 == Parser.FastString.fs_byte_index mid_a q.qow_wsend2);
  Parser.NTriples.Locality.lemma_skip_eol_shift "" mid_a mid_b q.qow_wsend2;
  assert (Parser.NTriples.skip_eol (mid_a ^ mid_b) q.qow_wsend2 == q.qow_eolend2);
  assert (quad_ok_line_wf (mid_a ^ mid_b) q)
#pop-options

val lw_wf_extend_right (mid_a mid_b : string) (w : line_witness)
  : Lemma (requires lw_wf "" mid_a mid_b w)
          (ensures  lw_wf "" (mid_a ^ mid_b) "" w)
let lw_wf_extend_right mid_a mid_b w =
  match w with
  | LW_Blank b -> lw_wf_extend_right_blank mid_a mid_b b
  | LW_Comment c -> lw_wf_extend_right_comment mid_a mid_b c
  | LW_QuadFail f -> lw_wf_extend_right_quadfail mid_a mid_b f
  | LW_QuadOk q -> lw_wf_extend_right_quadok mid_a mid_b q

(* Symmetric derivation: `lw_wf mid_a mid_b "" w` (a witness already known
   well-formed EMBEDDED right after `mid_a`) implies `lw_wf "" (mid_a^mid_b)
   "" (shift_line_witness (fs_byte_length mid_a) w)` -- growing `mid` to the
   LEFT DOES move `w`'s own positions, by exactly `fs_byte_length mid_a`
   (the byte count of what is now prepended), so every core fact is
   re-derived via the shift lemmas at `prefix=mid_a, suffix=""` this time. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_shift_left_blank (mid_a mid_b : string) (b : blank_line_witness)
  : Lemma (requires lw_wf mid_a mid_b "" (LW_Blank b))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (shift_line_witness (Parser.FastString.fs_byte_length mid_a) (LW_Blank b)))
let lw_wf_shift_left_blank mid_a mid_b b =
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_right mid_b;
  empty_string_concat_left (mid_a ^ mid_b);
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" b.lw_pos b.lw_wsend;
  lemma_byte_index_at_middle mid_a mid_b "" b.lw_wsend;
  Parser.NTriples.Locality.lemma_skip_eol_shift mid_a mid_b "" b.lw_wsend
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_shift_left_comment (mid_a mid_b : string) (c : comment_line_witness)
  : Lemma (requires lw_wf mid_a mid_b "" (LW_Comment c))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (shift_line_witness (Parser.FastString.fs_byte_length mid_a) (LW_Comment c)))
let lw_wf_shift_left_comment mid_a mid_b c =
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_right mid_b;
  empty_string_concat_left (mid_a ^ mid_b);
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" c.cw_pos c.cw_wsend;
  lemma_byte_index_at_middle mid_a mid_b "" c.cw_wsend;
  lemma_skip_comment_shift mid_a mid_b "" c.cw_wsend c.cw_commentend;
  Parser.NTriples.Locality.lemma_skip_eol_shift mid_a mid_b "" c.cw_commentend
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_shift_left_quadfail (mid_a mid_b : string) (f : quad_fail_witness)
  : Lemma (requires lw_wf mid_a mid_b "" (LW_QuadFail f))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (shift_line_witness (Parser.FastString.fs_byte_length mid_a) (LW_QuadFail f)))
let lw_wf_shift_left_quadfail mid_a mid_b f =
  let off = Parser.FastString.fs_byte_length mid_a in
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_right mid_b;
  empty_string_concat_left (mid_a ^ mid_b);
  empty_string_concat_right (mid_a ^ mid_b);
  assert ("" ^ ((mid_a ^ mid_b) ^ "") == mid_a ^ mid_b);
  assert (Parser.Combinators.ParseFail? (Parser.NQuads.parse_nquad (mid_a ^ mid_b) (off + f.qfw_wsend)));
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" f.qfw_pos f.qfw_wsend;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) (off + f.qfw_pos) == Parser.Combinators.ParseOk () (off + f.qfw_wsend));
  lemma_byte_index_at_middle mid_a mid_b "" f.qfw_wsend;
  lemma_nq_skip_line_shift_exact mid_a mid_b "" f.qfw_wsend f.qfw_stopeol;
  assert (Parser.NQuads.nq_skip_line (mid_a ^ mid_b)
            (Parser.FastString.fs_byte_length (mid_a ^ mid_b)) (off + f.qfw_wsend)
            (Parser.FastString.fs_byte_length mid_b - f.qfw_wsend)
          == off + f.qfw_stopeol)
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_wf_shift_left_quadok (mid_a mid_b : string) (q : quad_ok_witness)
  : Lemma (requires lw_wf mid_a mid_b "" (LW_QuadOk q))
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (shift_line_witness (Parser.FastString.fs_byte_length mid_a) (LW_QuadOk q)))
let lw_wf_shift_left_quadok mid_a mid_b q =
  let off = Parser.FastString.fs_byte_length mid_a in
  Parser.FastString.Axioms.fs_byte_length_concat mid_a mid_b;
  Parser.FastString.Axioms.fs_byte_length_empty ();
  empty_string_concat_right mid_b;
  empty_string_concat_left (mid_a ^ mid_b);
  empty_string_concat_right (mid_a ^ mid_b);
  assert ("" ^ ((mid_a ^ mid_b) ^ "") == mid_a ^ mid_b);
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" q.qow_entry q.qow_entry;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) (off + q.qow_entry) == Parser.Combinators.ParseOk () (off + q.qow_entry));
  assert (Parser.NTriples.parse_subject (mid_a ^ mid_b) (off + q.qow_entry)
          == Parser.Combinators.ParseOk q.qow_subj (off + q.qow_pos2));
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" q.qow_pos2 q.qow_pos3;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) (off + q.qow_pos2) == Parser.Combinators.ParseOk () (off + q.qow_pos3));
  assert (Parser.NTriples.parse_iri (mid_a ^ mid_b) (off + q.qow_pos3)
          == Parser.Combinators.ParseOk q.qow_pred (off + q.qow_pos4));
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" q.qow_pos4 q.qow_pos5;
  assert (Parser.NTriples.pws (mid_a ^ mid_b) (off + q.qow_pos4) == Parser.Combinators.ParseOk () (off + q.qow_pos5));
  assert (Parser.NTriples.parse_object (mid_a ^ mid_b) (off + q.qow_pos5)
          == Parser.Combinators.ParseOk q.qow_obj (off + q.qow_pos6));
  assert (Parser.NQuads.parse_opt_graph_label (mid_a ^ mid_b) (off + q.qow_pos6)
          == Parser.Combinators.ParseOk q.qow_graph (off + q.qow_pos7));
  lemma_byte_index_at_middle mid_a mid_b "" q.qow_pos8;
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" q.qow_pos7 q.qow_pos8;
  Parser.NTriples.Locality.lemma_pws_shift mid_a mid_b "" (q.qow_pos8 + 1) q.qow_wsend2;
  lemma_byte_index_at_middle mid_a mid_b "" q.qow_wsend2;
  Parser.NTriples.Locality.lemma_skip_eol_shift mid_a mid_b "" q.qow_wsend2;
  let q' = { q with
    qow_entry = off + q.qow_entry; qow_pos2 = off + q.qow_pos2; qow_pos3 = off + q.qow_pos3;
    qow_pos4 = off + q.qow_pos4; qow_pos5 = off + q.qow_pos5; qow_pos6 = off + q.qow_pos6;
    qow_pos7 = off + q.qow_pos7; qow_pos8 = off + q.qow_pos8;
    qow_wsend2 = off + q.qow_wsend2; qow_eolend2 = off + q.qow_eolend2 } in
  assert (quad_ok_line_wf (mid_a ^ mid_b) q')
#pop-options

val lw_wf_shift_left (mid_a mid_b : string) (w : line_witness)
  : Lemma (requires lw_wf mid_a mid_b "" w)
          (ensures  lw_wf "" (mid_a ^ mid_b) "" (shift_line_witness (Parser.FastString.fs_byte_length mid_a) w))
let lw_wf_shift_left mid_a mid_b w =
  match w with
  | LW_Blank b -> lw_wf_shift_left_blank mid_a mid_b b
  | LW_Comment c -> lw_wf_shift_left_comment mid_a mid_b c
  | LW_QuadFail f -> lw_wf_shift_left_quadfail mid_a mid_b f
  | LW_QuadOk q -> lw_wf_shift_left_quadok mid_a mid_b q

(* The dataset step a shifted quad-success witness performs on `mid_a^
   mid_b` matches what the ORIGINAL witness performs on `mid_b` alone --
   `Locality.lemma_parse_nquad_shift_generic` gives `parse_nquad`'s parsed
   VALUE agreement directly (the blank/comment/quad-fail kinds never touch
   the dataset at all, so their cases are trivial). *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lw_ds_step_shift (mid_a mid_b : string) (w : line_witness) (ds : RDF.Graph.Executable.rdf_dataset)
  : Lemma (requires lw_wf mid_a mid_b "" w)
          (ensures
            lw_ds_step (mid_a ^ mid_b) (shift_line_witness (Parser.FastString.fs_byte_length mid_a) w) ds
            == lw_ds_step mid_b w ds)
let lw_ds_step_shift mid_a mid_b w ds =
  match w with
  | LW_Blank _ -> () | LW_Comment _ -> () | LW_QuadFail _ -> ()
  | LW_QuadOk q ->
    empty_string_concat_right mid_b;
    Parser.NTriples.Locality.lemma_parse_nquad_shift_generic mid_a mid_b "" q.qow_entry q.qow_entry
      q.qow_subj q.qow_pos2 q.qow_pos3 q.qow_pred q.qow_pos4 q.qow_pos5 q.qow_obj q.qow_pos6
      q.qow_graph q.qow_pos7 q.qow_pos8
#pop-options

(* Chain-level lifts of the three per-witness facts above, by ordinary
   structural induction on `ws` -- `chain_wf`/`chain_end`'s own recursion
   threads `lw_end w` (or its shifted counterpart) forward automatically,
   so each step is exactly one per-witness lemma call plus the recursive
   call on the tail. *)
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val chain_wf_extend_right (mid_a mid_b : string) (start_pos : nat) (ws : list line_witness)
  : Lemma (requires chain_wf "" mid_a mid_b start_pos ws)
          (ensures chain_wf "" (mid_a ^ mid_b) "" start_pos ws)
          (decreases ws)
let rec chain_wf_extend_right mid_a mid_b start_pos ws =
  match ws with
  | [] -> ()
  | w :: rest ->
    lw_wf_extend_right mid_a mid_b w;
    chain_wf_extend_right mid_a mid_b (lw_end w) rest
#pop-options

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val chain_end_shift (off start_pos : nat) (ws : list line_witness)
  : Lemma (ensures chain_end (off + start_pos) (List.Tot.map (shift_line_witness off) ws)
                    == off + chain_end start_pos ws)
          (decreases ws)
let rec chain_end_shift off start_pos ws =
  match ws with
  | [] -> ()
  | w :: rest ->
    lw_end_shift off w;
    chain_end_shift off (lw_end w) rest
#pop-options

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val chain_wf_shift_left (mid_a mid_b : string) (start_pos : nat) (ws : list line_witness)
  : Lemma (requires chain_wf mid_a mid_b "" start_pos ws)
          (ensures chain_wf "" (mid_a ^ mid_b) ""
                     (Parser.FastString.fs_byte_length mid_a + start_pos)
                     (List.Tot.map (shift_line_witness (Parser.FastString.fs_byte_length mid_a)) ws))
          (decreases ws)
let rec chain_wf_shift_left mid_a mid_b start_pos ws =
  match ws with
  | [] -> ()
  | w :: rest ->
    lw_wf_shift_left mid_a mid_b w;
    lw_pos_shift (Parser.FastString.fs_byte_length mid_a) w;
    lw_end_shift (Parser.FastString.fs_byte_length mid_a) w;
    chain_wf_shift_left mid_a mid_b (lw_end w) rest
#pop-options

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val chain_ds_fold_shift
    (mid_a mid_b : string) (start_pos : nat) (ws : list line_witness) (ds : RDF.Graph.Executable.rdf_dataset)
  : Lemma (requires chain_wf mid_a mid_b "" start_pos ws)
          (ensures
            chain_ds_fold (mid_a ^ mid_b) (List.Tot.map (shift_line_witness (Parser.FastString.fs_byte_length mid_a)) ws) ds
            == chain_ds_fold mid_b ws ds)
          (decreases ws)
let rec chain_ds_fold_shift mid_a mid_b start_pos ws ds =
  match ws with
  | [] -> ()
  | w :: rest ->
    lw_ds_step_shift mid_a mid_b w ds;
    chain_ds_fold_shift mid_a mid_b (lw_end w) rest (lw_ds_step mid_b w ds)
#pop-options

(* Pure list-append fact for `chain_wf`/`chain_end`/`chain_ds_fold` -- no
   shift/embedding reasoning at all, mirrors `List.Tot.append_assoc`-style
   structural induction over `chain_wf`'s own recursive definition (the
   FINDING's own "estimated mechanical" piece, in its purest form). *)
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val chain_wf_append (prefix mid suffix : string) (start_pos : nat) (ws1 ws2 : list line_witness)
  : Lemma
      (requires chain_wf prefix mid suffix start_pos ws1 /\
                chain_wf prefix mid suffix (chain_end start_pos ws1) ws2)
      (ensures chain_wf prefix mid suffix start_pos (ws1 @ ws2) /\
               chain_end start_pos (ws1 @ ws2) == chain_end (chain_end start_pos ws1) ws2)
      (decreases ws1)
let rec chain_wf_append prefix mid suffix start_pos ws1 ws2 =
  match ws1 with
  | [] -> ()
  | w :: rest -> chain_wf_append prefix mid suffix (lw_end w) rest ws2
#pop-options

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val chain_ds_fold_append (mid : string) (ws1 ws2 : list line_witness) (ds : RDF.Graph.Executable.rdf_dataset)
  : Lemma (ensures chain_ds_fold mid (ws1 @ ws2) ds == chain_ds_fold mid ws2 (chain_ds_fold mid ws1 ds))
          (decreases ws1)
let rec chain_ds_fold_append mid ws1 ws2 ds =
  match ws1 with
  | [] -> ()
  | w :: rest -> chain_ds_fold_append mid rest ws2 (lw_ds_step mid w ds)
#pop-options

(* THE chain-concatenation lemma: `ws_a @ (shift ws_b)` covers `mid_a ^
   mid_b`, standalone, given `ws_a` covers `mid_a` (embedded ahead of
   `mid_b`) and `ws_b` covers `mid_b` (embedded right after `mid_a`) --
   exactly the shape the THIRD landing's FINDING asked for. Composes the
   six lemmas immediately above; no new induction here. *)
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
val chain_append (mid_a mid_b : string) (ws_a ws_b : list line_witness)
  : Lemma
      (requires
        chain_wf "" mid_a mid_b 0 ws_a /\
        chain_end 0 ws_a == Parser.FastString.fs_byte_length mid_a /\
        chain_wf mid_a mid_b "" 0 ws_b /\
        chain_end 0 ws_b == Parser.FastString.fs_byte_length mid_b)
      (ensures
        (let off = Parser.FastString.fs_byte_length mid_a in
         let ws_ab = ws_a @ List.Tot.map (shift_line_witness off) ws_b in
         chain_wf "" (mid_a ^ mid_b) "" 0 ws_ab /\
         chain_end 0 ws_ab == off + Parser.FastString.fs_byte_length mid_b))
let chain_append mid_a mid_b ws_a ws_b =
  let off = Parser.FastString.fs_byte_length mid_a in
  chain_wf_extend_right mid_a mid_b 0 ws_a;
  chain_wf_shift_left mid_a mid_b 0 ws_b;
  chain_end_shift off 0 ws_b;
  chain_wf_append "" (mid_a ^ mid_b) "" 0 ws_a (List.Tot.map (shift_line_witness off) ws_b)
#pop-options

(* ============================================================================
 * FINDING (guard-depth-3 stop, SIXTH landing, 2026-08-11): the dataset-fold
 * companion to `chain_append` -- "folding the appended chain from any `ds`
 * matches folding `ws_a` on `mid_a` then `ws_b` on `mid_b`" -- is NOT
 * closed. It needs one more per-witness fact beyond everything above:
 * `lw_ds_step (mid_a^mid_b) w ds == lw_ds_step mid_a w ds` for a quad-
 * success witness `w` already known well-formed EMBEDDED ahead of `mid_b`
 * (growing `mid` to the RIGHT does not move `w`'s position, so this needs
 * no position bookkeeping -- ONLY `Locality.lemma_parse_nquad_shift_
 * generic`'s parsed-VALUE agreement, already available as a hypothesis-
 * satisfying call). Three attempts, each confirmed a genuine multi-minute
 * z3 search (not a quick rejection) via `ps` on the live `z3-4.13.3`
 * child, all still running past 3m20s when killed:
 *   1. Plain composition (`lemma_parse_nquad_shift_generic` call, no
 *      further help) -- "Could not prove post-condition", generic span.
 *   2. Same, plus an explicit `assert` restating the match-shaped
 *      conclusion inline -- still running past 3m20s, killed.
 *   3. Same content, restructured as a PROOF-LEVEL match on `(parse_nquad
 *      mid_a q.qow_entry, parse_nquad (mid_a^mid_b) q.qow_entry)` (letting
 *      F*'s tactic engine case-split instead of asking Z3 to case-split
 *      inside one assert) -- still running past 3m20s, killed.
 *
 * DIAGNOSIS: `lw_ds_step`'s OWN body already contains a `match parse_nquad
 * mid q.qow_entry with ParseOk (t,g) _ -> ... | _ -> ds`, and `parse_nquad`
 * is a large recursive-descent function (`Parser.NQuads.fst`) with no
 * `unfold` annotation -- asking Z3 to unfold `lw_ds_step` TWICE (once per
 * side of the goal equality, at TWO different `mid` arguments) and connect
 * each unfolding to `lemma_parse_nquad_shift_generic`'s own match-shaped
 * conclusion appears to multiply the case-split cost far beyond what
 * `chain_wf_extend_right`'s analogous (but WF-predicate-only, no
 * `parse_nquad` re-matching) proof needed. Every OTHER `lw_wf_*`/`chain_*`
 * lemma in this section stays under 5s per the same `--admit_except`
 * isolation test that caught this one running long -- this is the FIRST
 * (and, per this landing's testing, ONLY) piece in the whole `chain_
 * append` cluster to hit the guard.
 *
 * THE FIX A FUTURE SESSION SHOULD TRY FIRST: state `lw_ds_step`'s
 * `parse_nquad`-match OUTCOME as an explicit lemma of its own
 * (`lw_ds_step_via_parse_nquad : Lemma (lw_ds_step mid (LW_QuadOk q) ds ==
 * (match parse_nquad mid q.qow_entry with ParseOk (t,g) _ ->
 * dataset_add_quad ds t g | _ -> ds))`, trivial by `()` since it is
 * `lw_ds_step`'s own definition) and apply it EXPLICITLY on both sides
 * BEFORE calling `lemma_parse_nquad_shift_generic`, so Z3 is asked to
 * connect two ALREADY-UNFOLDED match expressions rather than unfold
 * `lw_ds_step` itself under the weight of the rest of the query -- this
 * mirrors the fix that closed `lw_wf_extend_right_quadok`/`lw_wf_shift_
 * left_quadok` above (explicit intermediate `assert`s per field, rather
 * than one large composed goal).
 *
 * WHAT REMAINS VERIFIED (this landing): `chain_append` (position/WF
 * conclusion only) is COMPLETE and verifies clean -- a caller who already
 * has a witness chain covering `mid_a` (embedded ahead of `mid_b`) and one
 * covering `mid_b` (embedded after `mid_a`) can combine them into one
 * chain covering `mid_a ^ mid_b`, matching the THIRD landing's FINDING
 * exactly. Only the DATASET-EQUALITY companion fact (useful for actually
 * eliminating `stream_fold_wf`'s separately-supplied `ws_t` parameter, see
 * that section's own banner) is what stops here.
 * ============================================================================ *)

(* ============================================================================
 * CONSUMER HOMOMORPHISM (issue #402, this file's last theorem layer,
 * SEVENTH landing, 2026-08-11): the "into a consumer" half of the owner's
 * terabyte-streaming question. `theorem_stream_eq_batch` above answers the
 * PARSER half (streaming dataset construction == batch dataset
 * construction); this section answers the other half -- feeding quads to
 * an arbitrary consumer FOLD, one chunk at a time, gives the same final
 * consumer state as feeding the batch-parsed quads to that SAME fold.
 *
 * THE API. `stream_consume (#a) (consume : a -> qquad -> a) (init : a)
 * (chunks : list string) : a` below is built ENTIRELY by REUSING existing
 * parsing machinery -- `Parser.NQuads.fold_nquads_acc`, the generic-
 * accumulator sibling of `parse_nquads_acc` this project's own `Parser.
 * NQuads.fst` banner documents as built for exactly this purpose ("Generic
 * streaming fold (CLI parse-stream query fast path...)"). NOT a new
 * parser, not a reimplementation of the line-scanning logic: `feed_chunk_
 * consume` below composes `split_complete_lines` (this file, already
 * proved) with `fold_nquads_acc` (`Parser.NQuads.fst`, already proved as a
 * parser -- its own correctness is not re-litigated here, only its
 * chunk-boundary behaviour), the SAME two-piece composition `feed_chunk`
 * uses for dataset construction, just folding into a caller-supplied `a`
 * instead of an `rdf_dataset`.
 *
 * ORDER, STATED PRECISELY (per this task's own design note: "if order is
 * not canonical, state the theorem for the dataset-derived quad list as-is
 * and say so"). `RDF.Canonical.dataset_quads` (this project's existing
 * "flatten a dataset to its quads" notion, used for canonicalisation) is
 * GROUPED BY GRAPH: every default-graph quad first, then every quad of
 * each named graph in that graph's FIRST-APPEARANCE order -- NOT the order
 * quads appear in the source document whenever two different graphs'
 * quads interleave (a document `default, graphA, default, graphA` yields
 * `dataset_quads` order `default, default, graphA, graphA`, not arrival
 * order). Reproducing THAT grouped order from a bounded-memory, one-chunk-
 * at-a-time consumer is not possible in general: a later chunk can reopen
 * a graph whose quads an earlier chunk already handed to the consumer, so
 * "group by graph" requires buffering the WHOLE stream (exactly what
 * `dataset_finalise`+`dataset_quads` do, after the fact, over a fully
 * materialised dataset). Choosing `dataset_quads` order as this section's
 * target would therefore either (a) force `stream_consume` to buffer
 * everything (defeating the whole point of a streaming consumer), or (b)
 * be FALSE for interleaved-graph documents. Neither is acceptable, so this
 * section instead targets ARRIVAL order: `Parser.NQuads.fold_nquads`'s own
 * order, i.e. exactly the sequence `parse_nquads_acc`'s single walk visits
 * quads in, top of the document to the bottom, REGARDLESS of which graph
 * each one targets -- the one order a truly bounded-memory streaming
 * consumer CAN reproduce, and the order a real bulk-loading consumer
 * (INSERT each quad as parsed) actually wants.
 * ============================================================================ *)

(* `consume`'s "receive one quad" shape (`a -> qquad -> a`) wrapped into
   `fold_nquads_acc`'s own step shape (`triple -> option iri -> a -> a`,
   the SAME shape `Parser.NQuads.fold_nquads`'s existing callers already
   use) -- pure notation, no new logic. `qquad = (option iri * triple)`
   (`RDF.Canonical.fst`), so `(g, t)` matches its constructor order. *)
let quad_step (#a:Type) (consume : a -> RDF.Canonical.qquad -> a)
    (t : RDF.Graph.Executable.triple) (g : option RDF.Graph.Executable.iri) (acc : a) : a =
  consume acc (g, t)

(* This module never wants early stopping (unlike `SPARQL.Plan.
   Streamable.fst`'s ASK fast path, `fold_nquads`'s other caller) -- a
   full-ingest consumer always wants every quad. Named so every call site
   below states its intent instead of repeating a `fun _ -> false` literal. *)
let never_stop (#a:Type) (_ : a) : bool = false

(* One chunk's worth of consumer folding: identical shape to `feed_chunk`
   (same `carry ^ chunk` combine, same `split_complete_lines` call), except
   the `complete` prefix is folded into the caller's accumulator `a` via
   `fold_nquads_acc` instead of parsed into a fresh `rdf_dataset` slice via
   `parse_nquads_acc`. State threaded out is `(a * stream_state)` -- see
   the CONSTANT-MEMORY remark below. *)
let feed_chunk_consume (#a:Type) (consume : a -> RDF.Canonical.qquad -> a)
    (st : stream_state) (acc : a) (chunk : string) : a * stream_state =
  let combined = st.carry ^ chunk in
  let (complete, carry') = split_complete_lines combined in
  let acc' = Parser.NQuads.fold_nquads_acc (quad_step consume) (never_stop #a)
               complete 0 acc (Parser.FastString.fs_byte_length complete + 1) in
  (acc', { carry = carry' })

(* End of stream: fold whatever partial line remains in `carry` -- the
   consumer analogue of `finish`. *)
let finish_consume (#a:Type) (consume : a -> RDF.Canonical.qquad -> a)
    (st : stream_state) (acc : a) : a =
  Parser.NQuads.fold_nquads_acc (quad_step consume) (never_stop #a)
    st.carry 0 acc (Parser.FastString.fs_byte_length st.carry + 1)

let rec stream_consume_acc (#a:Type) (consume : a -> RDF.Canonical.qquad -> a)
    (chunks : list string) (acc : a) (st : stream_state)
  : Tot a (decreases chunks) =
  match chunks with
  | [] -> finish_consume consume st acc
  | c :: rest ->
    let (acc', st') = feed_chunk_consume consume st acc c in
    stream_consume_acc consume rest acc' st'

(* THE consumer-facing entry point (task brief's `stream_consume`). *)
let stream_consume (#a:Type) (consume : a -> RDF.Canonical.qquad -> a) (init : a) (chunks : list string) : a =
  stream_consume_acc consume chunks init initial_state

(* CONSTANT-MEMORY COROLLARY (design note item 4) -- definitional, not a
   theorem: `stream_consume_acc`'s own signature above IS the observation.
   The value threaded from one chunk to the next is exactly `(acc : a) *
   stream_state`, i.e. `a`'s own footprint plus `carry` (at most one
   line's worth of pending bytes, per `split_complete_lines_carry_no_nl`).
   No `list qquad`, no `rdf_dataset`, no witness structure, no growing
   accumulator OTHER than whatever `a`/`consume` itself chooses to retain,
   is threaded anywhere in this recursion -- contrast `stream_parse_acc`
   above, which threads a full, linearly-growing `rdf_dataset` as its
   OTHER argument. This is a claim about `stream_consume`'s own recursion
   SHAPE (true for every `a`), not a claim that every instantiation runs
   in bounded memory -- `dataset_consume` below, whose `a = rdf_dataset`,
   necessarily grows (any consumer that reconstructs the whole dataset
   must), exactly as it would parsing in one shot; `stream_consume`
   contributes no ADDITIONAL retention beyond what `a` itself needs. *)

(* Batch reference point: fold `consume` over `s`'s quads in ONE call, no
   chunking -- `Parser.NQuads.fold_nquads`, already existing, already the
   project's own "generic consumer" entry point (`Parser.NQuads.fst`'s own
   banner). Named here (like `batch_parse` above) so the homomorphism
   theorems below have a fixed target to cite. *)
let batch_consume (#a:Type) (consume : a -> RDF.Canonical.qquad -> a) (init : a) (s : string) : a =
  Parser.NQuads.fold_nquads (quad_step consume) (never_stop #a) init s

(* One concrete rewrite of `stream_consume consume init [c]` down to its
   two constituent `fold_nquads_acc` calls -- the consumer analogue of
   `stream_parse_single_chunk_shape`, same proof (`empty_string_concat_
   left`, since `initial_state.carry = ""`). *)
val stream_consume_single_chunk_shape (#a:Type) (consume : a -> RDF.Canonical.qquad -> a) (init : a) (c : string)
  : Lemma (stream_consume consume init [c] ==
           (let (complete, carry) = split_complete_lines c in
            let acc1 = Parser.NQuads.fold_nquads_acc (quad_step consume) (never_stop #a) complete 0 init
                          (Parser.FastString.fs_byte_length complete + 1) in
            Parser.NQuads.fold_nquads_acc (quad_step consume) (never_stop #a) carry 0 acc1
              (Parser.FastString.fs_byte_length carry + 1)))
let stream_consume_single_chunk_shape #a consume init c =
  empty_string_concat_left c

(* `fold_nquads_acc` on the empty string is the identity, for ANY step/
   stop/accumulator/fuel -- the generic-consumer analogue of `parse_nquads_
   acc ""  0 X (n+1) == X` used throughout item 4/5 above (same one-step
   unfold technique: `fs_byte_length "" == 0` makes `pos >= len` fire
   immediately, or `fuel = 0` fires first -- either way every branch of
   `fold_nquads_acc`'s definition returns `acc` unchanged). *)
#push-options "--fuel 2 --ifuel 2"
val fold_nquads_acc_empty (#a:Type)
    (step : RDF.Graph.Executable.triple -> option RDF.Graph.Executable.iri -> a -> a)
    (stop : a -> bool) (acc : a) (fuel : nat)
  : Lemma (Parser.NQuads.fold_nquads_acc step stop "" 0 acc fuel == acc)
let fold_nquads_acc_empty #a step stop acc fuel =
  Parser.FastString.Axioms.fs_byte_length_empty ()
#pop-options

(* ============================================================================
 * SINGLE-CHUNK CONSUMER HOMOMORPHISM, generic over `a`/`consume` -- the
 * consumer analogue of `theorem_stream_eq_batch_single_chunk_{no_newline,
 * ends_in_newline}`/`theorem_stream_eq_batch_single_chunk` above, same two
 * boundary conditions (`c` has no newline at all, OR `c` ends in a
 * newline), same PURE-ALGEBRA proof shape (one operand of the two-call
 * pipeline is always `""`, so `fold_nquads_acc_empty` collapses it,
 * no embedding/witness argument needed) -- holds for ANY consumer type
 * `a` and ANY `consume`, not just the dataset-building one.
 * ============================================================================ *)
#push-options "--fuel 2 --ifuel 2"
val theorem_stream_consume_single_chunk_no_newline (#a:Type)
    (consume : a -> RDF.Canonical.qquad -> a) (init : a) (c : string)
  : Lemma
      (requires (forall ch. List.Tot.memP ch (FStar.String.list_of_string c) ==> ~ (is_nl ch)))
      (ensures stream_consume consume init [c] == batch_consume consume init c)
let theorem_stream_consume_single_chunk_no_newline #a consume init c =
  stream_consume_single_chunk_shape consume init c;
  split_complete_lines_no_newline c;
  // split_complete_lines c == ("", c): fst == "", snd == c.
  fold_nquads_acc_empty (quad_step consume) (never_stop #a) init (Parser.FastString.fs_byte_length "" + 1)
#pop-options

#push-options "--fuel 2 --ifuel 2"
val theorem_stream_consume_single_chunk_ends_in_newline (#a:Type)
    (consume : a -> RDF.Canonical.qquad -> a) (init : a) (c : string)
  : Lemma
      (requires FStar.String.length c > 0 /\ is_nl (List.Tot.last (FStar.String.list_of_string c)))
      (ensures stream_consume consume init [c] == batch_consume consume init c)
let theorem_stream_consume_single_chunk_ends_in_newline #a consume init c =
  stream_consume_single_chunk_shape consume init c;
  split_complete_lines_ends_in_newline c;
  // split_complete_lines c == (c, ""): fst == c, snd == "".
  let (complete, carry) = split_complete_lines c in
  let acc1 = Parser.NQuads.fold_nquads_acc (quad_step consume) (never_stop #a) complete 0 init
               (Parser.FastString.fs_byte_length complete + 1) in
  fold_nquads_acc_empty (quad_step consume) (never_stop #a) acc1 (Parser.FastString.fs_byte_length carry + 1)
#pop-options

(* Unified statement, generic over `a`/`consume`: either boundary condition
   suffices. *)
val theorem_stream_consume_single_chunk (#a:Type) (consume : a -> RDF.Canonical.qquad -> a) (init : a) (c : string)
  : Lemma
      (requires
        (forall ch. List.Tot.memP ch (FStar.String.list_of_string c) ==> ~ (is_nl ch)) \/
        (FStar.String.length c > 0 /\ is_nl (List.Tot.last (FStar.String.list_of_string c))))
      (ensures stream_consume consume init [c] == batch_consume consume init c)
let theorem_stream_consume_single_chunk #a consume init c =
  if FStar.String.length c = 0 then
    theorem_stream_consume_single_chunk_no_newline consume init c
  else if is_nl (List.Tot.last (FStar.String.list_of_string c)) then
    theorem_stream_consume_single_chunk_ends_in_newline consume init c
  else
    theorem_stream_consume_single_chunk_no_newline consume init c

(* ============================================================================
 * FULLY GENERAL (multi-chunk, no boundary restriction) CONSUMER
 * HOMOMORPHISM -- for the "build a dataset while streaming" consumer
 * specifically. Routed THROUGH `theorem_stream_eq_batch`/`stream_fold_eq_
 * batch` above, as the design brief asked: the only NEW proof burden is
 * `fold_nquads_acc_eq_parse_nquads_acc` below, a cheap, witness-free
 * structural induction (fold_nquads_acc's control flow is BRANCH-FOR-
 * BRANCH identical to parse_nquads_acc's -- `stop = never_stop` never
 * fires, so the only difference between the two function bodies is one
 * expression, `step t g acc` vs `dataset_add_quad ds t g`, at the single
 * quad-match branch; every OTHER branch's condition and recursive-call
 * position is syntactically the same in both functions). Given that
 * bridging fact, `dataset_consume`'s own `stream_consume` run is, step for
 * step, `feed_chunk`'s own run -- so `theorem_stream_eq_batch`'s ALREADY-
 * PROVED, UNCONDITIONED-ON-BOUNDARY multi-chunk result (under the SAME
 * `stream_fold_wf` witness premise) transports over directly, no witness-
 * chain re-derivation needed for THIS instantiation.
 * ============================================================================ *)

(* The canonical "reconstruct the dataset" consumer: `qquad`'s `(graph,
   triple)` pair fed straight to `dataset_add_quad`. This is `consume`
   instantiated so that `stream_consume dataset_consume` answers "what if
   the consumer IS dataset construction" -- the natural sanity case, and
   the one this section proves fully generally. *)
let dataset_consume (ds : RDF.Graph.Executable.rdf_dataset) (q : RDF.Canonical.qquad) : RDF.Graph.Executable.rdf_dataset =
  let (g, t) = q in Parser.NQuads.dataset_add_quad ds t g

(* THE bridging lemma: `fold_nquads_acc`, instantiated at `dataset_consume`
   (via `quad_step`) and `never_stop`, computes EXACTLY what `parse_nquads_
   acc` computes, for every input/position/dataset/fuel. Proof: reconstruct
   both functions' shared control-flow skeleton (same `let pos1 = match pws
   ... `, same four dispatch branches on `pos1`'s byte, same `pos_next`/
   `pos2` computations) inside the proof and recurse at each continuation
   point -- `stop acc`/`stop acc1` (fold_nquads_acc's one extra check
   beyond parse_nquads_acc) always evaluates to `false` (`never_stop`), so
   it never diverts control flow; every base case returns the SAME
   accumulator/dataset value (both `acc`/`ds` are literally the same
   parameter in this specific call), so `()` closes each leaf. No shift
   lemma, no witness chain -- this is ONE function's recursive equation
   matched against ANOTHER's, not a claim about embedding a string inside
   a larger one. *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
val fold_nquads_acc_eq_parse_nquads_acc
    (input : string) (pos : nat) (ds : RDF.Graph.Executable.rdf_dataset) (fuel : nat)
  : Lemma
      (ensures
        Parser.NQuads.fold_nquads_acc (quad_step dataset_consume) (never_stop #RDF.Graph.Executable.rdf_dataset)
          input pos ds fuel
        == Parser.NQuads.parse_nquads_acc input pos ds fuel)
      (decreases fuel)
let rec fold_nquads_acc_eq_parse_nquads_acc input pos ds fuel =
  if fuel = 0 then ()
  else
    let len = Parser.FastString.fs_byte_length input in
    if pos >= len then ()
    else
      let pos1 : nat = match Parser.NTriples.pws input pos with
                       | Parser.Combinators.ParseOk () p -> p
                       | _ -> pos in
      if pos1 >= len then ()
      else
        let ch = Parser.FastString.fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x23 then
          let pos2 = Parser.NTriples.skip_comment input pos1 in
          let pos3 = Parser.NTriples.skip_eol input pos2 in
          if pos3 = pos1 then ()
          else fold_nquads_acc_eq_parse_nquads_acc input pos3 ds (fuel - 1)
        else if code = 0x0A || code = 0x0D then
          let pos2 = Parser.NTriples.skip_eol input pos1 in
          if pos2 = pos1 then ()
          else fold_nquads_acc_eq_parse_nquads_acc input pos2 ds (fuel - 1)
        else
          match Parser.NQuads.parse_nquad input pos1 with
          | Parser.Combinators.ParseOk (t, graph_opt) pos2 ->
            let ds' = Parser.NQuads.dataset_add_quad ds t graph_opt in
            let pos3 = match Parser.NTriples.pws input pos2 with
                       | Parser.Combinators.ParseOk () p -> p
                       | _ -> pos2 in
            let pos4 = Parser.NTriples.skip_comment input pos3 in
            let pos5 = Parser.NTriples.skip_eol input pos4 in
            let pos_next = if pos5 > pos1 then pos5 else if pos4 > pos1 then pos4 else pos2 in
            fold_nquads_acc_eq_parse_nquads_acc input pos_next ds' (fuel - 1)
          | Parser.Combinators.ParseFail _ _ ->
            let pos2 = Parser.NQuads.nq_skip_line input len pos1 (len - pos1) in
            if pos2 = pos1 then ()
            else fold_nquads_acc_eq_parse_nquads_acc input pos2 ds (fuel - 1)
#pop-options

(* Multi-chunk fold invariant for `dataset_consume`, RAW (no `dataset_
   finalise` -- a generic consumer cannot apply it, so this states the
   pre-finalise quantity directly, matching `parse_nquads_acc`'s own
   un-finalised accumulation): near-verbatim copy of `stream_fold_eq_
   batch`'s own proof (SAME induction shape, SAME lemma calls --
   `lemma_parse_nquads_acc_concat_line_general`, `split_complete_lines_
   reconstruct`, `string_concat_assoc` twice), with `fold_nquads_acc_eq_
   parse_nquads_acc` inserted once per step to bridge `feed_chunk_
   consume`'s `fold_nquads_acc` call to `feed_chunk`'s `parse_nquads_acc`
   call -- the ONLY new ingredient beyond `stream_fold_eq_batch` itself. *)
#push-options "--z3rlimit 300 --fuel 4 --ifuel 4"
val stream_consume_dataset_fold_eq_batch
    (carry0 : string) (chunks : list string)
    (ws_list : list (list line_witness & list line_witness))
    (ds0 : RDF.Graph.Executable.rdf_dataset)
  : Lemma
      (requires stream_fold_wf carry0 chunks ws_list)
      (ensures
        stream_consume_acc dataset_consume chunks ds0 ({ carry = carry0 })
        == Parser.NQuads.parse_nquads_acc (carry0 ^ concat_all chunks) 0 ds0
             (Parser.FastString.fs_byte_length (carry0 ^ concat_all chunks) + 1))
      (decreases chunks)
let rec stream_consume_dataset_fold_eq_batch carry0 chunks ws_list ds0 =
  match chunks, ws_list with
  | [], [] ->
    empty_string_concat_right carry0;
    fold_nquads_acc_eq_parse_nquads_acc carry0 0 ds0 (Parser.FastString.fs_byte_length carry0 + 1)
  | c :: rest, (ws_c, ws_t) :: wss ->
    let combined = carry0 ^ c in
    let (complete, carry') = split_complete_lines combined in
    let tail_str = carry' ^ concat_all rest in
    let ds1 = Parser.NQuads.parse_nquads_acc complete 0 ds0 (Parser.FastString.fs_byte_length complete + 1) in
    fold_nquads_acc_eq_parse_nquads_acc complete 0 ds0 (Parser.FastString.fs_byte_length complete + 1);
    // feed_chunk_consume dataset_consume {carry=carry0} ds0 c == (ds1, {carry=carry'}), now
    // definitional given the bridging fact just established.
    stream_consume_dataset_fold_eq_batch carry' rest wss ds1;
    lemma_parse_nquads_acc_concat_line_general complete tail_str ds0 ws_c ws_t;
    split_complete_lines_reconstruct combined;
    string_concat_assoc complete carry' (concat_all rest);
    string_concat_assoc carry0 c (concat_all rest)
#pop-options

(* Top-level corollary, `carry0 = ""`/`ds0 = empty_dataset` -- RAW form
   (pre-`dataset_finalise`), matching `stream_consume_dataset_fold_eq_
   batch`'s own un-finalised statement. *)
val stream_consume_dataset_eq_batch_raw
    (chunks : list string) (ws_list : list (list line_witness & list line_witness))
  : Lemma
      (requires stream_fold_wf "" chunks ws_list)
      (ensures
        stream_consume dataset_consume RDF.Graph.Executable.empty_dataset chunks
        == Parser.NQuads.parse_nquads_acc (concat_all chunks) 0 RDF.Graph.Executable.empty_dataset
             (Parser.FastString.fs_byte_length (concat_all chunks) + 1))
let stream_consume_dataset_eq_batch_raw chunks ws_list =
  stream_consume_dataset_fold_eq_batch "" chunks ws_list RDF.Graph.Executable.empty_dataset;
  empty_string_concat_left (concat_all chunks)

(* THE fully general consumer homomorphism theorem for `dataset_consume`:
   finalising `stream_consume`'s raw result (the one correction a generic
   consumer cannot perform for itself -- see the CONSTANT-MEMORY remark
   above) equals `batch_parse`'s own dataset. Matches `theorem_stream_eq_
   batch`'s exact scope (same `stream_fold_wf` witness premise, no
   boundary/no-newline restriction) -- this is the "does the generic
   consumer API actually agree with the fully-proven parser-level theorem"
   sanity case, answered YES, unconditionally on chunk boundaries. *)
val theorem_stream_consume_dataset_eq_batch
    (chunks : list string) (ws_list : list (list line_witness & list line_witness))
  : Lemma
      (requires stream_fold_wf "" chunks ws_list)
      (ensures
        RDF.Graph.Executable.dataset_finalise (stream_consume dataset_consume RDF.Graph.Executable.empty_dataset chunks)
        == batch_parse (concat_all chunks))
let theorem_stream_consume_dataset_eq_batch chunks ws_list =
  stream_consume_dataset_eq_batch_raw chunks ws_list

(* ============================================================================
 * FINDING (SEVENTH landing, 2026-08-11): what remains open for a TRULY
 * GENERIC consumer (arbitrary `a`, arbitrary `consume`) at FULL multi-
 * chunk generality (no boundary restriction). `theorem_stream_consume_
 * single_chunk` above is generic in `a` but SINGLE-chunk only (pure
 * algebra, one collapsing-to-empty operand); `theorem_stream_consume_
 * dataset_eq_batch` above is FULLY multi-chunk general but ONE fixed `a`
 * (`rdf_dataset` via `dataset_consume`). Closing the product of both --
 * generic `a` AND full multi-chunk generality -- needs the SAME per-line
 * witness-chain apparatus this file built for `parse_nquads_acc`/`lw_ds_
 * step`/`chain_ds_fold` (lines ~1150-1820 above), GENERICISED over `a`/
 * `consume`:
 *   1. `lw_generic_step (#a) (consume : a -> qquad -> a) (mid : string)
 *      (w : line_witness) (acc : a) : a` -- mirrors `lw_ds_step` exactly,
 *      substituting `consume acc (g, t)` for `dataset_add_quad ds t g` in
 *      the `LW_QuadOk` case; identity in the other three cases, unchanged.
 *   2. `chain_generic_fold (#a) consume (mid : string) (ws : list line_
 *      witness) (acc : a) : Tot a` -- mirrors `chain_ds_fold`.
 *   3. Generic analogues of the FOUR per-kind step-shift lemmas (`lemma_
 *      parse_nquads_acc_{blank,comment,quad_fail,quad_ok}_step_shift`),
 *      `_restart`, `_full_via_chain`, and `lemma_parse_nquads_acc_concat_
 *      line_general` itself -- for `fold_nquads_acc`+`lw_generic_step`
 *      instead of `parse_nquads_acc`+`lw_ds_step`.
 * WHY THIS IS "ONLY" MECHANICAL, NOT A NEW WALL: every position/outcome
 * fact these lemmas depend on (`lemma_pws_shift`, `lemma_byte_index_at_
 * middle`, `lemma_skip_eol_shift`, `lemma_skip_comment_shift`, `lemma_nq_
 * skip_line_shift_exact`, `Parser.NTriples.Locality.lemma_parse_nquad_
 * shift_generic`, every `*_wf` predicate) talks ONLY about POSITIONS and
 * PARSER outcomes (`pws`/`skip_eol`/`parse_nquad`/...) -- NONE of them
 * mention `ds`/`rdf_dataset`/`dataset_add_quad` at all. The `#push-options`
 * + one-step-unfold technique each step-shift lemma uses (see `lemma_
 * parse_nquads_acc_blank_step_shift`'s own banner) applies identically to
 * `fold_nquads_acc`'s definitional equation, since (per `fold_nquads_acc_
 * eq_parse_nquads_acc` above) that equation is branch-for-branch identical
 * to `parse_nquads_acc`'s. WHY IT WAS NOT ATTEMPTED THIS LANDING: it is
 * roughly FOUR step-shift lemmas + a restart lemma + a full-via-chain
 * lemma + the concat-line-general lemma, each a close copy of an already-
 * proved original but each still needing its OWN z3 run at the SAME
 * z3rlimit budget those originals needed (150-600) -- a second full pass
 * through the same ~670-line apparatus, assessed (per this task's own
 * guard-depth-3 discipline and the file's established precedent of
 * scoping to what a session can actually clear -- see the MULTI-CHUNK
 * `theorem_stream_eq_batch` banner above making the identical call re:
 * `chain_append`'s dataset-fold companion) as a separate landing's worth
 * of work, not a same-session extension. `dataset_consume`'s full-
 * generality result above already demonstrates every ingredient (the
 * position/outcome facts) needed to close the general case is dataset-
 * agnostic and already proved -- only the mechanical duplication remains.
 * ============================================================================ *)
