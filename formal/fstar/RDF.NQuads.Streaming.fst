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
 * FINDING (guard-depth-3 stop, per CLAUDE.md/subagent-prompting discipline)
 * -- `theorem_stream_eq_batch` is NOT proved in this landing.
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
 *   1. `fs_byte_index_concat` -- does NOT exist yet. `Parser.FastString.
 *      fsti` bridges `fs_byte_length`, `fs_byte_at`, `fs_byte_sub`,
 *      `fs_find_byte`, `fs_cp_at`, `fs_cp_len` to `Parser.FastString.Spec`
 *      via `_eq` lemmas (used by the ALREADY-PROVED `fs_byte_at_concat` /
 *      `fs_byte_sub_concat_left` / `fs_byte_sub_concat_right` in `Parser.
 *      FastString.Axioms.fst`) -- but `fs_byte_index` (the char-returning
 *      convenience wrapper `parse_nquads_acc` actually calls) has NO such
 *      bridging lemma exposed. One would need to be added (trivially
 *      provable, `fs_byte_index_eq`, mirroring the existing six) as a
 *      genuinely additive `val`+`let` pair in `Parser.FastString.fst`/
 *      `.fsti` -- not attempted here since it is a change to a module
 *      outside this task's stated scope (`Parser.NQuads.fst`), and
 *      touching it deserves its own reviewed, narrowly-scoped landing.
 *   2. A LOCALITY lemma for `parse_subject` / `parse_iri` / `parse_object`
 *      (and their full call graph through `Parser.Combinators.fst`'s
 *      `ptake_while` / `pquoted_string` / etc.): that each behaves
 *      IDENTICALLY on `complete ^ carry` at any position `p < fs_byte_length
 *      complete` as it does on `complete` alone -- both control flow
 *      (which branch is taken) AND extracted VALUES (every `fs_byte_sub`
 *      call inside a still-open line targets a range wholly inside
 *      `complete`, so `fs_byte_sub_concat_left` supplies the value
 *      equality, but ONLY once fact 1 supplies the byte-index agreement
 *      that lets the SAME branches even be reached). This is a
 *      per-combinator induction across a 1300+ line module, not a single
 *      lemma -- the honest size estimate is closer to the scope of a
 *      SEPARATE landing than a same-session extension of this one.
 *
 * NARROWEST VERIFIED CHECKPOINT: `split_complete_lines` and its five
 * lemmas above (`split_complete_lines_reconstruct`, `_carry_no_nl`,
 * `_no_newline`, `_extend_carry`, `_ends_in_newline`), plus `stream_parse_
 * single_chunk_shape`'s definitional rewrite -- all verify under `make
 * RDF.NQuads.Streaming.fst.checked` with no admits, no `--lax`, no new
 * `assume val`.
 *
 * NEXT NARROWEST UNPROVED STATEMENT: `fs_byte_index_eq` in `Parser.
 * FastString.fst`/`.fsti` (item 1 above) -- small, mechanical, and the
 * gating step before item 2's much larger locality effort can even be
 * attempted meaningfully.
 * ============================================================================ *)
