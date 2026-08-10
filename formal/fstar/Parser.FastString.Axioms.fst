module Parser.FastString.Axioms

module Spec = Parser.FastString.Spec
open Parser.FastString
open FStar.List.Tot

// ============================================================================
// Companion implementation of Parser.FastString.Axioms.fsti -- G4/#358
// Step 4 of the FastString re-founding migration
// (docs/designissues/2026-08-10-faststring-refounding-plan.md).
//
// Every `val` in the `.fsti` is proved here from the REAL definitions in
// Parser.FastString.Spec.fst, reached via Parser.FastString.fsti's
// bridging lemmas (fs_byte_length_eq and siblings) -- no `friend`, no new
// `assume val`, no `admit`. The `.fsti`'s own banner records the one
// deviation this landing made from "byte-identical": fact 6
// (`fs_cp_at_ascii`) was FOUND FALSE as originally stated (a genuine,
// machine-checked counterexample, not a proof-technique limitation --
// see that val's banner in the .fsti), and its `requires` clause gained
// one missing conjunct (`pos < fs_byte_length s`). Every other val here
// is exactly the original axiom, now a theorem.
//
// PROOF STRATEGY, PER FACT. Each proof:
//   1. Invokes the relevant `fs_*_eq` bridging lemma(s) from
//      Parser.FastString.fsti to rewrite the `fs_*` primitive into its
//      Parser.FastString.Spec formula.
//   2. Discharges the resulting Spec-level goal using Spec.fst's own
//      lemma kit (utf8_bytes_concat, utf8_decode_at_ascii,
//      utf8_decode_encode_identity, utf8_decode_at_shift, ...) plus a
//      small set of list-level helper lemmas proved locally below
//      (nth_byte/drop_bytes/take_bytes distribute-over-append facts that
//      Spec.fst does not itself need for its own lemma kit).
//
// `assert_norm` NOTE. `Spec.utf8_bytes s = List.Tot.concatMap
// utf8_enc_char (FStar.String.list_of_string s)` is a plain (non-
// recursive-on-its-argument-in-the-relevant-sense-here) definition, but
// Z3 does not unfold it automatically at a LITERAL string argument (e.g.
// `Spec.utf8_bytes ""`) via a bare `assert` -- confirmed empirically
// (Error 19) while building this file. `assert_norm`, which runs F*'s
// own normalizer (delta+zeta+iota+primops) before handing anything to
// Z3, closes it in one step: `list_of_string ""` reduces to `[]` via the
// normalizer's native string-literal handling (documented in
// FStar.String.fsti's module comment: "string literals ... handled by
// F*'s normalizers"), and `concatMap _ []` then reduces to `[]`
// structurally. Every literal-string fact below (`fs_byte_length_empty`)
// uses this.
// ============================================================================

// ----------------------------------------------------------------------
// Local helper lemmas -- list-level facts about Parser.FastString.Spec's
// byte-list primitives (nth_byte / drop_bytes / take_bytes) that this
// module's proofs need but Spec.fst's own lemma kit does not state,
// because Spec.fst had no consumer needing them until now. Proof-only,
// standard structural induction, no new axioms.
// ----------------------------------------------------------------------

/// Reading a concatenation below the left operand's length reads the
/// left operand directly -- the complement of Spec.nth_byte_append
/// (which handles the "at or past the left operand's length" case).
let rec nth_byte_append_left (a b : list Spec.byte) (i : nat)
  : Lemma (requires i < length a)
          (ensures Spec.nth_byte (a @ b) i == Spec.nth_byte a i)
  =
  match a with
  | hd :: tl -> if i = 0 then () else nth_byte_append_left tl b (i - 1)

/// `drop_bytes` never grows a list past its own length below the cut
/// point: dropping `n <= length bs` bytes leaves exactly `length bs - n`.
let rec drop_bytes_length (bs : list Spec.byte) (n : nat)
  : Lemma (requires n <= length bs)
          (ensures length (Spec.drop_bytes bs n) == length bs - n)
  =
  match bs with
  | [] -> ()
  | hd :: tl -> if n = 0 then () else drop_bytes_length tl (n - 1)

/// Dropping a prefix of a concatenation that lies wholly inside the left
/// operand leaves the undropped tail of the left operand followed by all
/// of the right operand untouched.
let rec drop_bytes_append_left (a b : list Spec.byte) (start : nat)
  : Lemma (requires start <= length a)
          (ensures Spec.drop_bytes (a @ b) start == Spec.drop_bytes a start @ b)
  =
  match a with
  | [] -> ()
  | hd :: tl -> if start = 0 then () else drop_bytes_append_left tl b (start - 1)

/// Dropping past the whole left operand of a concatenation is the same
/// as dropping the (shifted) remainder from the right operand alone.
let rec drop_bytes_append_right (a b : list Spec.byte) (start : nat)
  : Lemma (requires start >= length a)
          (ensures Spec.drop_bytes (a @ b) start == Spec.drop_bytes b (start - length a))
  =
  match a with
  | [] -> ()
  | hd :: tl -> drop_bytes_append_right tl b (start - 1)

/// Taking a prefix of a concatenation that lies wholly inside the left
/// operand is the same as taking that prefix of the left operand alone.
let rec take_bytes_append_left (a b : list Spec.byte) (n : nat)
  : Lemma (requires n <= length a)
          (ensures Spec.take_bytes (a @ b) n == Spec.take_bytes a n)
  =
  match a with
  | [] -> ()
  | hd :: tl -> if n = 0 then () else take_bytes_append_left tl b (n - 1)

/// Taking exactly a list's own length back out returns the list itself.
let rec take_bytes_self (bs : list Spec.byte)
  : Lemma (Spec.take_bytes bs (length bs) == bs)
  =
  match bs with
  | [] -> ()
  | hd :: tl -> take_bytes_self tl

/// An in-bounds index always reads `Some` byte, never `None`.
let rec nth_byte_some_of_lt (bs : list Spec.byte) (i : nat)
  : Lemma (requires i < length bs)
          (ensures Some? (Spec.nth_byte bs i))
  =
  match bs with
  | hd :: tl -> if i = 0 then () else nth_byte_some_of_lt tl (i - 1)

// ----------------------------------------------------------------------
// Facts 1-5, 7: proved directly from the bridging lemmas plus Spec.fst's
// own lemma kit and the local helpers above.
// ----------------------------------------------------------------------

let fs_byte_length_empty () =
  fs_byte_length_eq "";
  assert_norm (Spec.utf8_bytes "" == [])

let fs_byte_length_concat a b =
  fs_byte_length_eq (a ^ b);
  fs_byte_length_eq a;
  fs_byte_length_eq b;
  Spec.utf8_bytes_concat a b;
  FStar.List.Tot.append_length (Spec.utf8_bytes a) (Spec.utf8_bytes b)

let fs_byte_length_ascii_singleton s c =
  fs_byte_length_eq s;
  Spec.utf8_bytes_ascii_singleton s c

let fs_byte_at_concat a b i =
  fs_byte_length_eq (a ^ b);
  fs_byte_length_eq a;
  fs_byte_at_eq (a ^ b) i;
  fs_byte_at_eq a i;
  Spec.utf8_bytes_concat a b;
  if i < fs_byte_length a then
    nth_byte_append_left (Spec.utf8_bytes a) (Spec.utf8_bytes b) i
  else begin
    fs_byte_length_eq b;
    fs_byte_at_eq b (i - fs_byte_length a);
    Spec.nth_byte_append (Spec.utf8_bytes a) (Spec.utf8_bytes b) (i - fs_byte_length a)
  end

let fs_byte_sub_concat_left a b start len =
  fs_byte_length_eq a;
  fs_byte_sub_eq (a ^ b) start len;
  fs_byte_sub_eq a start len;
  Spec.utf8_bytes_concat a b;
  drop_bytes_append_left (Spec.utf8_bytes a) (Spec.utf8_bytes b) start;
  drop_bytes_length (Spec.utf8_bytes a) start;
  take_bytes_append_left (Spec.drop_bytes (Spec.utf8_bytes a) start) (Spec.utf8_bytes b) len

let fs_byte_sub_concat_right a b start len =
  fs_byte_length_eq a;
  fs_byte_sub_eq (a ^ b) start len;
  fs_byte_sub_eq b (start - fs_byte_length a) len;
  Spec.utf8_bytes_concat a b;
  drop_bytes_append_right (Spec.utf8_bytes a) (Spec.utf8_bytes b) start

/// Fact 6 (NARROWED, see the .fsti's banner on this val for the full
/// counterexample this landing found and the justification for the
/// added `pos < fs_byte_length s` hypothesis). With that hypothesis,
/// `Spec.nth_byte` at `pos` is guaranteed `Some`, so `fs_byte_at` and
/// `fs_cp_at` read the SAME byte, and `Spec.utf8_decode_at_ascii`
/// (Spec.fst's own lemma kit) closes the rest.
let fs_cp_at_ascii s pos =
  fs_byte_length_eq s;
  fs_byte_at_eq s pos;
  fs_cp_at_eq s pos;
  nth_byte_some_of_lt (Spec.utf8_bytes s) pos;
  match Spec.nth_byte (Spec.utf8_bytes s) pos with
  | Some b0 -> Spec.utf8_decode_at_ascii (Spec.utf8_bytes s) pos b0

let fs_byte_at_ascii_singleton s c =
  fs_byte_at_eq s 0;
  Spec.utf8_bytes_ascii_singleton s c

// ----------------------------------------------------------------------
// Fact 8 (`fs_byte_sub_self`): needs `Parser.FastString.Spec.fst`'s
// "single-decoder round trip" theorem -- `utf8_decode_all (utf8_bytes s)
// == FStar.String.list_of_string s` for every `s` -- which that file's
// own banner records as ATTEMPTED AND PARKED after three failed tries,
// all stalling on getting `utf8_decode_all_aux`'s recursive definition
// to unfold at a fully symbolic call site (the closure-identity /
// cross-boundary-unfold obstruction class, skills/proof-factory/
// SKILL.md). Proved here via the concrete next step that file's own
// banner names: an explicit UNFOLD LEMMA restating
// `utf8_decode_all_aux`'s defining equation as a `val`/`let ... = ()`
// pair (so F* proves the unfold ONCE, non-recursively, at the point of
// definition, rather than asking Z3 to fire the recursive axiom at a
// symbolic call site inside a separate induction), then TWO structural
// inductions built on top of it:
//   - `lemma_decode_all_aux_shift`: `utf8_decode_all_aux` is
//     prefix-oblivious (decoding `prefix @ suffix` starting at
//     `length prefix + pos` is identical to decoding `suffix` from
//     `pos`) -- induction on `length suffix - pos`, mirroring the
//     function's own `decreases`, using the unfold lemma once per step
//     plus `Spec.utf8_decode_at_shift` (already proved in Spec.fst) for
//     the one-position read.
//   - `lemma_decode_all_aux_encode`: decoding the UTF-8 encoding of a
//     char list `cs` followed by arbitrary `rest`, starting from an
//     arbitrary accumulator `acc`, reduces to decoding `rest` alone with
//     accumulator `List.Tot.rev_acc cs acc` -- induction on `cs`,
//     peeling one char at a time with `Spec.utf8_decode_encode_identity`
//     (Spec.fst) supplying the one-character decode-encode fact and
//     `lemma_decode_all_aux_shift` supplying the "skip past this
//     char's own encoding" step. Stated with `List.Tot.rev_acc` (not
//     `List.Tot.rev _ @ _`) specifically because `rev_acc`'s OWN
//     recursive equation (`rev_acc (hd::tl) acc == rev_acc tl (hd::acc)`)
//     is syntactically identical to the accumulator step the induction
//     performs -- no `append_assoc`/`rev` lemmas needed inside the
//     induction itself, only at the final wrap-up below.
// The wrap-up (`utf8_decode_all_utf8_bytes_identity`) instantiates
// `lemma_decode_all_aux_encode` at `rest = []`, `acc = []` and closes
// with `List.Tot.append_l_nil` (`enc @ [] == enc`) and
// `List.Tot.rev_involutive` (`rev (rev cs) == cs`, since `rev_acc cs []
// == rev cs` by `rev`'s own definition and the base case of
// `utf8_decode_all_aux` applies its own outer `rev`).
//
// This theorem is a genuine, reusable finding beyond fact 8 itself: it
// is the exact "single-decoder round trip" statement Parser.FastString.
// Spec.fst's banner names as the closest achievable unconditional
// version of the file's SINGLE-DECODER FINDING (issue #374). Recorded in
// `docs/designissues/2026-08-10-faststring-refounding-plan.md`'s Step 4
// entry and `docs/designissues/2026-08-10-string-foundation-decision.md`
// (gap 4, "the parked decode-encode theorem") -- both should be read as
// UPDATED by this landing, not merely referencing it.
// ----------------------------------------------------------------------

/// Non-recursive restatement of `Spec.utf8_decode_all_aux`'s own
/// defining equation, with an explicit `pos < blen` hypothesis (so the
/// `if` in the real definition is resolved once, here, rather than left
/// for a later symbolic call site to re-derive). `= ()` because this IS
/// the function's own body, verbatim, under the same hypothesis its
/// `else` branch is guarded by.
val utf8_decode_all_aux_unfold (bs : list Spec.byte) (blen pos : nat) (acc : list FStar.Char.char)
  : Lemma (requires pos < blen)
          (ensures
            Spec.utf8_decode_all_aux bs blen pos acc ==
            (let (cp, adv) = Spec.utf8_decode_at bs pos in
             let advn : nat = if adv = 0 then 1 else adv in
             let next : nat = pos + advn in
             if next > blen then FStar.List.Tot.rev acc
             else
               let c : FStar.Char.char =
                 if cp >= 0 && cp < 0xd7ff then FStar.Char.char_of_int cp
                 else if cp >= 0xe000 && cp <= 0x10ffff then FStar.Char.char_of_int cp
                 else FStar.Char.char_of_int 0xFFFD
               in
               Spec.utf8_decode_all_aux bs blen next (c :: acc)))
let utf8_decode_all_aux_unfold bs blen pos acc = ()

/// `utf8_decode_all_aux` is prefix-oblivious: decoding `prefix @ suffix`
/// from position `length prefix + pos` is identical to decoding
/// `suffix` alone from `pos`. Induction on `length suffix - pos`,
/// mirroring `utf8_decode_all_aux`'s own `decreases`.
let rec lemma_decode_all_aux_shift (prefix suffix : list Spec.byte) (pos : nat) (acc : list FStar.Char.char)
  : Lemma (requires pos <= length suffix)
          (ensures
            Spec.utf8_decode_all_aux (prefix @ suffix) (length prefix + length suffix) (length prefix + pos) acc
            == Spec.utf8_decode_all_aux suffix (length suffix) pos acc)
    (decreases (length suffix - pos))
  =
  if pos >= length suffix then ()
  else begin
    Spec.utf8_decode_at_shift prefix suffix pos;
    utf8_decode_all_aux_unfold (prefix @ suffix) (length prefix + length suffix) (length prefix + pos) acc;
    utf8_decode_all_aux_unfold suffix (length suffix) pos acc;
    let (cp, adv) = Spec.utf8_decode_at suffix pos in
    let advn : nat = if adv = 0 then 1 else adv in
    let next : nat = pos + advn in
    if next > length suffix then ()
    else begin
      let c : FStar.Char.char =
        if cp >= 0 && cp < 0xd7ff then FStar.Char.char_of_int cp
        else if cp >= 0xe000 && cp <= 0x10ffff then FStar.Char.char_of_int cp
        else FStar.Char.char_of_int 0xFFFD
      in
      lemma_decode_all_aux_shift prefix suffix next (c :: acc)
    end
  end

/// Decoding the UTF-8 encoding of `cs` followed by `rest`, starting from
/// accumulator `acc`, is the same as decoding `rest` alone starting from
/// accumulator `List.Tot.rev_acc cs acc`. Induction on `cs`: peel `hd`
/// off, use `Spec.utf8_decode_encode_identity` to decode its own
/// encoding in one step, then `lemma_decode_all_aux_shift` to skip past
/// it and land on `tl`'s encoding at position 0.
let rec lemma_decode_all_aux_encode (cs : list FStar.Char.char) (rest : list Spec.byte) (acc : list FStar.Char.char)
  : Lemma
      (ensures
        Spec.utf8_decode_all_aux
          (List.Tot.concatMap Spec.utf8_enc_char cs @ rest)
          (length (List.Tot.concatMap Spec.utf8_enc_char cs) + length rest)
          0
          acc
        == Spec.utf8_decode_all_aux rest (length rest) 0 (List.Tot.rev_acc cs acc))
    (decreases cs)
  =
  match cs with
  | [] -> ()
  | hd :: tl ->
    let enc_hd = Spec.utf8_enc_char hd in
    let enc_tl = List.Tot.concatMap Spec.utf8_enc_char tl in
    List.Tot.append_assoc enc_hd enc_tl rest;
    let full_bytes = enc_hd @ (enc_tl @ rest) in
    let blen = length enc_hd + (length enc_tl + length rest) in
    Spec.utf8_decode_encode_identity hd (enc_tl @ rest);
    Spec.utf8_enc_char_len_bounds hd;
    utf8_decode_all_aux_unfold full_bytes blen 0 acc;
    lemma_decode_all_aux_shift enc_hd (enc_tl @ rest) 0 (hd :: acc);
    lemma_decode_all_aux_encode tl rest (hd :: acc)

/// THE SINGLE-DECODER ROUND TRIP (Parser.FastString.Spec.fst's own
/// banner, "ATTEMPTED, PARKED" -- landed here). `Spec.utf8_bytes`
/// (encode via `list_of_string` + `utf8_enc_char`) and
/// `Spec.utf8_decode_all` (decode via `utf8_decode_at`, repeatedly) are
/// genuine inverses for EVERY string, not merely valid-UTF-8 ones (the
/// codepoint-level round trip is unconditional; it is only the BYTE-level
/// equivalence with a hypothetical "any raw byte buffer" decoder that
/// issue #374's SINGLE-DECODER FINDING rules out, and this theorem does
/// not claim that).
let utf8_decode_all_utf8_bytes_identity (s : string)
  : Lemma (Spec.utf8_decode_all (Spec.utf8_bytes s) == FStar.String.list_of_string s)
  =
  let cs = FStar.String.list_of_string s in
  let enc = List.Tot.concatMap Spec.utf8_enc_char cs in
  List.Tot.append_l_nil enc;
  lemma_decode_all_aux_encode cs [] [];
  List.Tot.rev_involutive cs

let fs_byte_sub_self s =
  fs_byte_length_eq s;
  fs_byte_sub_eq s 0 (fs_byte_length s);
  take_bytes_self (Spec.utf8_bytes s);
  utf8_decode_all_utf8_bytes_identity s;
  FStar.String.string_of_list_of_string s
