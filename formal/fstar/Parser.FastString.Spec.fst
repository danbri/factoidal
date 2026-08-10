module Parser.FastString.Spec

(* ============================================================================
 * Parser.FastString.Spec -- UTF-8 codec, spec-level.
 *
 * MIGRATION CONTEXT
 * ------------------
 * Step 1 of the FastString re-founding migration (owner-approved plan:
 * docs/designissues/2026-08-10-faststring-refounding-plan.md). This module
 * gives the fs_* primitives declared in Parser.FastString a DEFINITIONAL
 * semantics: a pure, provably-total UTF-8 codec over `list byte`. Steps 2-3
 * (not in this module) will re-found `Parser.FastString.fsti` on top of it --
 * assume vals become Spec-backed lets, with today's fast OCaml kept alive as
 * a rule-11(b) Option-B realisation patch (extracted spec functions under
 * `fs_*_spec` names; the patch overrides `fs_*` with the current bodies;
 * deletability = delete the patch and the spec bodies take over, slower
 * never wrong).
 *
 * This module is ADDITIVE and PROOF-ONLY:
 *   - not wired into build-ocaml.sh's module list (no extraction target);
 *   - Parser.FastString.fst and its consumers are UNTOUCHED by this commit.
 *
 * MIRRORING CLAIM (`utf8_decode_at`)
 * -----------------------------------
 * `utf8_decode_at` mirrors `fs_cp_at_impl` in
 * formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
 * 89_fast_string_primitives.sh (lines ~159-225) BRANCH FOR BRANCH:
 *
 *   - ASCII fast case (b0 < 0x80)                            -> (b0, 1)
 *   - lead byte too low for a valid 2-byte form (b0 < 0xC2)   -> reject
 *   - 2-byte form (0xC2 <= b0 < 0xE0): continuation check on b1.
 *     b0 >= 0xC2 already rules out the overlong 0xC0/0xC1 leads, so no
 *     separate overlong check is needed here (cp lands in [0x80, 0x7FF]).
 *   - 3-byte form (0xE0 <= b0 < 0xF0): continuation checks on b1, b2;
 *     reject overlong (cp < 0x800) and surrogates (0xD800-0xDFFF).
 *   - 4-byte form (0xF0 <= b0 < 0xF5): continuation checks on b1, b2, b3;
 *     reject overlong (cp < 0x10000) and out-of-range (cp > 0x10FFFF).
 *   - lead byte too high (b0 >= 0xF5)                         -> reject
 *
 * Every rejection returns (0xFFFD, 1) -- the Unicode replacement character
 * with advance 1. This is the TERMINATION GUARANTEE: advance is always
 * >= 1 regardless of how malformed the input is, so a caller that repeatedly
 * decodes-and-advances always makes forward progress and the remaining
 * length strictly decreases.
 *
 * Byte-mask arithmetic below uses `%` (mod) and `*`/`+` instead of bitwise
 * `land`/`lor`/`lsl`: the OCaml impl's `x land M` / `x lor y` / `x lsl n`
 * are used only in disjoint-bit-range positions here (continuation-byte
 * low 6 bits, lead-byte low 5/4/3 bits, shift-and-combine reassembly), so
 * `x % (M+1)` and `hi * (1 lsl n) + lo` are the same values -- and `%`/`*`/
 * `+` are what F*'s SMT-backed nat arithmetic reasons about directly,
 * without needing a bitvector theory or FStar.UInt lemmas.
 * ============================================================================ *)

open FStar.Mul
open FStar.List.Tot

(* A single UTF-8 code unit. *)
type byte = n:nat{n < 256}

(* A UTF-8 continuation byte: 10xxxxxx. *)
let is_continuation (b:byte) : bool = (b >= 0x80) && (b < 0xC0)

(* -------------------------------------------------------------------- *)
(* Encoder: char -> list byte, RFC 3629 case split by codepoint range.   *)
(* -------------------------------------------------------------------- *)

val utf8_enc_char (c:FStar.Char.char) : Tot (list byte)
let utf8_enc_char c =
  let cp = FStar.Char.int_of_char c in
  // DEFENSIVE CLAMP (issue #374 finding, single-decoder banner below).
  // `cp : nat`, and for every GENUINE FStar.Char.char, F*'s own
  // char_code refinement guarantees 0 <= cp < 0xD7FF or
  // 0xE000 <= cp <= 0x10FFFF -- so this branch is UNREACHABLE in the
  // LOGIC for any char this module ever constructs, and the existing
  // proofs below (utf8_decode_encode_identity etc.) discharge it as
  // such. It exists because extraction erases that refinement: `cp`'s
  // OCaml/Z.t runtime value can be poisoned by `list_of_string`
  // (ulib's own decoder, used by `utf8_bytes` below) when handed a
  // non-well-formed OCaml string bypassing F*'s type discipline --
  // list_of_string's BatUTF8-backed realisation is not actually total
  // w.r.t. that guarantee on such input (confirmed empirically: it
  // returns negative and out-of-range ints for malformed UTF-8 byte
  // runs). Left unclamped, a poisoned `cp` used to flow straight into
  // the returned `list byte` as an out-of-range "byte", then on into
  // Parser.FastString.fst's fs_byte_sub / FStar.String.string_of_list,
  // whose `BatUChar.chr` call throws `BatUChar.Out_of_range` -- an
  // uncaught crash, not merely a wrong number (issue #374). Clamping
  // HERE, at the encode boundary, stops the poison at its source
  // instead of chasing it through every downstream consumer.
  if cp < 0 || cp > 0x10FFFF || (cp >= 0xD800 && cp < 0xE000) then
    [ 0xEF; 0xBF; 0xBD ]                    // UTF-8 encoding of U+FFFD
  else if cp < 0x80 then
    [ cp ]
  else if cp < 0x800 then
    [ 0xC0 + (cp / 0x40);
      0x80 + (cp % 0x40) ]
  else if cp < 0x10000 then
    [ 0xE0 + (cp / 0x1000);
      0x80 + ((cp / 0x40) % 0x40);
      0x80 + (cp % 0x40) ]
  else
    [ 0xF0 + (cp / 0x40000);
      0x80 + ((cp / 0x1000) % 0x40);
      0x80 + ((cp / 0x40) % 0x40);
      0x80 + (cp % 0x40) ]

(* -------------------------------------------------------------------- *)
(* utf8_bytes : string -> list byte, via concatMap over list_of_string.  *)
(* -------------------------------------------------------------------- *)
(*
 * SINGLE-DECODER FINDING (issue #374, 2026-08-10). Full elimination of
 * `list_of_string` from this definition -- i.e. making `utf8_bytes`
 * decode EVERY string exclusively through `utf8_decode_at`, on ALL
 * input including non-well-formed byte buffers -- is IMPOSSIBLE inside
 * plain F* without a new `assume val`, and this is not a design choice
 * this module can improve on. The argument, checked against the actual
 * F*/ulib sources rather than assumed:
 *
 *   1. `FStar.String.char` (ulib, FStar.Char.fsti) is a `new val
 *      char:eqtype` -- a genuinely ABSTRACT type, opaque to F*'s logic
 *      except through `int_of_char`/`char_of_int`/`u32_of_char`/
 *      `char_of_u32`. The ONLY way to observe a `string`'s content at
 *      all, for ANY string -- valid or not -- is `list_of_string :
 *      string -> Tot (list char)` (FStar.String.fsti). Every other
 *      string primitive (`length`, `index`, `get`, `sub`) is defined
 *      IN TERMS OF `list_of_string` (`strlen s = List.length
 *      (list_of_string s)`). There is no byte-level accessor anywhere
 *      in FStar.String -- confirmed by reading the .fsti directly, not
 *      inferred.
 *   2. `list_of_string`'s OCaml realisation (`FStar_String.ml`:
 *      `BatList.init (BatUTF8.length s) (fun i -> BatUChar.code
 *      (BatUTF8.get s i))`) is NOT actually total w.r.t. the type
 *      `list char` it is DECLARED to return, on a `string` value that
 *      does not correspond to any real Unicode text -- confirmed
 *      empirically (a standalone probe linking `fstar.lib` directly,
 *      not inferred from the equivalence test's crash alone): decoding
 *      "abc:\xE6\x80\x97\xA5:xyz" through BatUTF8 returns the codepoint
 *      list [97;98;99;58;24599;-1670;120;121;122] -- a NEGATIVE
 *      "codepoint" (-1670) that violates `int_of_char : char -> nat`'s
 *      own postcondition. This is a genuine extraction-soundness gap
 *      in ulib's OCaml backend for this domain, not a bug this module
 *      introduced, and not one it can fix (BatUTF8 is third-party,
 *      outside the verified boundary).
 *   3. Consequence: `utf8_bytes` cannot be redefined to avoid
 *      `list_of_string` while still accepting an arbitrary `string`
 *      and returning a real byte list -- there is no OTHER F* Tot
 *      primitive that observes a string's content. Adding one would be
 *      exactly a NEW `assume val`, which this landing's task brief
 *      forbids and which iron rule #3(b) requires an open issue for
 *      even if allowed.
 *
 * WHAT THIS LANDING DOES INSTEAD -- fixes the part of the problem that
 * actually IS ours: the poisoned codepoint from (2) used to propagate
 * UNCLAMPED through `utf8_enc_char` (below) into `utf8_bytes`'s output
 * as an out-of-range "byte" (violating THIS module's OWN `byte =
 * n:nat{n<256}` type), and from there into `Parser.FastString.fst`'s
 * `fs_byte_sub` / `FStar.String.string_of_list`, whose `BatUChar.chr`
 * call THROWS `BatUChar.Out_of_range` -- an uncaught crash, confirmed
 * as the exact mechanism behind the equivalence test's rc=2 abort
 * (previously attributed only vaguely to "other adversarial inputs").
 * `utf8_enc_char`'s new defensive clamp (see its own comment) stops
 * that poison at the encode boundary -- provably dead code for any
 * GENUINE `FStar.Char.char` (unreachable per `char_code`'s own
 * refinement, so existing proofs are unaffected), but a real runtime
 * safety net once extraction has already let a poisoned value in. This
 * eliminates the CRASH. The remaining WRONG-VALUE divergences (bytes
 * genuinely miscounted relative to the fast realisation's raw byte
 * count, per finding (2) -- BatUTF8 silently drops/merges bytes on
 * malformed runs) are the residual documented at
 * docs/designissues/2026-08-10-faststring-refounding-plan.md and in
 * tests/unit/parser_fast_string_equivalence.ml's XFAIL rows: forced by
 * (1)+(2), not by anything fixable here.
 *)

val utf8_bytes (s:string) : Tot (list byte)
let utf8_bytes s = List.Tot.concatMap utf8_enc_char (FStar.String.list_of_string s)

(* -------------------------------------------------------------------- *)
(* Byte-list indexing (spec-level; O(n), not the fast path).             *)
(* -------------------------------------------------------------------- *)

let rec nth_byte (bs:list byte) (i:nat) : option byte =
  match bs with
  | [] -> None
  | hd :: tl -> if i = 0 then Some hd else nth_byte tl (i - 1)

val nth_byte_zero (hd:byte) (tl:list byte)
  : Lemma (nth_byte (hd :: tl) 0 == Some hd)
let nth_byte_zero hd tl = ()

val nth_byte_succ (hd:byte) (tl:list byte) (i:nat)
  : Lemma (nth_byte (hd :: tl) (i + 1) == nth_byte tl i)
let nth_byte_succ hd tl i = ()

(* nth_byte distributes over (@): reading at position (length a + k) in
   (a @ b) is the same as reading at position k in b directly. This is
   the SHIFT fact `utf8_decode_at_shift` (below) needs to relate a
   decode at a position inside a larger byte list to a decode of the
   suffix alone at position 0 -- the building block for the single-
   decoder round-trip theorem (`utf8_decode_all_utf8_bytes_identity`,
   end of this file's lemma kit). *)
val nth_byte_append (a b:list byte) (k:nat)
  : Lemma (nth_byte (a @ b) (List.Tot.length a + k) == nth_byte b k)
let rec nth_byte_append a b k =
  match a with
  | [] -> ()
  | hd :: tl -> nth_byte_append tl b k

(* -------------------------------------------------------------------- *)
(* utf8_decode_at : list byte -> pos:nat -> (nat & advn:pos)             *)
(* Mirrors fs_cp_at_impl branch-for-branch; see module banner.           *)
(* -------------------------------------------------------------------- *)

val utf8_decode_at (bs:list byte) (p:nat) : Tot (nat & pos)
let utf8_decode_at bs p =
  match nth_byte bs p with
  | None -> (0xFFFD, 1)
  | Some b0 ->
    if b0 < 0x80 then
      (b0, 1)
    else if b0 < 0xC2 then
      (0xFFFD, 1)
    else if b0 < 0xE0 then begin
      match nth_byte bs (p + 1) with
      | None -> (0xFFFD, 1)
      | Some b1 ->
        if not (is_continuation b1) then (0xFFFD, 1)
        else
          let cp = ((b0 % 0x20) * 0x40) + (b1 % 0x40) in
          (cp, 2)
    end
    else if b0 < 0xF0 then begin
      match nth_byte bs (p + 1), nth_byte bs (p + 2) with
      | Some b1, Some b2 ->
        if not (is_continuation b1) || not (is_continuation b2) then (0xFFFD, 1)
        else
          let cp = ((b0 % 0x10) * 0x1000) + ((b1 % 0x40) * 0x40) + (b2 % 0x40) in
          if cp < 0x800 || (cp >= 0xD800 && cp <= 0xDFFF) then (0xFFFD, 1)
          else (cp, 3)
      | _ -> (0xFFFD, 1)
    end
    else if b0 < 0xF5 then begin
      match nth_byte bs (p + 1), nth_byte bs (p + 2), nth_byte bs (p + 3) with
      | Some b1, Some b2, Some b3 ->
        if not (is_continuation b1) || not (is_continuation b2) || not (is_continuation b3)
        then (0xFFFD, 1)
        else
          let cp =
            ((b0 % 0x08) * 0x40000) + ((b1 % 0x40) * 0x1000) +
            ((b2 % 0x40) * 0x40) + (b3 % 0x40)
          in
          if cp < 0x10000 || cp > 0x10FFFF then (0xFFFD, 1)
          else (cp, 4)
      | _ -> (0xFFFD, 1)
    end
    else (0xFFFD, 1)

(* utf8_decode_at is POSITIONAL: its whole behaviour is determined by
   `nth_byte bs p`, `nth_byte bs (p+1)`, `nth_byte bs (p+2)`,
   `nth_byte bs (p+3)` (it never looks further, never looks at `bs`
   itself past those four reads). Consequence: decoding at position
   `length prefix + p` inside `prefix @ suffix` is IDENTICAL to
   decoding `suffix` at position `p` directly -- the prefix is inert.
   `nth_byte_append` supplies the four positional facts (p, p+1, p+2,
   p+3 all shift the same way); once those hold, both sides reduce
   through the SAME case split (same scrutinee values), so `()`
   closes it. This is the "single decoder is prefix-oblivious" fact
   the round-trip theorem below composes at every step of the walk. *)
val utf8_decode_at_shift (prefix suffix:list byte) (p:nat)
  : Lemma (utf8_decode_at (prefix @ suffix) (List.Tot.length prefix + p)
           == utf8_decode_at suffix p)
let utf8_decode_at_shift prefix suffix p =
  nth_byte_append prefix suffix p;
  nth_byte_append prefix suffix (p + 1);
  nth_byte_append prefix suffix (p + 2);
  nth_byte_append prefix suffix (p + 3)

(* -------------------------------------------------------------------- *)
(* drop_bytes / take_bytes / slice_bytes -- list-slicing helpers used by *)
(* fs_byte_sub's re-founded (Step 2/3) definition in Parser.FastString.  *)
(* Deliberately hand-written (not FStar.List.Tot.Base.splitAt) --        *)
(* fstar-module-style flags fixed-fuel/extraction-semantics traps on     *)
(* that combinator; these two are structurally trivial and match the    *)
(* existing fs_codepoints_of_string_aux `decreases` idiom already        *)
(* verified in this file's sibling module.                               *)
(* -------------------------------------------------------------------- *)

let rec drop_bytes (bs:list byte) (n:nat) : Tot (list byte) (decreases n) =
  match bs with
  | [] -> []
  | hd :: tl -> if n = 0 then bs else drop_bytes tl (n - 1)

let rec take_bytes (bs:list byte) (n:nat) : Tot (list byte) (decreases n) =
  match bs with
  | [] -> []
  | hd :: tl -> if n = 0 then [] else hd :: take_bytes tl (n - 1)

(* Byte-index slice, mirroring patch 89's fs_byte_sub clamp EXACTLY by
 * construction rather than by an explicit branch: drop_bytes past the
 * end of the list yields [], and take_bytes of [] yields [] regardless
 * of `len` -- the same "start > slen -> empty" / "start+len > slen ->
 * truncate to slen" clamps patch 89 computes explicitly with
 * `if i > slen then "" else let m = if i+n>slen then slen-i else n ...`. *)
val slice_bytes (bs:list byte) (start:nat) (len:nat) : Tot (list byte)
let slice_bytes bs start len = take_bytes (drop_bytes bs start) len

(* -------------------------------------------------------------------- *)
(* find_byte : list byte -> nat (byte value) -> nat (start) -> nat.      *)
(* Mirrors patch 89's fs_find_byte loop: scan every position from 0,     *)
(* only ACCEPT a match at idx >= start, and if nothing matches, return   *)
(* the full list length (== fs_byte_length s) -- same "not-found -> slen *)
(* regardless of how far start overshoots slen" behaviour as the OCaml   *)
(* `if i >= slen then slen else ...` loop, since idx always walks the    *)
(* full list here too.                                                   *)
(* -------------------------------------------------------------------- *)

let rec find_byte_scan (bs:list byte) (b:nat) (idx:nat) (start:nat) : Tot nat (decreases bs) =
  match bs with
  | [] -> idx
  | hd :: tl -> if idx >= start && hd = b then idx else find_byte_scan tl b (idx + 1) start

val find_byte (bs:list byte) (b:nat) (start:nat) : Tot nat
let find_byte bs b start = find_byte_scan bs b 0 start

(* -------------------------------------------------------------------- *)
(* utf8_decode_all : list byte -> list char.                             *)
(* Decode a WHOLE byte list into codepoints by repeated utf8_decode_at,  *)
(* exactly the loop shape already verified as                            *)
(* `Parser.FastString.fs_codepoints_of_string_aux` (same decreases        *)
(* idiom, same "invalid UTF-8 replaced by 0xFFFD" policy, same 0xD7FF    *)
(* caveat: this module sits BELOW Parser.FastString and therefore has no *)
(* access to `unsafe_char_of_d7ff`, so -- exactly like the existing,     *)
(* already-shipped fs_codepoints_of_string_aux -- codepoint U+D7FF       *)
(* decoded from raw bytes falls into the `else` branch and is replaced   *)
(* by U+FFFD rather than round-tripped exactly. This is not a new bug:   *)
(* it is the SAME pre-existing limitation this function's model already  *)
(* has, restated here because Spec cannot depend on Parser.FastString's  *)
(* assume val without a circular module dependency.                      *)
(* -------------------------------------------------------------------- *)

let rec utf8_decode_all_aux (bs:list byte) (blen:nat) (pos:nat) (acc:list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases (blen - pos))
  =
  if pos >= blen then FStar.List.Tot.rev acc
  else
    let (cp, adv) = utf8_decode_at bs pos in
    let advn : nat = if adv = 0 then 1 else adv in
    let next : nat = pos + advn in
    if next > blen then FStar.List.Tot.rev acc
    else
      // Defense-in-depth twin of utf8_enc_char's clamp above (issue
      // #374): `cp >= 0` is added to the first disjunct so a
      // poisoned/out-of-range cp can never reach FStar.Char.char_of_int
      // unclamped. Provably redundant once `bs` is `utf8_bytes`'s own
      // (now-clamped) output -- utf8_decode_at only ever returns 0xFFFD
      // or a codepoint it has itself range-checked -- but this function
      // takes an arbitrary `bs:list byte` per its signature, not only
      // `utf8_bytes`-produced ones, so the guard stays as a real
      // safety net rather than a provable-dead branch relied upon.
      let c : FStar.Char.char =
        if cp >= 0 && cp < 0xd7ff then FStar.Char.char_of_int cp
        else if cp >= 0xe000 && cp <= 0x10ffff then FStar.Char.char_of_int cp
        else FStar.Char.char_of_int 0xFFFD
      in
      utf8_decode_all_aux bs blen next (c :: acc)

val utf8_decode_all (bs:list byte) : Tot (list FStar.Char.char)
let utf8_decode_all bs = utf8_decode_all_aux bs (List.Tot.length bs) 0 []

(* -------------------------------------------------------------------- *)
(* is_cp_boundary : list byte -> nat -> bool                             *)
(* Position 0, end of the list, or a non-continuation byte.              *)
(* -------------------------------------------------------------------- *)

val is_cp_boundary (bs:list byte) (p:nat) : bool
let is_cp_boundary bs p =
  p = 0 || p >= List.Tot.length bs ||
  (match nth_byte bs p with
   | Some b -> not (is_continuation b)
   | None -> true)

(* ======================================================================
 * LEMMA KIT
 * ====================================================================== *)

(* 1. utf8_enc_char length bounds: every encoding is 1..4 bytes. *)
val utf8_enc_char_len_bounds (c:FStar.Char.char)
  : Lemma (1 <= List.Tot.length (utf8_enc_char c) /\ List.Tot.length (utf8_enc_char c) <= 4)
let utf8_enc_char_len_bounds c = ()

(* 2. utf8_bytes distributes over ^ (string concatenation). *)
val lemma_concatMap_append (#a #b:Type) (f: a -> Tot (list b)) (l1 l2: list a)
  : Lemma (List.Tot.concatMap f (l1 @ l2) == List.Tot.concatMap f l1 @ List.Tot.concatMap f l2)
let rec lemma_concatMap_append #a #b f l1 l2 =
  match l1 with
  | [] -> ()
  | hd :: tl ->
    lemma_concatMap_append f tl l2;
    List.Tot.append_assoc (f hd) (List.Tot.concatMap f tl) (List.Tot.concatMap f l2)

val utf8_bytes_concat (s1 s2:string)
  : Lemma (utf8_bytes (s1 ^ s2) == utf8_bytes s1 @ utf8_bytes s2)
let utf8_bytes_concat s1 s2 =
  FStar.String.list_of_concat s1 s2;
  lemma_concatMap_append utf8_enc_char (FStar.String.list_of_string s1) (FStar.String.list_of_string s2)

(* 3. ASCII singleton encode: utf8_bytes of a 1-ASCII-char string is
 *    exactly its codepoint, as a singleton byte list. Stated over any
 *    string s whose `list_of_string` is the singleton [c], rather than
 *    via `FStar.String.string_of_list`, so callers can discharge the
 *    hypothesis however is convenient at the use site (e.g. directly
 *    from `FStar.String.list_of_string_of_list`). *)
val utf8_bytes_ascii_singleton (s:string) (c:FStar.Char.char)
  : Lemma (requires FStar.String.list_of_string s == [c] /\ FStar.Char.int_of_char c < 0x80)
          (ensures utf8_bytes s == [ FStar.Char.int_of_char c ])
let utf8_bytes_ascii_singleton s c = ()

(* 4. utf8_decode_at on an ASCII head: decoding at a position whose byte
 *    is < 0x80 always yields (that byte, 1), independent of what
 *    follows -- the ASCII fast case never looks past b0. *)
val utf8_decode_at_ascii (bs:list byte) (p:nat) (b0:byte)
  : Lemma (requires nth_byte bs p == Some b0 /\ b0 < 0x80)
          (ensures utf8_decode_at bs p == (b0, 1))
let utf8_decode_at_ascii bs p b0 = ()

(* 5. Decode-encode identity: decoding at position 0 of
 *    (utf8_enc_char c) @ rest recovers exactly (codepoint of c,
 *    length (utf8_enc_char c)) -- for every valid char c, with
 *    arbitrary trailing bytes. Case split mirrors the encoder's own
 *    codepoint-range branches. *)
val utf8_decode_encode_identity (c:FStar.Char.char) (rest:list byte)
  : Lemma (utf8_decode_at (utf8_enc_char c @ rest) 0
           == (FStar.Char.int_of_char c, List.Tot.length (utf8_enc_char c)))
let utf8_decode_encode_identity c rest =
  let cp = FStar.Char.int_of_char c in
  if cp < 0x80 then begin
    // utf8_enc_char c == [cp]; (utf8_enc_char c) @ rest == cp :: rest.
    // nth_byte (cp :: rest) 0 == Some cp, and cp < 0x80 is the ASCII
    // fast case, decoded without touching `rest`.
    ()
  end
  else if cp < 0x800 then begin
    let b0 = 0xC0 + (cp / 0x40) in
    let b1 = 0x80 + (cp % 0x40) in
    // utf8_enc_char c == [b0; b1]; (utf8_enc_char c) @ rest == b0 :: b1 :: rest.
    // b0 is in [0xC2, 0xDF] (cp >= 0x80 rules out the 0xC0/0xC1 overlong
    // leads), landing the 2-byte branch; b1 is a continuation byte by
    // construction (0x80 + (cp % 0x40), and cp % 0x40 < 0x40).
    assert (0xC2 <= b0 /\ b0 < 0xE0);
    assert (is_continuation b1);
    assert (((b0 % 0x20) * 0x40) + (b1 % 0x40) == cp)
  end
  else if cp < 0x10000 then begin
    let b0 = 0xE0 + (cp / 0x1000) in
    let b1 = 0x80 + ((cp / 0x40) % 0x40) in
    let b2 = 0x80 + (cp % 0x40) in
    assert (0xE0 <= b0 /\ b0 < 0xF0);
    assert (is_continuation b1);
    assert (is_continuation b2);
    assert (((b0 % 0x10) * 0x1000) + ((b1 % 0x40) * 0x40) + (b2 % 0x40) == cp);
    // cp >= 0x800 (this branch) rules out the overlong reject; c's
    // codepoint is never a surrogate (FStar.Char.char_code excludes
    // [0xd7ff, 0xe000)), so the surrogate reject never fires either.
    assert (cp < 0xD800 \/ cp > 0xDFFF)
  end
  else begin
    let b0 = 0xF0 + (cp / 0x40000) in
    let b1 = 0x80 + ((cp / 0x1000) % 0x40) in
    let b2 = 0x80 + ((cp / 0x40) % 0x40) in
    let b3 = 0x80 + (cp % 0x40) in
    assert (0xF0 <= b0 /\ b0 < 0xF5);
    assert (is_continuation b1);
    assert (is_continuation b2);
    assert (is_continuation b3);
    assert (((b0 % 0x08) * 0x40000) + ((b1 % 0x40) * 0x1000) +
            ((b2 % 0x40) * 0x40) + (b3 % 0x40) == cp)
    // cp >= 0x10000 (this branch, and FStar.Char.char_code caps at
    // 0x10ffff) rules out both the overlong and out-of-range rejects.
  end

(* 6. SINGLE-DECODER ROUND TRIP -- ATTEMPTED, PARKED (issue #374).
 *    `utf8_decode_all (utf8_bytes s) == FStar.String.list_of_string s`
 *    for every s (encode via `utf8_enc_char` then decode via
 *    `utf8_decode_at` is a genuine inverse of `list_of_string`) would be
 *    the closest UNCONDITIONAL statement of "utf8_bytes's implicit
 *    decode agrees with the single decoder" provable inside F* -- see
 *    the SINGLE-DECODER FINDING banner above `utf8_bytes` for exactly
 *    where a STRONGER claim (agreement with `list_of_string`'s OWN
 *    internal algorithm on adversarial byte buffers) is categorically
 *    not available: `list_of_string` is an opaque ulib primitive with
 *    no algorithmic specification to match against.
 *
 *    Three attempts (`nth_byte_append` / `utf8_decode_at_shift` above
 *    are the reusable byproducts, both verify standalone and are used
 *    by nothing else yet): the induction needs `utf8_decode_all_aux`
 *    to unfold ONE STEP at a symbolic (non-literal) `bs`/`pos`/`acc`
 *    so that the already-established facts (`utf8_decode_at bs pos ==
 *    (int_of_char c, length (utf8_enc_char c))` via `utf8_decode_at_shift`
 *    + `utf8_decode_encode_identity`; `char_of_int (int_of_char c) == c`
 *    via `char_of_u32_of_char`; `int_of_char c`'s char_code range) can
 *    rewrite inside it. All three attempts stalled at Error 19 "Could
 *    not prove post-condition" on exactly that unfold step, even with
 *    every supporting fact asserted into context immediately beforehand
 *    -- this is the closure-identity/cross-boundary-unfold class
 *    documented in skills/proof-factory/SKILL.md ("a lambda in the
 *    engine module gets a different opaque symbol..."; here the
 *    obstruction is a recursive `let`'s own defining equation not
 *    firing at a fully symbolic call site, the analogous obstruction
 *    one level down). The fix that class of problem names -- a `norm
 *    [delta_only [...]; zeta; iota]` tactic step reducing
 *    `utf8_decode_all_aux bs blen pos acc` explicitly rather than
 *    relying on Z3's own unfolding -- was not attempted (three tries
 *    is this task's own stop rule); it is the concrete next step if
 *    this theorem is picked back up. Parked, not landed: main stays
 *    on the two verified fixes below (`utf8_enc_char`'s and
 *    `utf8_decode_all_aux`'s clamps), which are what eliminate the
 *    crash and are independent of this theorem. *)
