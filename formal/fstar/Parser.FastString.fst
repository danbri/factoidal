module Parser.FastString

open FStar.Char

// ============================================================================
// Byte-indexed string primitives for the parser hot path.
//
// STEP 2/3 RE-FOUNDING (2026-08-10; docs/designissues/
// 2026-08-10-faststring-refounding-plan.md). Before this landing, the six
// primitives below (fs_byte_length, fs_byte_at, fs_byte_sub, fs_find_byte,
// fs_cp_at, fs_cp_len) were `assume val`s -- acknowledged GAPs under iron
// rule #3(a), realised directly in OCaml
// (minimal_regrettable_glue_code_each_with_an_open_issue/
// 89_fast_string_primitives.sh) with ZERO F*-checked relationship to what
// they compute. They are now real DEFINITIONS over Parser.FastString.Spec's
// pure UTF-8 codec (`Parser.FastString.Spec.fst`, migration Step 1) --
// Parser.FastString is a genuine spec, not an acknowledged hole, and the
// six former GAPs have moved to a rule-11(b) Option-B PERFORMANCE
// realisation instead (Step 3's experimental_ocaml_glue patch overrides
// each `fs_*` with the fast OCaml body from the old patch 89; deleting
// that patch falls back to the definitions below -- slower, never wrong).
//
// Parser.FastString.fsti (new, this same landing) keeps these definitions
// OPAQUE to the 31 consumer modules exactly the way the old `assume val`s
// were -- see that file's banner for why, and for the bridging lemmas
// (`fs_*_eq`) that give proof modules controlled access to the underlying
// Parser.FastString.Spec formula without a full `friend` unfold.
//
// ORIGINAL RATIONALE (unchanged, still the reason this module exists at
// all -- restated verbatim from the pre-migration banner):
// ----------------------------------------------------------------------
// The F* OCaml runtime's FStar.String maps length/index/sub onto BatUTF8,
// which walks the UTF-8 byte sequence on every call to count codepoints.
// Profiled cost on a 1000-triple full-IRI Turtle file: 99.9 percent of leaf
// CPU samples are inside BatUTF8.length_aux, BatUTF8.nth_aux, BatUTF8.next.
// Every inner-loop call to String.length or String.index in the Turtle
// scanner therefore costs O(n) in the input byte count, turning the
// whole parse into O(n^2).
//
// SAFETY
// ------
// These are byte-level operations. They are ONLY safe for parsers whose
// grammar commits on ASCII bytes and treats any multi-byte UTF-8 as opaque
// bytes inside quoted literal bodies. Turtle, N-Triples, N-Quads, and TriG
// all satisfy this: whitespace, delimiters, keywords, escapes, number
// formats, and IRI-reference brackets are all ASCII. Multi-byte UTF-8
// appears only inside "..." and <...> bodies which we extract as raw
// substrings and hand back to the caller without inspecting the bytes.
//
// If your parser needs codepoint semantics (e.g. to enforce a Unicode
// character-class precondition over the entire input, not just the
// delimiter set), these primitives are the wrong tool. Stay on
// FStar.String for that use.
//
// COST MODEL (Step 3's fast OCaml realisation; the plain definitions below
// are O(n)/O(n^2) list-walking -- correct, not fast, until Step 3's patch
// is applied)
// -----------------------------------
// fs_byte_length : O(1)          -- reads the OCaml string's byte length
// fs_byte_at     : O(1)          -- one String.unsafe_get, bounds-checked
// fs_byte_sub    : O(len)        -- a single String.sub allocation
// fs_find_byte   : O(end - start)-- scans bytes for one specific code
// ============================================================================

module Spec = Parser.FastString.Spec

// ----------------------------------------------------------------------
// The six re-founded primitives, in Parser.FastString.fsti's val order
// (F* requires an interfaced module's `.fst` definitions to appear in the
// SAME order as the `.fsti`'s `val`s -- Error 233 if not, confirmed while
// landing this file). Spec twins and bridging lemmas therefore follow in
// their OWN two blocks below, mirroring the .fsti's own three-block
// layout, rather than interleaved per-primitive.
// ----------------------------------------------------------------------

// fs_byte_length. Byte length of the UTF-8 encoding of s. Differs from
// FStar.String.length (codepoint count) by being O(1) once Step 3's OCaml
// realisation is applied; the plain definition below is O(n).
let fs_byte_length (s:string) : nat =
  FStar.List.Tot.length (Spec.utf8_bytes s)

// fs_byte_at. Byte at index i (0 <= i < fs_byte_length s), as a nat in
// [0, 255]. NOT a codepoint -- a raw byte. Out-of-range i returns 0 (a
// total function, matching Step 3's fast OCaml realisation which now
// carries its own bounds check for the same reason -- see that patch's
// banner).
let fs_byte_at (s:string) (i:nat) : n:nat{n < 256} =
  match Spec.nth_byte (Spec.utf8_bytes s) i with
  | Some b -> b
  | None -> 0

// fs_byte_sub. Substring by BYTE indices, mirroring patch 89's clamp
// EXACTLY -- but structurally rather than via an explicit branch:
// Parser.FastString.Spec.slice_bytes (drop_bytes then take_bytes) already
// yields [] once `start` runs past the end of the byte list, and
// truncates `len` once it would run past the end, which is precisely
// patch 89's `if i > slen then "" else let m = if i+n>slen then slen-i
// else n in String.sub s i m` clamp. The slice is then DECODED back into
// codepoints (Spec.utf8_decode_all) and re-encoded via
// FStar.String.string_of_list.
//
// This is a genuine BEHAVIOUR CHANGE from patch 89's raw byte-copy
// fs_byte_sub for any slice that does not land on a UTF-8 codepoint
// boundary: an F* `string` cannot represent a byte sequence that is not
// valid UTF-8 (there is no way to build a string containing "half a
// multi-byte character"), so a boundary-crossing slice necessarily
// decodes-and-reencodes into something DIFFERENT from a literal byte
// copy of that range -- see Parser.FastString.fsti's fs_byte_sub_eq
// banner for the exact scope of what is (and is not) proved about this.
// tests/unit/parser_fast_string_equivalence.ml's byte_sub coverage is
// restricted to boundary-aligned, in-bounds slices for exactly this
// reason, with off-domain rows recorded as documented XFAIL.
let fs_byte_sub (s:string) (start:nat) (len:nat) : string =
  FStar.String.string_of_list
    (Spec.utf8_decode_all (Spec.slice_bytes (Spec.utf8_bytes s) start len))

// fs_find_byte. Find the first occurrence of byte b at or after position
// start. Returns fs_byte_length s if not found -- Spec.find_byte scans
// the WHOLE byte list from index 0 regardless of `start` (only ACCEPTING
// a match once idx >= start), so a not-found result is always exactly
// the list length, matching patch 89's `if i>=slen then slen else ...`
// loop even when `start` overshoots `slen`.
let fs_find_byte (s:string) (b:nat) (start:nat) : nat =
  Spec.find_byte (Spec.utf8_bytes s) b start

// fs_cp_at / fs_cp_len. Decode the UTF-8 codepoint that begins at byte
// position `pos`. Returns (codepoint, byte_length_consumed); on invalid
// UTF-8 returns (0xFFFD, 1) so a caller that repeatedly decodes-and-
// advances always makes forward progress (Spec.utf8_decode_at's own
// termination guarantee, restated in Parser.FastString.Spec's banner).
let fs_cp_at (s:string) (pos:nat) : nat & nat =
  let (cp, adv) = Spec.utf8_decode_at (Spec.utf8_bytes s) pos in
  (cp, (adv <: nat))

let fs_cp_len (s:string) (pos:nat) : nat =
  let (_, adv) = Spec.utf8_decode_at (Spec.utf8_bytes s) pos in
  (adv <: nat)

// ----------------------------------------------------------------------
// Spec twins -- see Parser.FastString.fsti's banner for why each is a
// SEPARATE, independently-computed function rather than a call to its
// `fs_*` sibling by name (a plain forwarding call would be silently
// redirected to Step 3's fast OCaml override once that patch is applied,
// since a forwarding reference resolves to whatever the named binding IS
// at the OCaml compilation point, not to "the definition as originally
// written" -- confirmed by a standalone probe before choosing this
// shape).
// ----------------------------------------------------------------------

let fs_byte_length_spec (s:string) : nat =
  FStar.List.Tot.length (Spec.utf8_bytes s)

let fs_byte_at_spec (s:string) (i:nat) : n:nat{n < 256} =
  match Spec.nth_byte (Spec.utf8_bytes s) i with
  | Some b -> b
  | None -> 0

let fs_byte_sub_spec (s:string) (start:nat) (len:nat) : string =
  FStar.String.string_of_list
    (Spec.utf8_decode_all (Spec.slice_bytes (Spec.utf8_bytes s) start len))

let fs_find_byte_spec (s:string) (b:nat) (start:nat) : nat =
  Spec.find_byte (Spec.utf8_bytes s) b start

let fs_cp_at_spec (s:string) (pos:nat) : nat & nat =
  let (cp, adv) = Spec.utf8_decode_at (Spec.utf8_bytes s) pos in
  (cp, (adv <: nat))

let fs_cp_len_spec (s:string) (pos:nat) : nat =
  let (_, adv) = Spec.utf8_decode_at (Spec.utf8_bytes s) pos in
  (adv <: nat)

// ----------------------------------------------------------------------
// Bridging lemmas -- see Parser.FastString.fsti for the full rationale.
// Each is a trivial unfolding proof: the `fs_*` definition above IS the
// RHS stated here.
// ----------------------------------------------------------------------

let fs_byte_length_eq (s:string)
  : Lemma (fs_byte_length s == FStar.List.Tot.length (Spec.utf8_bytes s))
  = ()

let fs_byte_at_eq (s:string) (i:nat)
  : Lemma (fs_byte_at s i ==
           (match Spec.nth_byte (Spec.utf8_bytes s) i with
            | Some b -> b
            | None -> 0))
  = ()

let fs_byte_sub_eq (s:string) (start:nat) (len:nat)
  : Lemma (fs_byte_sub s start len ==
           FStar.String.string_of_list
             (Spec.utf8_decode_all (Spec.slice_bytes (Spec.utf8_bytes s) start len)))
  = ()

let fs_find_byte_eq (s:string) (b:nat) (start:nat)
  : Lemma (fs_find_byte s b start == Spec.find_byte (Spec.utf8_bytes s) b start)
  = ()

let fs_cp_at_eq (s:string) (pos:nat)
  : Lemma (fs_cp_at s pos ==
           (let (cp, adv) = Spec.utf8_decode_at (Spec.utf8_bytes s) pos in
            (cp, (adv <: nat))))
  = ()

let fs_cp_len_eq (s:string) (pos:nat)
  : Lemma (fs_cp_len s pos ==
           (let (_, adv) = Spec.utf8_decode_at (Spec.utf8_bytes s) pos in
            (adv <: nat)))
  = ()

// ---------------------------------------------------------------------------
// unsafe_char_of_d7ff is NOT declared here any more -- it lives in
// Parser.FastString.CharBoundary.fst (a plain `.fst`-only assume val, the
// same shape it always was) and is re-exported into this module's
// namespace via `include Parser.FastString.CharBoundary` in
// Parser.FastString.fsti. See that module's banner for the full "why a
// separate file" explanation. `Parser.FastString.unsafe_char_of_d7ff`
// still resolves from any consumer exactly as before.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Convenience: return the byte at position i as an FStar.Char.char, so
// existing call sites that do "let c = String.index input pos in
// let code = int_of_char c in ..." can keep their downstream code by
// using fs_byte_index instead. The char will carry the numeric code in
// its Char.int_of_char representation -- the same way String.index did
// before, for ASCII inputs.
//
// SAFETY: char_of_int's F* precondition is (c < 0xD800). A raw byte is
// always < 256 < 0xD800, so this is total without an explicit refinement
// check. We still write the refinement out to help the SMT solver.
// ---------------------------------------------------------------------------
let fs_byte_index (s: string) (i: nat) : char =
  let b = fs_byte_at s i in
  // b is a byte, so 0 <= b <= 255 < 0xD800; safe for char_of_int.
  if b < 0xD800 then char_of_int b else char_of_int 0

// Convenience: char-returning version for call sites that don't want to
// deal with nat. Matches the String.index surface. NOT in Parser.FastString
// .fsti -- zero external consumers (grepped before this migration), so it
// stays private the same way it was effectively unreferenced before.
let fs_char_at (s: string) (i: nat) : char = fs_byte_index s i

// ---------------------------------------------------------------------------
// Codepoint-list view of a UTF-8 string (#240).
//
// FStar.String.list_of_string is realised in the F* OCaml runtime via
// BatUTF8.length + BatUTF8.get, which read bytes through
// String.unsafe_get. Under js_of_ocaml's `use-js-string=true` mode
// String.unsafe_get returns a UTF-16 code unit instead of a byte, so
// BatUTF8 misreads non-ASCII input and synthesises out-of-range
// codepoints (BatUChar.Out_of_range, codepoints > 0x10FFFF). Visible
// in the public demo as "Müller" → 0x36DB65 → BatUChar.chr crash.
//
// This is the same UTF-8 walk but goes through fs_cp_at, which is now a
// real Parser.FastString.Spec-backed definition (Step 2) instead of an
// assume val, and Step 3's OCaml patch overrides fs_cp_at IN PLACE (same
// binding site, not appended at file end) specifically so this function
// -- defined below fs_cp_at and therefore binding to whatever fs_cp_at
// resolves to at ITS OWN compile point -- automatically becomes fast too
// once that patch lands, with no separate override of its own. (Patch 89
// carried a dedicated fs_codepoints_of_string_aux/fs_codepoints_of_string
// override before this migration; Step 3 evaluates it deletable for
// exactly this reason -- see that patch's updated header.)
//
// Termination: each step advances by `adv >= 1` bytes (fs_cp_at_impl
// returns (0xFFFD, 1) on invalid input, never (_, 0)), so the
// `byte_length s - pos` measure strictly decreases.
// ---------------------------------------------------------------------------

let rec fs_codepoints_of_string_aux (s : string) (slen : nat) (pos : nat)
                                    (acc : list char)
  : Tot (list char) (decreases (slen - pos))
  =
  if pos >= slen then FStar.List.Tot.rev acc
  else
    let (cp, adv) = fs_cp_at s pos in
    let advn : nat = if adv = 0 then 1 else adv in
    let next : nat = pos + advn in
    // We need (slen - next) < (slen - pos), i.e. next > pos. advn >= 1
    // gives that. F* needs help to see the witness via the refinement
    // on advn.
    if next > slen then FStar.List.Tot.rev acc
    else
      // Char.char_of_int precondition is i < 0xd7ff \/ (i >= 0xe000 /\
      // i <= 0x10ffff). Split the branches so each matches one disjunct
      // verbatim — the SMT solver needs the disjunct visible per arm.
      let c : char =
        if cp < 0xd7ff then char_of_int cp
        else if cp >= 0xe000 && cp <= 0x10ffff then char_of_int cp
        else char_of_int 0xFFFD
      in
      fs_codepoints_of_string_aux s slen next (c :: acc)

let fs_codepoints_of_string (s:string) : list char =
  fs_codepoints_of_string_aux s (fs_byte_length s) 0 []

// ---------------------------------------------------------------------------
// UTF-8-encode ONE codepoint (#325).
//
// The counterpart to fs_byte_sub: use fs_byte_sub when you hold BYTES and
// want them out unchanged, and this when you hold a CODEPOINT (from a
// \uXXXX / \UXXXXXXXX escape, or a numeric character reference) and want
// its UTF-8 encoding. Mixing the two up is the bug behind issue #325, and
// it is worth stating the whole hazard in one place:
//
//   FStar.String.string_of_list extracts to
//     BatUTF8.init (length l) (fun i -> BatUChar.chr (List.at l i))
//   i.e. it RE-ENCODES every list element as a UTF-8 codepoint. Push a
//   RAW BYTE 0xE6 into that list and two bytes 0xC3 0xA6 come back out.
//   So a parser that walks bytes with fs_byte_index, accumulates them in
//   a `list char`, and finishes with string_of_list silently rewrites all
//   its non-ASCII input as UTF-8-read-as-Latin-1: <.../日本語> parsed to
//   <.../æ¥æ¬èª>. On a ONE-element list, though, string_of_list is
//   exactly "encode this codepoint", which is what escapes need.
//
//   FStar.String.string_of_char is the mirror-image trap: it extracts to
//   BatString.of_char (Char.chr c), which is byte-oriented — correct for
//   passing a byte through, and it RAISES for anything above U+00FF, so
//   it must never be handed a codepoint.
//
// Rule of thumb for any parser in this tree: raw bytes leave through
// fs_byte_sub, codepoints leave through fs_utf8_of_codepoint, and the two
// never share an accumulator.
//
// The codepoint clamp mirrors Parser.NTriples.safe_char_of_int (invalid
// values become U+FFFD) and routes U+D7FF through unsafe_char_of_d7ff to
// dodge FStar.Char.char_of_int's off-by-one precondition, as documented
// above. It is restated here rather than imported because this module sits
// below Parser.NTriples in the dependency graph.
// ---------------------------------------------------------------------------
let fs_utf8_of_codepoint (cp: int) : string =
  let c : FStar.Char.char =
    if cp = 0xD7FF then unsafe_char_of_d7ff cp
    else if cp >= 0 && (cp < 0xD7FF || (cp >= 0xE000 && cp <= 0x10FFFF)) then
      let n : nat = cp in
      FStar.Char.char_of_int n
    else
      FStar.Char.char_of_int 0xFFFD
  in
  FStar.String.string_of_list [c]
