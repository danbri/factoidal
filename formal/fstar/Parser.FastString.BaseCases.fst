module Parser.FastString.BaseCases

open Parser.FastString
module Spec = Parser.FastString.Spec

(* ============================================================================
 * Parser.FastString.BaseCases -- FastString re-founding, Step 5, Task A
 * (docs/designissues/2026-08-10-faststring-refounding-plan.md).
 *
 * PROOF-ONLY, ADDITIVE, NOT WIRED. Not in build-ocaml.sh's module lists --
 * this file states and proves facts, it defines no new runtime primitive.
 *
 * PURPOSE. `Parser.FastString.Axioms.fsti` (issue #358) *assumes* eight
 * facts about `fs_byte_length`/`fs_byte_at`/`fs_byte_sub` because, at the
 * time it was written, the six `fs_*` primitives were bare `assume val`s
 * with no F*-visible equations at all. Steps 2/3 of THIS migration changed
 * that: `Parser.FastString.fsti` now exports bridging lemmas
 * (`fs_byte_length_eq`, `fs_byte_at_eq`, ...) that restate each primitive
 * in terms of `Parser.FastString.Spec`'s definitional UTF-8 codec. This
 * module uses ONLY those bridging lemmas plus `Parser.FastString.Spec` --
 * deliberately NOT `Parser.FastString.Axioms` (in-flight elsewhere this
 * session; this module is independent of it by construction, not just by
 * task-brief instruction) -- to PROVE, rather than assume, the concrete
 * single-character facts the JSON/N-Triples round-trip work needs, plus a
 * general ASCII-content lemma family that gives `Parser.FastString.
 * RoundTripLemmas.fst`'s `build_string`/`one_char_string` scaffolding a
 * more direct route: that file goes build_string -> Axioms' abstracted
 * eight facts; this module goes build_string -> Spec.utf8_bytes directly,
 * one layer closer to the definitional codec.
 *
 * PATTERN, per char: `Spec.utf8_bytes_ascii_singleton` (needs
 * `FStar.String.list_of_string s == [c]`, which F*'s normalizer discharges
 * for any string LITERAL with no help -- confirmed empirically, matching
 * the same pattern `Axioms.fsti`'s own banner documents for fact 3) plus
 * `Spec.nth_byte_zero` gives `utf8_bytes s == [code]` and
 * `nth_byte (utf8_bytes s) 0 == Some code`; composed with the bridging
 * lemmas `fs_byte_length_eq`/`fs_byte_at_eq`, that is exactly
 * `fs_byte_length s == 1` and `fs_byte_at s 0 == code`.
 * ============================================================================ *)

(* ----------------------------------------------------------------------
 * General ASCII-singleton pattern, packaged once, reused per delimiter.
 * ---------------------------------------------------------------------- *)

val fs_ascii_singleton_facts (s : string) (c : FStar.Char.char)
  : Lemma (requires FStar.String.list_of_string s == [c] /\ FStar.Char.int_of_char c < 0x80)
          (ensures  fs_byte_length s == 1 /\ fs_byte_at s 0 == FStar.Char.int_of_char c)
let fs_ascii_singleton_facts s c =
  fs_byte_length_eq s;
  fs_byte_at_eq s 0;
  Spec.utf8_bytes_ascii_singleton s c;
  Spec.nth_byte_zero (FStar.Char.int_of_char c) []

(* ----------------------------------------------------------------------
 * The JSON / N-Triples delimiter set, one lemma pair per character:
 * quote, open/close brace, open/close bracket, colon, comma,
 * less-than/greater-than, space, newline, backslash -- 12 characters,
 * literal-capped per CLAUDE.md's normalizer-cost note.
 * ---------------------------------------------------------------------- *)

// U+0022 QUOTATION MARK, "\""
val fs_byte_at_quote (_:unit) : Lemma (fs_byte_at "\"" 0 == 0x22)
let fs_byte_at_quote () = fs_ascii_singleton_facts "\"" (FStar.Char.char_of_int 0x22)

val fs_byte_length_quote (_:unit) : Lemma (fs_byte_length "\"" == 1)
let fs_byte_length_quote () = fs_ascii_singleton_facts "\"" (FStar.Char.char_of_int 0x22)

// U+007B LEFT CURLY BRACKET, "{"
val fs_byte_at_lbrace (_:unit) : Lemma (fs_byte_at "{" 0 == 0x7B)
let fs_byte_at_lbrace () = fs_ascii_singleton_facts "{" (FStar.Char.char_of_int 0x7B)

val fs_byte_length_lbrace (_:unit) : Lemma (fs_byte_length "{" == 1)
let fs_byte_length_lbrace () = fs_ascii_singleton_facts "{" (FStar.Char.char_of_int 0x7B)

// U+007D RIGHT CURLY BRACKET, "}"
val fs_byte_at_rbrace (_:unit) : Lemma (fs_byte_at "}" 0 == 0x7D)
let fs_byte_at_rbrace () = fs_ascii_singleton_facts "}" (FStar.Char.char_of_int 0x7D)

val fs_byte_length_rbrace (_:unit) : Lemma (fs_byte_length "}" == 1)
let fs_byte_length_rbrace () = fs_ascii_singleton_facts "}" (FStar.Char.char_of_int 0x7D)

// U+005B LEFT SQUARE BRACKET, "["
val fs_byte_at_lbracket (_:unit) : Lemma (fs_byte_at "[" 0 == 0x5B)
let fs_byte_at_lbracket () = fs_ascii_singleton_facts "[" (FStar.Char.char_of_int 0x5B)

val fs_byte_length_lbracket (_:unit) : Lemma (fs_byte_length "[" == 1)
let fs_byte_length_lbracket () = fs_ascii_singleton_facts "[" (FStar.Char.char_of_int 0x5B)

// U+005D RIGHT SQUARE BRACKET, "]"
val fs_byte_at_rbracket (_:unit) : Lemma (fs_byte_at "]" 0 == 0x5D)
let fs_byte_at_rbracket () = fs_ascii_singleton_facts "]" (FStar.Char.char_of_int 0x5D)

val fs_byte_length_rbracket (_:unit) : Lemma (fs_byte_length "]" == 1)
let fs_byte_length_rbracket () = fs_ascii_singleton_facts "]" (FStar.Char.char_of_int 0x5D)

// U+003A COLON, ":"
val fs_byte_at_colon (_:unit) : Lemma (fs_byte_at ":" 0 == 0x3A)
let fs_byte_at_colon () = fs_ascii_singleton_facts ":" (FStar.Char.char_of_int 0x3A)

val fs_byte_length_colon (_:unit) : Lemma (fs_byte_length ":" == 1)
let fs_byte_length_colon () = fs_ascii_singleton_facts ":" (FStar.Char.char_of_int 0x3A)

// U+002C COMMA, ","
val fs_byte_at_comma (_:unit) : Lemma (fs_byte_at "," 0 == 0x2C)
let fs_byte_at_comma () = fs_ascii_singleton_facts "," (FStar.Char.char_of_int 0x2C)

val fs_byte_length_comma (_:unit) : Lemma (fs_byte_length "," == 1)
let fs_byte_length_comma () = fs_ascii_singleton_facts "," (FStar.Char.char_of_int 0x2C)

// U+003C LESS-THAN SIGN, "<"
val fs_byte_at_lt (_:unit) : Lemma (fs_byte_at "<" 0 == 0x3C)
let fs_byte_at_lt () = fs_ascii_singleton_facts "<" (FStar.Char.char_of_int 0x3C)

val fs_byte_length_lt (_:unit) : Lemma (fs_byte_length "<" == 1)
let fs_byte_length_lt () = fs_ascii_singleton_facts "<" (FStar.Char.char_of_int 0x3C)

// U+003E GREATER-THAN SIGN, ">"
val fs_byte_at_gt (_:unit) : Lemma (fs_byte_at ">" 0 == 0x3E)
let fs_byte_at_gt () = fs_ascii_singleton_facts ">" (FStar.Char.char_of_int 0x3E)

val fs_byte_length_gt (_:unit) : Lemma (fs_byte_length ">" == 1)
let fs_byte_length_gt () = fs_ascii_singleton_facts ">" (FStar.Char.char_of_int 0x3E)

// U+0020 SPACE, " "
val fs_byte_at_space (_:unit) : Lemma (fs_byte_at " " 0 == 0x20)
let fs_byte_at_space () = fs_ascii_singleton_facts " " (FStar.Char.char_of_int 0x20)

val fs_byte_length_space (_:unit) : Lemma (fs_byte_length " " == 1)
let fs_byte_length_space () = fs_ascii_singleton_facts " " (FStar.Char.char_of_int 0x20)

// U+000A LINE FEED, "\n"
val fs_byte_at_newline (_:unit) : Lemma (fs_byte_at "\n" 0 == 0x0A)
let fs_byte_at_newline () = fs_ascii_singleton_facts "\n" (FStar.Char.char_of_int 0x0A)

val fs_byte_length_newline (_:unit) : Lemma (fs_byte_length "\n" == 1)
let fs_byte_length_newline () = fs_ascii_singleton_facts "\n" (FStar.Char.char_of_int 0x0A)

// U+005C REVERSE SOLIDUS, "\\"
val fs_byte_at_backslash (_:unit) : Lemma (fs_byte_at "\\" 0 == 0x5C)
let fs_byte_at_backslash () = fs_ascii_singleton_facts "\\" (FStar.Char.char_of_int 0x5C)

val fs_byte_length_backslash (_:unit) : Lemma (fs_byte_length "\\" == 1)
let fs_byte_length_backslash () = fs_ascii_singleton_facts "\\" (FStar.Char.char_of_int 0x5C)

(* ============================================================================
 * General content lemma family -- the Spec-direct replacement for
 * `Parser.FastString.RoundTripLemmas.fst`'s `build_string`/`one_char_string`
 * scaffolding (that file routes through `Parser.FastString.Axioms`'s eight
 * assumed facts; this family routes through `Parser.FastString.Spec`
 * directly via the bridging lemmas, one layer closer to the definitional
 * codec, and proves the SAME two composite facts that file's own banner
 * says the SRJ text round-trip needs: a `build_string`'s byte LENGTH is
 * its codepoint count, and the byte AT position `i` is that codepoint's
 * numeric value -- for all-ASCII content).
 * ============================================================================ *)

/// One codepoint as a string, built via `string_of_list` -- same
/// construction as `RoundTripLemmas.one_char_string`, so
/// `list_of_string_of_list` gives its codepoint list back directly.
let one_char_string (c : FStar.Char.char) : string =
  FStar.String.string_of_list [c]

let lemma_one_char_list_of_string (c : FStar.Char.char)
  : Lemma (FStar.String.list_of_string (one_char_string c) == [c])
  = FStar.String.list_of_string_of_list [c]

/// All codepoints in the list are ASCII (< 0x80).
let rec all_ascii (cs : list FStar.Char.char) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest -> FStar.Char.int_of_char c < 0x80 && all_ascii rest

/// Build a string from an explicit codepoint list, one `one_char_string`
/// concatenation at a time -- same shape as `RoundTripLemmas.build_string`.
let rec build_string (cs : list FStar.Char.char) : Tot string (decreases cs) =
  match cs with
  | [] -> ""
  | c :: rest -> one_char_string c ^ build_string rest

/// The codepoint list of an all-ASCII `cs`, re-typed at `Parser.
/// FastString.Spec`'s own `byte` type. `FStar.List.Tot.map FStar.Char.
/// int_of_char cs` would carry the same VALUES, but F* cannot see the
/// elementwise `< 256` byte refinement through a bare `map` applied to a
/// list-level `all_ascii` predicate (confirmed empirically: Error 19,
/// "Subtyping check failed ... FStar.Char.char -> Parser.FastString.Spec.
/// byte, got ... -> Prims.nat" at exactly this shape). This recursive
/// definition carries the refinement structurally instead -- at each cons
/// step, matching `cs` against `c :: rest` unfolds `all_ascii cs` to
/// `FStar.Char.int_of_char c < 0x80 /\ all_ascii rest` in context, which
/// is exactly the fact `int_of_char c : Spec.byte` needs.
val codes_of (cs : list FStar.Char.char{all_ascii cs}) : Tot (list Spec.byte) (decreases cs)
let rec codes_of cs =
  match cs with
  | [] -> []
  | c :: rest -> FStar.Char.int_of_char c :: codes_of rest

/// `codes_of` preserves length.
val lemma_codes_of_length (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (ensures FStar.List.Tot.length (codes_of cs) == FStar.List.Tot.length cs)
          (decreases cs)
let rec lemma_codes_of_length cs =
  match cs with
  | [] -> ()
  | _ :: rest -> lemma_codes_of_length rest

/// Per-element consequence of `all_ascii`: the codepoint AT index `i` of
/// an all-ASCII list is itself < 0x80. Stated and proved standalone
/// (ordinary nat inequality, no cross-type coercion) so the two lemmas
/// below can take it as an explicit `requires` -- SMT cannot derive an
/// elementwise consequence of a whole-list boolean predicate at a
/// SYMBOLIC index without induction, and a `val`'s `ensures` is
/// well-formedness-checked before any proof step in its body runs, so the
/// bound must be visible as a hypothesis in the SIGNATURE, not just
/// established partway through the proof (confirmed empirically: the
/// `Some (FStar.Char.int_of_char ...)`-shaped `ensures` below failed
/// Error 19 "Subtyping check failed ... Parser.FastString.Spec.byte"
/// without this).
val lemma_all_ascii_index (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < FStar.List.Tot.length cs})
  : Lemma (ensures FStar.Char.int_of_char (FStar.List.Tot.index cs i) < 0x80)
          (decreases cs)
let rec lemma_all_ascii_index cs i =
  match cs with
  | c :: rest -> if i = 0 then () else lemma_all_ascii_index rest (i - 1)

/// Reading position `i` out of `nth_byte` applied to `codes_of cs` agrees
/// with the codepoint's own value at that index. The Spec-level workhorse
/// behind `lemma_build_string_byte_at` below -- induction via
/// `Spec.nth_byte_zero`/`Spec.nth_byte_succ`.
val lemma_nth_byte_codes_of (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < FStar.List.Tot.length cs})
  : Lemma (requires FStar.Char.int_of_char (FStar.List.Tot.index cs i) < 0x80)
          (ensures Spec.nth_byte (codes_of cs) i
                    == Some (FStar.Char.int_of_char (FStar.List.Tot.index cs i)))
          (decreases cs)
let rec lemma_nth_byte_codes_of cs i =
  match cs with
  | c :: rest ->
    if i = 0 then
      Spec.nth_byte_zero (FStar.Char.int_of_char c) (codes_of rest)
    else begin
      Spec.nth_byte_succ (FStar.Char.int_of_char c) (codes_of rest) (i - 1);
      lemma_all_ascii_index rest (i - 1);
      lemma_nth_byte_codes_of rest (i - 1)
    end

/// `utf8_bytes` of a `build_string` is exactly `codes_of cs` -- for ASCII
/// content. Induction on `cs` via `Spec.utf8_bytes_concat` (fact 2 of
/// `Spec.fst`'s own lemma kit) composed with `Spec.utf8_bytes_ascii_singleton`
/// at the leaf.
val lemma_build_string_utf8_bytes (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (ensures Spec.utf8_bytes (build_string cs) == codes_of cs)
          (decreases cs)
let rec lemma_build_string_utf8_bytes cs =
  match cs with
  | [] ->
    // `utf8_bytes ""` needs `assert_norm` help to unfold through
    // `List.Tot.concatMap` over `FStar.String.list_of_string ""` --
    // confirmed empirically both facts reduce individually (`list_of_string
    // "" == []`, `concatMap f [] == []`) but the composed application
    // `utf8_bytes s` at `s = ""` does not unfold with plain `()` at
    // default fuel/ifuel (Error 19, "Could not prove post-condition").
    assert_norm (Spec.utf8_bytes "" == [])
  | c :: rest ->
    lemma_one_char_list_of_string c;
    Spec.utf8_bytes_ascii_singleton (one_char_string c) c;
    lemma_build_string_utf8_bytes rest;
    Spec.utf8_bytes_concat (one_char_string c) (build_string rest)

/// Byte length of a `build_string` matches the codepoint count, for ASCII
/// content -- `RoundTripLemmas.lemma_build_string_byte_length`'s Spec-
/// direct sibling (that one composes Axioms facts 1/2/3; this one goes
/// straight through `fs_byte_length_eq` + `Spec.utf8_bytes`).
val lemma_build_string_byte_length (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (ensures fs_byte_length (build_string cs) == FStar.List.Tot.length cs)
let lemma_build_string_byte_length cs =
  fs_byte_length_eq (build_string cs);
  lemma_build_string_utf8_bytes cs;
  lemma_codes_of_length cs

/// Byte AT position `i` of a `build_string` is exactly that codepoint's
/// numeric value, for ASCII content -- `RoundTripLemmas.
/// lemma_build_string_byte_at`'s Spec-direct sibling, via `fs_byte_at_eq`
/// + `lemma_nth_byte_codes_of` instead of Axioms facts 4/7.
val lemma_build_string_byte_at
    (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < FStar.List.Tot.length cs})
  : Lemma (requires FStar.Char.int_of_char (FStar.List.Tot.index cs i) < 0x80)
          (ensures fs_byte_at (build_string cs) i == FStar.Char.int_of_char (FStar.List.Tot.index cs i))
          // `requires` restates `lemma_all_ascii_index`'s conclusion --
          // needed in the SIGNATURE, same reason as
          // `lemma_nth_byte_codes_of` above. Always dischargeable by
          // calling `lemma_all_ascii_index cs i` first (both call sites
          // below do); kept explicit rather than folded into `all_ascii cs`
          // for the same SMT-cannot-induct-at-a-symbolic-index reason.
let lemma_build_string_byte_at cs i =
  fs_byte_at_eq (build_string cs) i;
  lemma_build_string_utf8_bytes cs;
  lemma_nth_byte_codes_of cs i
