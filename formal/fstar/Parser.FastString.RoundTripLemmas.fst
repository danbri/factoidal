module Parser.FastString.RoundTripLemmas

open Parser.FastString
open Parser.FastString.Axioms

(** ======================================================================== **)
(** Proved consequences of `Parser.FastString.Axioms` -- issue #358.         **)
(**                                                                          **)
(** NO new axioms below: everything here is a `let`/`Lemma` proved from the  **)
(** six facts in `Parser.FastString.Axioms.fsti` (plus ordinary F* string    **)
(** literal reduction, e.g. `"a" ^ "b" == "ab"`, which the normalizer        **)
(** already handles with no help -- confirmed empirically while writing      **)
(** this module).                                                            **)
(** ======================================================================== **)

/// Demo consequence requested by #358: the length-homomorphism + ASCII-
/// singleton axioms are enough to compute a concrete literal's byte
/// length, something that was flatly unprovable before this module
/// (`SPARQL.Protocol.RoundTrip.fst`'s banner records the same fact
/// failing with Error 19 against the bare `assume val`s).
let demo_fs_byte_length_ab ()
  : Lemma (fs_byte_length "ab" == 2)
  =
  fs_byte_length_ascii_singleton "a" (FStar.Char.char_of_int 97);
  fs_byte_length_ascii_singleton "b" (FStar.Char.char_of_int 98);
  fs_byte_length_concat "a" "b";
  assert ("a" ^ "b" == "ab")

/// What the SRJ text round-trip needs (per `SPARQL.Protocol.RoundTrip.fst`'s
/// banner, "the missing bridging fact" category): once a parser has
/// consumed a known `prefix` of the input, reading byte `i` of whatever
/// comes next (`rest`) at the shifted physical position
/// `fs_byte_length prefix + i` agrees with reading byte `i` directly out
/// of `rest`. This is the fact a recursive-descent scanner over
/// `prefix ^ rest` relies on implicitly every time it advances its
/// position counter past a literal it just matched.
let lemma_byte_at_after_prefix (prefix rest : string) (i : nat)
  : Lemma (requires i < fs_byte_length rest)
          (ensures  fs_byte_at (prefix ^ rest) (fs_byte_length prefix + i) == fs_byte_at rest i)
  =
  fs_byte_length_concat prefix rest;
  fs_byte_at_concat prefix rest (fs_byte_length prefix + i)

(** ======================================================================== **)
(** Multi-character ASCII content, session 2026-08-09/10 continuing #358.    **)
(**                                                                          **)
(** The eight axioms only reach ONE-character strings directly (facts 3/7).  **)
(** `SPARQL.Protocol.RoundTrip.fst`'s literal-lexing goal needs facts about  **)
(** arbitrary-length ASCII content (an `rdf_term`'s `lexical_form`, an SRJ   **)
(** variable name, etc.) -- a VARIABLE string, not a literal, so the demo    **)
(** `"a" ^ "b" == "ab"` trick (which only works because the normalizer      **)
(** reduces CONCRETE literal concatenation) does not apply.                 **)
(**                                                                          **)
(** ROUTE FOUND: build the string explicitly from its codepoint list via     **)
(** `FStar.String.string_of_list` (one call per character, singleton lists), **)
(** never via `FStar.String.list_of_string` decomposition of an opaque       **)
(** variable string. The two are NOT interchangeable here -- confirmed       **)
(** empirically this session: `list_of_string`/`string_of_list` behave as    **)
(** ordinary SMT-congruent functions when the SAME lemma call produces both  **)
(** sides of an equality (`FStar.String.list_of_string_of_list [c]` below    **)
(** works first try), but ATTEMPTING to chain that fact through a SEPARATE   **)
(** equality hypothesis (e.g. `list_of_string s == []` established via a     **)
(** `match`, then asking Z3 to derive `string_of_list (list_of_string s) ==  **)
(** string_of_list []`) fails Error 19 even though it is plain first-order   **)
(** congruence for an otherwise-ordinary `assume val`-shaped function --     **)
(** reproduced against a fresh `assume val myf : list int -> int` (WORKS)    **)
(** versus the identical pattern against `FStar.String.string_of_list`       **)
(** (FAILS), isolating the quirk to this specific stdlib pair rather than to **)
(** general SMT congruence. Building the target string FORWARD from a list   **)
(** (`string_of_list [c]`, `list_of_string_of_list` in the SAME lemma call)   **)
(** sidesteps the quirk entirely and is the pattern below.                   **)
(** ======================================================================== **)

/// One codepoint as a string, built via `string_of_list` (not `make`/
/// `string_of_char`, so `list_of_string_of_list` gives back its codepoint
/// list directly for facts 3/7 to consume).
let one_char_string (c : FStar.Char.char) : string =
  FStar.String.string_of_list [c]

let lemma_one_char_list_of_string (c : FStar.Char.char)
  : Lemma (FStar.String.list_of_string (one_char_string c) == [c])
  = FStar.String.list_of_string_of_list [c]

/// Value-and-length characterisation of `one_char_string` for an ASCII
/// codepoint, composing facts 3 and 7.
let lemma_one_char_byte_length (c : FStar.Char.char{FStar.Char.int_of_char c < 128})
  : Lemma (fs_byte_length (one_char_string c) == 1)
  = lemma_one_char_list_of_string c;
    fs_byte_length_ascii_singleton (one_char_string c) c

let lemma_one_char_byte_at (c : FStar.Char.char{FStar.Char.int_of_char c < 128})
  : Lemma (fs_byte_at (one_char_string c) 0 == FStar.Char.int_of_char c)
  = lemma_one_char_list_of_string c;
    fs_byte_at_ascii_singleton (one_char_string c) c

/// All codepoints in the list are ASCII (< 128).
let rec all_ascii (cs : list FStar.Char.char) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest -> FStar.Char.int_of_char c < 128 && all_ascii rest

/// Build a string from an explicit codepoint list, one `one_char_string`
/// concatenation at a time. This is the FORWARD construction that lets
/// facts 2/3/7 walk the content by structural induction on `cs` -- the
/// route the codepoint-list-DEcomposition direction could not take (see
/// banner above).
let rec build_string (cs : list FStar.Char.char) : Tot string (decreases cs) =
  match cs with
  | [] -> ""
  | c :: rest -> one_char_string c ^ build_string rest

/// Byte length of a `build_string` matches the codepoint count, for ASCII
/// content. Induction on `cs` via facts 1 (empty), 2 (concat homomorphism)
/// composed with `lemma_one_char_byte_length`.
let rec lemma_build_string_byte_length (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (ensures fs_byte_length (build_string cs) == List.Tot.length cs)
          (decreases cs)
  = match cs with
    | [] -> fs_byte_length_empty ()
    | c :: rest ->
      lemma_one_char_byte_length c;
      lemma_build_string_byte_length rest;
      fs_byte_length_concat (one_char_string c) (build_string rest)

/// Byte AT position `i` of a `build_string` is exactly that codepoint's
/// numeric value, for ASCII content -- the VALUE-level sibling of the
/// length lemma above, composing fact 4 (index-into-concat) with fact 7
/// at the leaf.
let rec lemma_build_string_byte_at
    (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < List.Tot.length cs})
  : Lemma (ensures fs_byte_at (build_string cs) i == FStar.Char.int_of_char (List.Tot.index cs i))
          (decreases cs)
  = match cs with
    | c :: rest ->
      lemma_one_char_byte_length c;
      lemma_build_string_byte_length rest;
      fs_byte_length_concat (one_char_string c) (build_string rest);
      fs_byte_at_concat (one_char_string c) (build_string rest) i;
      if i < 1 then lemma_one_char_byte_at c
      else lemma_build_string_byte_at rest (i - 1)

/// The quoted-string READ-BACK primitive step named in the brief: slicing
/// the byte range strictly between the two quote bytes of a constructed
/// `"..."` JSON string literal recovers the content exactly, at the
/// `fs_byte_sub` level (below `Parser.JSON.json_string_segments`'s own
/// scanning loop -- see `SPARQL.Protocol.RoundTrip.fst`'s banner for why
/// the scanning loop itself cannot be closed with only these eight facts).
/// Composes facts 3 (length of the quote literal), 2 (concat length,
/// twice), 5a and 5b (slice-into-concat, once each) and 8 (self-slice).
let lemma_quoted_content_byte_sub (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (
      (**) lemma_build_string_byte_length cs;
      fs_byte_sub ("\"" ^ build_string cs ^ "\"") 1 (List.Tot.length cs) == build_string cs)
  =
  let content = build_string cs in
  // NOTE: `quote` is a reserved-ish F* identifier (quotation syntax) --
  // using it as a `let`-binder name here produced a "Syntax error"
  // pointing at the FOLLOWING line, exactly the off-by-one trap CLAUDE.md
  // warns about. Named `dq_str` instead.
  let dq_str = "\"" in
  lemma_build_string_byte_length cs;
  let len = List.Tot.length cs in
  assert (("\"" ^ content ^ "\"") == (dq_str ^ (content ^ dq_str)));
  fs_byte_length_ascii_singleton dq_str (FStar.Char.char_of_int 0x22);
  fs_byte_length_concat content dq_str;
  fs_byte_length_concat dq_str (content ^ dq_str);
  fs_byte_sub_concat_right dq_str (content ^ dq_str) 1 len;
  fs_byte_sub_concat_left content dq_str 0 len;
  fs_byte_sub_self content
