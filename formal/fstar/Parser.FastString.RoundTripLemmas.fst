module Parser.FastString.RoundTripLemmas

open Parser.FastString
open Parser.FastString.Axioms
module Spec = Parser.FastString.Spec

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

(** ======================================================================== **)
(** Arbitrary-ASCII-string bridging: `fs_byte_*` agrees with `FStar.String.*` **)
(** on any string whose codepoints are all ASCII -- task #52                 **)
(** (SPARQL 1.1 lexer's `substring` migration off `FStar.String.sub`,        **)
(** docs/designissues/2026-08-10-string-foundation-decision.md gap 1, owner  **)
(** decision "1: A" 2026-08-11). NEEDED BY: SPARQL11.Parser.TokenRoundTrip   **)
(** .fst / SPARQL11.Parser.AskBgpRoundTrip.fst, whose bridging lemmas        **)
(** (`peek_at_offset`/`peek_at_space`/`index_concat_at` and friends) reason  **)
(** about `peek_char`/`at_end`/`substring` -- now `fs_byte_*`-backed -- via  **)
(** `String.index`/`String.length` on OPAQUE string variables (a fragment's  **)
(** printed token text: delimiters, operators, keywords -- always ASCII, but **)
(** not a LITERAL the normalizer can reduce). The `build_string`/`all_ascii` **)
(** machinery above only reaches strings constructed FORWARD from a known   **)
(** codepoint list; these lemmas close the gap for an arbitrary string       **)
(** variable by round-tripping it through `list_of_string`/`string_of_list`. **)
(**                                                                          **)
(** All ASCII test is on `FStar.String.list_of_string s`, not a separate     **)
(** first-class predicate on `string` -- matches the shape `all_ascii`       **)
(** already has (a `list FStar.Char.char -> bool`), no new type needed.      **)
(** ======================================================================== **)

/// FINDING (recorded per CLAUDE.md rule #14 / proof-factory findings
/// discipline): the natural first route here was `build_string (list_of_
/// string s) == s` (recover `s` by decomposing to a codepoint list, then
/// reconstructing via the already-proven `build_string`/`all_ascii`
/// machinery above), giving the byte-length/byte-at facts "for free" by
/// reduction to `lemma_build_string_byte_length`/`_byte_at`. That route
/// hits a wall this file's OWN earlier banner already named ("Building
/// the target string FORWARD from a list... sidesteps the quirk
/// entirely") but this specific instance sidesteps only ONE side of it:
/// proving `build_string cs == FStar.String.string_of_list cs` needs
/// CHAINING an equality hypothesis (the induction's own IH,
/// `build_string rest == string_of_list rest`) through a SEPARATE
/// `list_of_string` congruence step to conclude a STRING equality on
/// SYMBOLIC pieces -- confirmed to fail (Error 19, "incomplete
/// quantifiers", even at `--z3rlimit 1000 --fuel 4 --ifuel 4`, both as
/// a single recursive lemma AND factored into a non-recursive cons-step
/// helper called from the recursion) in an isolated throwaway probe
/// (`Scratch.BuildStringProbe*.fst`, not committed). `RDF.NTriples.
/// RoundTrip.fst`'s own "NEXT NARROWEST UNPROVED STATEMENT" section
/// (line ~572) independently hit the SAME class of wall proving `"" ^ s
/// == s` for a SYMBOLIC `s` -- this project's own prior art already
/// flags SYMBOLIC string-algebra-via-`^`/`string_of_list` chaining as a
/// genuine, not-yet-cleared obstruction, not merely under-attempted.
///
/// ROUTE THAT WORKS (below): skip `string`/`build_string` entirely and
/// stay at the CODEPOINT-LIST level throughout, reasoning about
/// `Parser.FastString.Spec.utf8_bytes`'s own definition (`List.Tot.
/// concatMap utf8_enc_char (FStar.String.list_of_string s)`,
/// unconditionally transparent -- `Parser.FastString.Spec` carries no
/// restricting `.fsti`) directly against `FStar.List.Tot.concatMap`/
/// `length`/`index`, all of which behave as ordinary structurally-
/// inductive SMT-congruent functions (no quirk observed) -- confirmed
/// by the same probe session, `Scratch.AsciiBridgeProbe.fst`. The
/// price: `lemma_ascii_string_is_build_string`'s convenient "recover the
/// original string" shape doesn't exist on this route; each fact below
/// is proved separately, straight from `fs_byte_length_eq`/`fs_byte_at_
/// eq` unfolded against `Spec.utf8_bytes`'s own concatMap definition.
#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"

/// Every ASCII codepoint UTF-8-encodes to exactly ONE byte, so `concatMap
/// utf8_enc_char` over an all-ASCII codepoint list has the SAME length as
/// the list itself. Induction on `cs`; `utf8_enc_char`'s own `cp < 0x80 ->
/// [cp]` branch (Parser.FastString.Spec.fst) gives the length-1 base fact
/// with no extra lemma call needed (transparent `let`, unfolds directly).
let rec lemma_ascii_utf8_bytes_length (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (ensures FStar.List.Tot.length (FStar.List.Tot.concatMap Spec.utf8_enc_char cs)
                    == FStar.List.Tot.length cs)
          (decreases cs)
  = match cs with
    | [] -> ()
    | c :: rest -> lemma_ascii_utf8_bytes_length rest

/// Byte length of an all-ASCII string equals its codepoint length
/// (`FStar.String.length`). This is the fact `SPARQL11.Parser.
/// TokenRoundTrip.fst`'s generic `peek_at_offset`/`peek_at_space`
/// lemmas need to relate a byte-indexed `at_end`/`peek_char` position
/// back to `FStar.String.length`-computed offsets, for the ASCII-only
/// content this lexer's own token fragments are always built from.
let lemma_ascii_string_byte_length (s : string)
  : Lemma (requires all_ascii (FStar.String.list_of_string s))
          (ensures  fs_byte_length s == FStar.String.length s)
  =
  fs_byte_length_eq s;
  lemma_ascii_utf8_bytes_length (FStar.String.list_of_string s)

/// Every element of an all-ASCII codepoint list is itself ASCII (the
/// per-INDEX unfolding of the list-level `all_ascii` predicate) --
/// needed as a SEPARATE lemma, not just inline reasoning, because
/// `Some (int_of_char (List.Tot.index cs i)) : option Spec.byte` below
/// needs the `< 256` refinement witnessed BEFORE that term elaborates,
/// which a same-expression inline fact cannot supply in time.
let rec lemma_all_ascii_index (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < FStar.List.Tot.length cs})
  : Lemma (ensures FStar.Char.int_of_char (FStar.List.Tot.index cs i) < 128)
          (decreases cs)
  = match cs with
    | c :: rest -> if i = 0 then () else lemma_all_ascii_index rest (i - 1)

/// Byte AT position `i` (`Spec.nth_byte`-level) of an all-ASCII
/// codepoint list's UTF-8 encoding is exactly that codepoint's numeric
/// value. The `match ... with Some b -> (b <: nat) == ... | None ->
/// False` phrasing (rather than `== Some (int_of_char ...)` directly)
/// sidesteps needing the `Spec.byte` refinement proved BEFORE the
/// lemma body runs -- constructing `Some (int_of_char c)` at the type
/// `option Spec.byte` needs `int_of_char c < 256` witnessed at
/// elaboration time, which `lemma_all_ascii_index` (a lemma call, not a
/// visible refinement) cannot supply there; pattern-matching the
/// ALREADY-`Spec.byte`-typed `b` and comparing as a plain `nat` avoids
/// the construction step entirely.
let rec lemma_ascii_utf8_bytes_at (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < FStar.List.Tot.length cs})
  : Lemma (ensures
      (match Spec.nth_byte (FStar.List.Tot.concatMap Spec.utf8_enc_char cs) i with
       | Some b -> (b <: nat) == FStar.Char.int_of_char (FStar.List.Tot.index cs i)
       | None -> False))
          (decreases cs)
  = lemma_all_ascii_index cs i;
    match cs with
    | c :: rest -> if i = 0 then () else lemma_ascii_utf8_bytes_at rest (i - 1)

/// Byte AT position `i` of an all-ASCII string, as a raw code, equals
/// `FStar.Char.int_of_char` of the codepoint `FStar.String.index` would
/// read at the same (byte == codepoint, for ASCII) position.
let lemma_ascii_string_byte_at (s : string) (i : nat{i < FStar.String.length s})
  : Lemma (requires all_ascii (FStar.String.list_of_string s))
          (ensures  fs_byte_at s i == FStar.Char.int_of_char (FStar.String.index s i))
  =
  fs_byte_at_eq s i;
  lemma_ascii_utf8_bytes_at (FStar.String.list_of_string s) i;
  FStar.String.index_list_of_string s i

/// The `fs_byte_index`-level (i.e. `char_at`/`peek_char`-level)
/// restatement of the fact above: reading byte `i` of an all-ASCII
/// string as a character (`fs_byte_index`, what `char_at`/`peek_char`
/// now compute post-task-#52) gives back exactly `FStar.String.index s
/// i` -- the SAME character the pre-migration codepoint-indexed
/// `char_at`/`peek_char` returned. `char_of_u32_of_char`'s ulib `SMTPat`
/// discharges the `char_of_int (int_of_char c) == c` step with no
/// explicit lemma call.
let lemma_ascii_string_byte_index (s : string) (i : nat{i < FStar.String.length s})
  : Lemma (requires all_ascii (FStar.String.list_of_string s))
          (ensures  fs_byte_index s i == FStar.String.index s i)
  =
  lemma_ascii_string_byte_at s i;
  fs_byte_index_eq s i
#pop-options

(** ======================================================================== **)
(** SHARPENED FINDING (session 2026-08-11, `s == build_string (codes_of s)`  **)
(** attempt) -- the wall is NARROWER, and lower-level, than the "chaining an **)
(** IH through a separate congruence step" theory recorded above. Recorded  **)
(** per CLAUDE.md rule #14 so the next attempt does not re-spend the same    **)
(** probing budget on routes this session already isolated and ruled out.    **)
(**                                                                          **)
(** TARGET ATTEMPTED: `lemma_build_string_is_string_of_list (cs : list char) **)
(** : Lemma (build_string cs == FStar.String.string_of_list cs)`, by         **)
(** induction on `cs` -- the natural generalisation that would give `i ==    **)
(** build_string (Str.list_of_string i)` (RDF.NTriples.RoundTrip.fst's own   **)
(** "NEXT NARROWEST" target, line ~752) via `string_of_list_of_string`.      **)
(**                                                                          **)
(** THE MINIMAL REPRO (isolated via `--split_queries always`, ~20 throwaway  **)
(** probes this session, not committed -- `Scratch.WallProbeNN.fst`):        **)
(**                                                                          **)
(**   #push-options "--z3rlimit 200 --fuel 4 --ifuel 4"                      **)
(**   let rec lemma_list_of_build_string (cs : list FStar.Char.char)         **)
(**     : Lemma (ensures FStar.String.list_of_string (build_string cs) == cs)**)
(**             (decreases cs)                                               **)
(**     = match cs with                                                      **)
(**       | [] -> ()                                                         **)
(**       | c :: rest ->                                                     **)
(**         lemma_list_of_build_string rest;                                 **)
(**         admit ()   // <- even THIS fails                                 **)
(**   #pop-options                                                           **)
(**                                                                          **)
(** This fails Error 19 "incomplete quantifiers" AT THE RECURSIVE CALL       **)
(** STATEMENT ITSELF (`lemma_list_of_build_string rest;`), confirmed by      **)
(** `--split_queries always` isolating it to exactly that sub-query --       **)
(** BEFORE the `admit ()` even runs, i.e. with NOTHING downstream consuming  **)
(** the recursive call's postcondition. This rules out every theory this     **)
(** session initially tried to fix:                                          **)
(**   - NOT about chaining through a SEPARATE hypothesis (the postcondition  **)
(**     is used, if at all, immediately, with no intervening `match`/branch).**)
(**   - NOT about `^`/`build_string`-vs-`string_of_list` STRING-typed        **)
(**     equality specifically -- the SAME failure reproduces restating the   **)
(**     goal as a LIST equality (`list_of_string (build_string cs) == cs`,   **)
(**     avoiding `string_of_list` on the RHS entirely) and even with plain   **)
(**     `nat`/`int`-valued conclusions once an `assume val` stands in for    **)
(**     the coercion pair (control probe, see below).                       **)
(**   - NOT a resource/timeout problem -- every failing query returns        **)
(**     "incomplete quantifiers" in single-digit milliseconds even at        **)
(**     `--z3rlimit 4000`; more fuel/ifuel/rlimit does not move it.          **)
(**   - NOT fixed by `calc`, by factoring the cons-step into a separately-   **)
(**     proven non-recursive helper lemma (`cons_step`, itself verifies      **)
(**     standalone in isolation), by `#restart-solver`, or by switching the  **)
(**     `decreases` metric from `cs` to `FStar.List.Tot.length cs`.          **)
(**                                                                          **)
(** WHAT DOES NOT FAIL (control probes, same session): a NON-recursive       **)
(** lemma proving the IDENTICAL fact for a single cons-step, taking the IH   **)
(** as an explicit `squash` PARAMETER instead of obtaining it from a         **)
(** recursive self-call, verifies in single-digit milliseconds every time    **)
(** (`Probe2`/`Probe6.lemma_string_of_list_cons`/`Probe7.cons_step`/         **)
(** `standalone_check`, all not committed). `lemma_scan_iri_end_build_string`**)
(** in `RDF.NTriples.RoundTrip.fst` -- a REAL, LANDED, recursive Lemma that  **)
(** manipulates symbolic strings via `fs_byte_length_concat`/`fs_byte_at_    **)
(** concat`/`lemma_strcat_assoc` -- proves this is not "recursive Lemma      **)
(** touching opaque strings never works": that lemma's recursive step never  **)
(** calls `FStar.String.list_of_string`/`string_of_list`/`list_of_concat`/   **)
(** `list_of_string_of_list`/`string_of_list_of_string` directly; it only    **)
(** consumes ALREADY-CLOSED facts from `Parser.FastString.Axioms`/           **)
(** `ConcatSpec` (proved ONCE, non-recursively, then fed in as black-box     **)
(** conclusions). The isolating control probe (`assume val myf : list char   **)
(** -> Tot int` in place of the ulib pair, otherwise the IDENTICAL recursive **)
(** shape) reproduces the SAME failure -- so this is not specific to         **)
(** `string`-typed values or to `FStar.String` either; it reproduces for any **)
(** opaque `Tot`-returning symbol once the RECURSIVE call's own postcondition**)
(** needs to be established from WITHIN that same recursive Lemma's body,    **)
(** for a goal shape this general.                                          **)
(**                                                                          **)
(** REFINED CONCLUSION: the wall is `FStar.String.list_of_string`/           **)
(** `string_of_list`'s coercion-pair axioms (`list_of_concat`,               **)
(** `list_of_string_of_list`, `string_of_list_of_string`) used INSIDE a      **)
(** SELF-RECURSIVE `let rec ... : Lemma ... (decreases cs) = match cs with   **)
(** ...` body -- not merely "chaining an equality through a separate         **)
(** hypothesis" as the earlier banner (above) characterised it. Every        **)
(** SUCCESSFUL use of this coercion pair in the landed tree (`Parser.        **)
(** FastString.ConcatSpec.lemma_strcat_empty_l/_r/_assoc`, this file's own   **)
(** `lemma_one_char_list_of_string`) is a NON-recursive, single-shot lemma;  **)
(** none of them is itself a `let rec`, and none is CALLED FROM WITHIN a     **)
(** recursive Lemma's OWN self-referential call chain at the point its       **)
(** postcondition is needed (`lemma_scan_iri_end_build_string` calls         **)
(** `lemma_strcat_assoc` fine -- but never touches the coercion pair         **)
(** directly, and never as the RECURSIVE call's own return value). Whether   **)
(** this is a genuine F* well-founded-recursion encoding limitation for      **)
(** this axiom shape, or a Z3 native-string-theory incompleteness specific   **)
(** to formulas built this way (the SMT encoding represents `string` as an   **)
(** uninterpreted `FString` sort with a `fuel_instrumented` recursive        **)
(** unfolding axiom for EVERY `let rec`-defined string-valued function --    **)
(** confirmed via `--log_queries`, `Probe*.build_string.fuel_instrumented`   **)
(** declared in the dumped `.smt2`), was not determined further -- distinct  **)
(** from this session's scope, and not needed to record the wall precisely. **)
(**                                                                          **)
(** ALSO ATTEMPTED, ALSO BLOCKED: approach candidate 2 (induct on `fs_byte_  **)
(** length s` via an `fs_byte_sub`-based self-decomposition, entirely        **)
(** avoiding `list_of_string`/`string_of_list`, staying inside the fs_byte_* **)
(** family that DOES recurse successfully per `lemma_scan_iri_end_build_     **)
(** string` above). The single-shot (non-recursive, so not hitting the wall  **)
(** above) base fact this route needs --                                     **)
(**   `fs_byte_sub s 0 1 ^ fs_byte_sub s 1 (fs_byte_length s - 1) == s`      **)
(** for `fs_byte_length s > 0` -- does NOT fall out of the existing bridging **)
(** lemmas (`fs_byte_sub_eq`, `fs_byte_length_eq`) alone: `fs_byte_sub_eq`   **)
(** routes through `Spec.slice_bytes`/`Spec.utf8_decode_all`, and            **)
(** reassembling two `slice_bytes` calls back into the original             **)
(** `Spec.utf8_bytes s` needs a decode-then-re-encode round-trip identity    **)
(** that `fs_byte_sub_eq`'s OWN banner already flags as "additional proof    **)
(** work, not attempted in this landing" (`Parser.FastString.fsti` lines     **)
(** ~127-138, "OFF-DOMAIN DIVERGENCE FROM THE PLAN"). Confirmed empirically   **)
(** (one probe, `Scratch.SelfSplitProbe.fst`, not committed): the bare       **)
(** decompose lemma above fails Error 19 "incomplete quantifiers" even       **)
(** calling `fs_byte_sub_eq` on both slices plus `fs_byte_length_eq` with no **)
(** further help -- a genuinely separate, un-started proof obligation        **)
(** (the `Spec.slice_bytes`/`utf8_decode_all` round trip), not the same wall **)
(** as the `list_of_string` one above. NOT reattempted further this landing  **)
(** per the guard-depth rule; recorded as the precise next rung for whoever   **)
(** picks candidate 2 back up, distinct from the coercion-pair-in-recursion  **)
(** wall this finding's main body characterises.                             **)
(**                                                                          **)
(** UPDATE (session 2026-08-11, slice-decode task): candidate 2's own        **)
(** missing piece -- "the `Spec.slice_bytes`/`utf8_decode_all` round trip"   **)
(** -- is landed below (`Parser.FastString.Spec.utf8_decode_all_slice_by_    **)
(** charcount`, Spec.fst Section 7), so `fs_byte_sub_eq`'s "OFF-DOMAIN        **)
(** DIVERGENCE FROM THE PLAN" note now has a discharging lemma               **)
(** (`fs_byte_sub_by_charcount`, below) -- CHAR-COUNT-indexed, per that      **)
(** Spec.fst section's own banner on why `is_cp_boundary` itself was not     **)
(** used as the hypothesis (a separate, harder, not-attempted converse       **)
(** theorem). Candidate 2's ORIGINAL "self-split at a single byte" shape     **)
(** (`fs_byte_sub s 0 1 ^ fs_byte_sub s 1 (...) == s`) is NOT re-attempted   **)
(** here -- it would need EXACTLY this same slice law plus the `is_cp_       **)
(** boundary`-to-charcount converse this session left as the next rung, to   **)
(** know that byte offset 1 actually IS a 1-character boundary for an        **)
(** arbitrary symbolic `s`. The char-count form sidesteps that entirely by   **)
(** taking the character count as the GIVEN, not something to recover from   **)
(** a byte position -- see `fs_byte_sub_by_charcount`'s own comment.         **)
(** ======================================================================== **)

/// `fs_byte_sub_eq`'s "OFF-DOMAIN DIVERGENCE FROM THE PLAN" note
/// (`Parser.FastString.fsti`, on `fs_byte_sub_eq` itself) named the
/// STRONGER theorem it did not attempt: that slicing on a codepoint
/// boundary recovers exactly the corresponding piece of the original
/// string's own codepoint structure, not merely "whatever
/// `slice_bytes`+`utf8_decode_all` compute". This is that theorem, in
/// CHAR-COUNT form (the byte offsets are the byte-lengths of encoded
/// char-count prefixes of `s`'s own codepoint list -- the caller
/// supplies `start`/`len` as a CHARACTER range, which is how every real
/// scanner in this codebase already tracks its own position, rather
/// than an already-computed byte offset it would need to independently
/// prove satisfies `Spec.is_cp_boundary`). Direct composition of
/// `fs_byte_sub_eq` (rewrites `fs_byte_sub` to its Spec formula) with
/// `Spec.utf8_decode_all_slice_by_charcount` (the slice law itself,
/// Parser.FastString.Spec.fst Section 7) -- no new induction needed.
val fs_byte_sub_by_charcount (s:string) (start len:nat)
  : Lemma (
      fs_byte_sub s
        (List.Tot.length (List.Tot.concatMap Spec.utf8_enc_char
                            (Spec.take_chars (FStar.String.list_of_string s) start)))
        (List.Tot.length (List.Tot.concatMap Spec.utf8_enc_char
                            (Spec.slice_chars (FStar.String.list_of_string s) start len)))
      == FStar.String.string_of_list (Spec.slice_chars (FStar.String.list_of_string s) start len))
let fs_byte_sub_by_charcount s start len =
  let cs = FStar.String.list_of_string s in
  let mid = Spec.slice_chars cs start len in
  let bstart = List.Tot.length (List.Tot.concatMap Spec.utf8_enc_char (Spec.take_chars cs start)) in
  let blen = List.Tot.length (List.Tot.concatMap Spec.utf8_enc_char mid) in
  fs_byte_sub_eq s bstart blen;
  Spec.utf8_decode_all_slice_by_charcount cs start len

(** ======================================================================== **)
(** #401 M1: `s == build_string (codes_of s)` -- THE missing bridging step   **)
(** the "SHARPENED FINDING" banner above named, now CLOSED. Session          **)
(** 2026-08-11, continuing #401.                                             **)
(**                                                                          **)
(** ROUTE THAT WORKS: two resources landed since the finding above was       **)
(** recorded make this provable WITHOUT ever touching                       **)
(** `list_of_string`/`string_of_list` INSIDE a self-recursive Lemma body --  **)
(** the exact thing the finding proved unprovable.                          **)
(**   (1) `Spec.utf8_decode_all_utf8_bytes_identity` (Parser.FastString.     **)
(**       Spec.fst Section 7, PR #409) -- `utf8_decode_all (utf8_bytes s)    **)
(**       == FStar.String.list_of_string s`, proved NON-recursively (its own **)
(**       proof is one call to the codepoint-list-level                     **)
(**       `utf8_decode_all_concatMap_identity`, which sidesteps the wall by  **)
(**       staying at the `list byte -> list char` level throughout).        **)
(**   (2) The finding's own diagnosis: the wall is specifically the coercion **)
(**       pair used INSIDE a self-recursive Lemma. A NON-recursive proof     **)
(**       that only COMPOSES already-closed facts is safe -- confirmed by    **)
(**       every successful use already in this file (`lemma_one_char_list_   **)
(**       of_string`, `demo_fs_byte_length_ab`, etc).                        **)
(**                                                                          **)
(** THE ONE recursive step still needed (`lemma_utf8_bytes_build_string`     **)
(** below) is SAFE because it recurses entirely at the `list byte`/         **)
(** `List.Tot.concatMap` level (an ordinary transparent inductive ADT, not   **)
(** the opaque `FString`-sorted coercion pair) -- the same "stay at the      **)
(** codepoint-list level" route the SHARPENED FINDING banner's own           **)
(** ROUTE THAT WORKS paragraph used for `lemma_ascii_utf8_bytes_length`/     **)
(** `_at` above. `list_of_string`/`string_of_list` appear only via ONE       **)
(** non-recursive call each: `lemma_one_char_list_of_string` at the cons     **)
(** case's LEAF (`one_char_string c` is a concrete, non-recursive witness,   **)
(** the same pattern `Spec.utf8_bytes_ascii_singleton`'s own hypothesis      **)
(** already uses), and `Spec.utf8_decode_all_utf8_bytes_identity`/           **)
(** `string_of_list_of_string` applied ONCE each, straight-line, in          **)
(** `lemma_list_of_build_string` / `lemma_ascii_string_is_build_string`      **)
(** below -- never chained through a recursive call's OWN postcondition.     **)
(** ======================================================================== **)

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"

/// FINDING, attempt 1 (recorded per CLAUDE.md rule #14): the first route
/// tried here proved `Spec.utf8_bytes (build_string cs) == concatMap
/// utf8_enc_char cs` BY INDUCTION on `cs` (cons case: IH + `Spec.
/// utf8_bytes_concat` + `Spec.utf8_bytes_ascii_singleton`). It reproduces
/// the SHARPENED FINDING's exact failure signature -- `fstar.exe --
/// query_stats` shows Error 19 "incomplete quantifiers" in 109ms (NOT a
/// timeout) at the recursive lemma's own goal, even though the recursive
/// body never calls `list_of_string`/`string_of_list` directly. Diagnosis:
/// `Spec.utf8_bytes` is ITSELF defined AS `concatMap utf8_enc_char
/// (list_of_string s)` (Section on `utf8_bytes`, above) and carries NO
/// restricting `.fsti` -- so merely MENTIONING `Spec.utf8_bytes (build_
/// string cs)` as a goal term inside a `let rec ... : Lemma` gives Z3's
/// fuel-instrumented unfolding axiom for that transparent definition an
/// opening to try (and fail) to unfold `list_of_string (build_string
/// cs)` on its own, independent of which lemmas the proof body supplies.
/// This SHARPENS the SHARPENED FINDING once more: the wall is not just
/// "`list_of_string`/`string_of_list` used inside a self-recursive
/// lemma" but "a TRANSPARENT function whose OWN definition contains
/// `list_of_string`/`string_of_list`, mentioned in a self-recursive
/// lemma's goal, at a call site built from a self-recursively-defined
/// string (`build_string`)" -- reproduces even via already-proven
/// black-box lemmas about that function, not just direct calls to the
/// coercion pair.
///
/// ROUTE THAT WORKS (below): never let `Spec.utf8_bytes`/`Spec.
/// utf8_decode_all` applied to a `build_string`-shaped argument appear
/// as a goal inside recursion. Instead: (1) get `fs_byte_length`/
/// `fs_byte_at` facts about `build_string cs` via the ALREADY-PROVEN,
/// non-recursive-at-this-call-site `lemma_build_string_byte_length`/
/// `_byte_at` (Axioms-opaque, no `Spec.utf8_bytes` unfolding involved);
/// (2) bridge those OPAQUE `fs_byte_*` facts to `Spec.utf8_bytes`'s
/// `List.Tot.index`/`length` via `fs_byte_length_eq`/`fs_byte_at_eq`
/// (single, non-recursive calls -- these hand Z3 an EQUALITY, not an
/// invitation to unfold); (3) do the SAME for the `concatMap utf8_enc_
/// char cs` side via the already-proven `lemma_ascii_utf8_bytes_length`/
/// `_at`; (4) conclude LIST equality via ulib's `FStar.List.Tot.
/// Properties.index_extensionality` (length + pointwise `index`), never
/// touching `list_of_string`/`string_of_list`/`Spec.utf8_bytes`'s
/// definition at all. The one recursive helper this route needs
/// (`nth_byte_index`) stays entirely at the PLAIN `list byte` level
/// (ordinary ADT, no opaque coercion pair, no strings) -- the same "list-
/// level reasoning is fine" pattern `lemma_ascii_utf8_bytes_length`/`_at`
/// above already rely on.
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

/// Plain-list helper (byte lists; no strings, no coercion pair): in
/// bounds, `nth_byte` agrees with `List.Tot.index`. Structural induction
/// on `bs` only -- safe (see banner above).
val nth_byte_index (bs : list Spec.byte) (i : nat{i < List.Tot.length bs})
  : Lemma (ensures Spec.nth_byte bs i == Some (List.Tot.index bs i))
          (decreases bs)
let rec nth_byte_index bs i =
  match bs with
  | hd :: tl -> if i = 0 then () else nth_byte_index tl (i - 1)

/// `build_string cs`'s UTF-8 byte-list length equals `List.Tot.length
/// cs` -- restated at the `Spec.utf8_bytes` level (rather than `fs_byte_
/// length`) via ONE non-recursive bridging call, so the index-
/// extensionality argument below can compare `Spec.utf8_bytes (build_
/// string cs)` and `concatMap utf8_enc_char cs` as ordinary lists.
val lemma_build_string_utf8_bytes_len (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (List.Tot.length (Spec.utf8_bytes (build_string cs)) == List.Tot.length cs)
let lemma_build_string_utf8_bytes_len cs =
  fs_byte_length_eq (build_string cs);
  lemma_build_string_byte_length cs

/// Pointwise: byte `i` of `build_string cs`'s UTF-8 encoding, read via
/// the TOTAL `Spec.nth_byte`. TWO traps found and fixed getting here
/// (both mundane elaboration issues, NOT the SHARPENED FINDING's wall --
/// recorded so neither is re-hit):
///   (1) an `ensures` typed via `List.Tot.index (Spec.utf8_bytes (build_
///       string cs)) i` needs `i < length (Spec.utf8_bytes (build_string
///       cs))` witnessed BEFORE the `val` elaborates -- the proof body's
///       own `lemma_build_string_utf8_bytes_len` call is too late to
///       supply it (Error 19 "Subtyping check failed" AT THE VAL, not
///       the proof). Fixed by stating the result via the TOTAL `Spec.
///       nth_byte` (unrestricted `i:nat`) instead of `List.Tot.index`.
///   (2) `Some (FStar.Char.int_of_char ...)` needs the `int_of_char`
///       result to already be witnessed `< 256` (the `Spec.byte`
///       refinement) at the CONSTRUCTION site -- exactly the trap this
///       file's own `lemma_ascii_utf8_bytes_at` banner (Section above)
///       already named and fixed via the `match ... Some b -> (b <:
///       nat) == ...` phrasing rather than `== Some (...)` directly;
///       same fix applied here.
/// Composes `nth_byte_index` (in-bounds via the length fact above),
/// `fs_byte_at_eq` (opaque bridge, single call), and the already-proven
/// `lemma_build_string_byte_at`.
val lemma_build_string_utf8_bytes_nth
    (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < List.Tot.length cs})
  : Lemma (ensures
      (match Spec.nth_byte (Spec.utf8_bytes (build_string cs)) i with
       | Some b -> (b <: nat) == FStar.Char.int_of_char (List.Tot.index cs i)
       | None -> False))
let lemma_build_string_utf8_bytes_nth cs i =
  lemma_build_string_utf8_bytes_len cs;
  nth_byte_index (Spec.utf8_bytes (build_string cs)) i;
  fs_byte_at_eq (build_string cs) i;
  lemma_build_string_byte_at cs i

/// The SAME pointwise fact for the `concatMap utf8_enc_char cs` side,
/// via `nth_byte_index` + the already-proven `lemma_ascii_utf8_bytes_at`
/// (Section above) -- same TOTAL-`nth_byte` / `match` shape, same
/// reason.
val lemma_concatMap_utf8_enc_char_nth
    (cs : list FStar.Char.char{all_ascii cs}) (i : nat{i < List.Tot.length cs})
  : Lemma (ensures
      (match Spec.nth_byte (List.Tot.concatMap Spec.utf8_enc_char cs) i with
       | Some b -> (b <: nat) == FStar.Char.int_of_char (List.Tot.index cs i)
       | None -> False))
let lemma_concatMap_utf8_enc_char_nth cs i =
  lemma_ascii_utf8_bytes_length cs;
  nth_byte_index (List.Tot.concatMap Spec.utf8_enc_char cs) i;
  lemma_ascii_utf8_bytes_at cs i

/// THE list-level bridge, closed: `build_string cs`'s UTF-8 encoding IS
/// `concatMap utf8_enc_char cs`, via `FStar.List.Tot.Properties.index_
/// extensionality` (length equality + pointwise `index` equality, both
/// established above by NON-recursive composition of already-proven
/// facts) -- no direct recursion over a `Spec.utf8_bytes`/`build_string`
/// goal anywhere in this proof (see the FINDING above for why that route
/// fails).
val lemma_utf8_bytes_build_string (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (Spec.utf8_bytes (build_string cs) == List.Tot.concatMap Spec.utf8_enc_char cs)
let lemma_utf8_bytes_build_string cs =
  let l1 = Spec.utf8_bytes (build_string cs) in
  let l2 = List.Tot.concatMap Spec.utf8_enc_char cs in
  lemma_build_string_utf8_bytes_len cs;
  lemma_ascii_utf8_bytes_length cs;
  let aux (i:nat) : Lemma (i < List.Tot.length cs ==> List.Tot.index l1 i == List.Tot.index l2 i) =
    if i < List.Tot.length cs then begin
      lemma_build_string_utf8_bytes_nth cs i;
      lemma_concatMap_utf8_enc_char_nth cs i;
      nth_byte_index l1 i;
      nth_byte_index l2 i
    end
  in
  FStar.Classical.forall_intro aux;
  FStar.List.Tot.Properties.index_extensionality l1 l2

#pop-options

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"

/// `list_of_string (build_string cs) == cs`, for ANY all-ASCII `cs` --
/// THE recursive-shaped fact the SHARPENED FINDING's minimal repro
/// (`lemma_list_of_build_string`, same name, same statement) showed
/// fails Error 19 when attempted BY INDUCTION on `cs`. Proved here
/// instead as a STRAIGHT-LINE, non-recursive composition of three
/// already-closed facts (the safe route): (1) the list-level bridge
/// above, (2) `utf8_decode_all_utf8_bytes_identity` applied to `s =
/// build_string cs` (decoding `build_string cs`'s own encoding gives
/// back its `list_of_string`), (3) `utf8_decode_all_concatMap_identity`
/// applied to `cs` directly (decoding `concatMap utf8_enc_char cs` gives
/// back `cs`) -- (1) identifies the two decode inputs as the SAME byte
/// list, so (2) and (3)'s conclusions chain by ordinary congruence.
val lemma_list_of_build_string (cs : list FStar.Char.char{all_ascii cs})
  : Lemma (FStar.String.list_of_string (build_string cs) == cs)
let lemma_list_of_build_string cs =
  lemma_utf8_bytes_build_string cs;
  Spec.utf8_decode_all_utf8_bytes_identity (build_string cs);
  Spec.utf8_decode_all_concatMap_identity cs

/// THE missing bridging step itself: any string `s` whose own codepoint
/// list is all-ASCII equals `build_string` of that codepoint list.
/// Straight-line composition of `lemma_list_of_build_string` above with
/// ulib's `string_of_list_of_string` coercion-pair lemma, called ONCE
/// each on `s` and on `build_string (list_of_string s)` (never inside a
/// recursive call) -- the safe, non-recursive use the SHARPENED FINDING
/// banner identified as always working.
val lemma_ascii_string_is_build_string (s : string)
  : Lemma (requires all_ascii (FStar.String.list_of_string s))
          (ensures  build_string (FStar.String.list_of_string s) == s)
let lemma_ascii_string_is_build_string s =
  let cs = FStar.String.list_of_string s in
  lemma_list_of_build_string cs;
  FStar.String.string_of_list_of_string s;
  FStar.String.string_of_list_of_string (build_string cs)

#pop-options

(** ======================================================================== **)
(** `Parser.FastString.BaseCases`-flavored sibling, for `RDF.NTriples.        **)
(** RoundTrip.fst`'s consumer -- session 2026-08-11, continuing #401 M1.      **)
(**                                                                          **)
(** `RDF.NTriples.RoundTrip.fst`'s Part 7 (`lemma_scan_iri_end_build_        **)
(** string`, `lemma_term_iri_round_trip_build_string`, etc.) `open`s          **)
(** `Parser.FastString.BaseCases`, NOT this module -- so its `build_string`/  **)
(** `all_ascii` are `Parser.FastString.BaseCases`'s OWN definitions, a        **)
(** SEPARATE (structurally identical, nominally distinct) pair from THIS      **)
(** module's `build_string`/`all_ascii` above. The bridging lemma the        **)
(** consumer needs must be proven for THAT pair, via `module BC = ...`        **)
(** qualification (not `open`, which would shadow this module's own          **)
(** same-named definitions).                                                 **)
(**                                                                          **)
(** MUCH SHORTER ROUTE available here: `Parser.FastString.BaseCases.fst`     **)
(** already carries `lemma_build_string_utf8_bytes (cs) : Spec.utf8_bytes    **)
(** (BC.build_string cs) == BC.codes_of cs` -- ALREADY PROVEN, and (session   **)
(** finding) it verifies DESPITE being the exact recursive induction shape    **)
(** (`Spec.utf8_bytes_concat` + `Spec.utf8_bytes_ascii_singleton` + IH) that  **)
(** failed Error 19 "incomplete quantifiers" for THIS module's `build_       **)
(** string` when the RHS was `List.Tot.concatMap Spec.utf8_enc_char cs`.      **)
(** The difference isolating the discrepancy: `BC.codes_of cs` is built by    **)
(** plain CONS (`int_of_char c :: codes_of rest`), never touching             **)
(** `List.Tot.concatMap`/`append` at all, and `Parser.FastString.BaseCases    **)
(** .fst` uses NO `#push-options` (default fuel 2/ifuel 1) where this         **)
(** module's failed attempt inherited `--fuel 4 --ifuel 4` from its own       **)
(** outer block -- consistent with this project's existing "more fuel does    **)
(** not always help, and can hurt" experience (`docs/claude-rules/` /         **)
(** `fstar-module-style` skill). NOT fully isolated which factor is           **)
(** load-bearing (out of scope for this landing); recorded as a candidate     **)
(** explanation, not a re-litigated wall.                                     **)
(**                                                                          **)
(** Given `lemma_build_string_utf8_bytes`'s free ride, the missing piece is   **)
(** just `Spec.utf8_decode_all (BC.codes_of cs) == cs` -- closed by a ONE-    **)
(** LINE, purely LIST-level (no strings, safe) lemma showing `BC.codes_of cs  **)
(** == List.Tot.concatMap Spec.utf8_enc_char cs` for all-ASCII `cs` (both     **)
(** sides reduce to the same `int_of_char c :: ...`/`[int_of_char c] @ ...`   **)
(** shape), then reusing `Spec.utf8_decode_all_concatMap_identity` (already   **)
(** proven, general, no `all_ascii` hypothesis needed) as a black box.        **)
(** ======================================================================== **)

module BC = Parser.FastString.BaseCases

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"

/// `codes_of cs` (BaseCases' plain-cons construction) and `concatMap
/// utf8_enc_char cs` (this module's construction) carry the SAME byte
/// list, for all-ASCII `cs` -- purely list-level induction (no strings
/// anywhere in this proof), safe per the established pattern.
val bc_codes_of_is_concatMap (cs : list FStar.Char.char{BC.all_ascii cs})
  : Lemma (ensures BC.codes_of cs == List.Tot.concatMap Spec.utf8_enc_char cs)
          (decreases cs)
let rec bc_codes_of_is_concatMap cs =
  match cs with
  | [] -> ()
  | c :: rest -> bc_codes_of_is_concatMap rest

/// Decoding `codes_of cs` (any all-ASCII `cs`) recovers `cs` exactly --
/// via the list-level identity above plus `Spec.utf8_decode_all_
/// concatMap_identity` (already proven for ANY `cs`, no `all_ascii`
/// hypothesis needed there).
val bc_utf8_decode_all_codes_of_identity (cs : list FStar.Char.char{BC.all_ascii cs})
  : Lemma (Spec.utf8_decode_all (BC.codes_of cs) == cs)
let bc_utf8_decode_all_codes_of_identity cs =
  bc_codes_of_is_concatMap cs;
  Spec.utf8_decode_all_concatMap_identity cs

/// `list_of_string (BC.build_string cs) == cs`, for BaseCases' `build_
/// string`/`all_ascii` pair -- straight-line, non-recursive composition
/// of `BC.lemma_build_string_utf8_bytes` (already proven, in BaseCases),
/// `Spec.utf8_decode_all_utf8_bytes_identity` (already proven, Section 7
/// of Spec.fst), and the list-level identity just above.
val bc_lemma_list_of_build_string (cs : list FStar.Char.char{BC.all_ascii cs})
  : Lemma (FStar.String.list_of_string (BC.build_string cs) == cs)
let bc_lemma_list_of_build_string cs =
  BC.lemma_build_string_utf8_bytes cs;
  Spec.utf8_decode_all_utf8_bytes_identity (BC.build_string cs);
  bc_utf8_decode_all_codes_of_identity cs

/// THE missing bridging step, for `RDF.NTriples.RoundTrip.fst`'s
/// consumer: any string `s` whose own codepoint list is all-ASCII
/// (`BaseCases.all_ascii`) equals `BaseCases.build_string` of that
/// codepoint list. Same straight-line shape as `lemma_ascii_string_is_
/// build_string` above, one module over.
val lemma_ascii_string_is_build_string_bc (s : string)
  : Lemma (requires BC.all_ascii (FStar.String.list_of_string s))
          (ensures  BC.build_string (FStar.String.list_of_string s) == s)
let lemma_ascii_string_is_build_string_bc s =
  let cs = FStar.String.list_of_string s in
  bc_lemma_list_of_build_string cs;
  FStar.String.string_of_list_of_string s;
  FStar.String.string_of_list_of_string (BC.build_string cs)

#pop-options
