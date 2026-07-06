module SPARQL.FullText

(** ======================================================================== **)
(** Fulltext SPARQL extension — Slice 1 (exact/token match, no scoring)      **)
(**                                                                          **)
(** Design: docs/designissues/2026-07-05-fulltext-sparql-design.md          **)
(** Implements the doc's §2.2 module split ("spec side", mirrors            **)
(** RDF.CottasStore.PresenceBitmap.fst's pattern of Tot functions verified   **)
(** separately from any writer/consumer) and §6's Slice 1 scope:            **)
(**   - the `text:query` AST (`fulltext_query`)                             **)
(**   - the pure-F* default tokenizer (§2.1: lowercase + punctuation split)  **)
(**   - the match predicate over token lists (all-tokens/AND mode, §7)      **)
(** No `score_bm25`/`rank_results` yet (Slice 2, §6) — this module makes no  **)
(** ranking claim; callers apply `ftq_limit` in dataset order only.         **)
(**                                                                          **)
(** Zero new `assume val`s (design doc §2.2's slice-1 selling point): the    **)
(** tokenizer's case-fold is a small self-contained ASCII fold rather than   **)
(** reusing SPARQL11.Algebra's `string_lowercase_unicode` assume val — that  **)
(** assume val lives in a module that (via the dispatch wiring in §3) ends   **)
(** up depending on THIS module, so reusing it here would cycle the graph.   **)
(** The task brief's stated floor ("ASCII + common punctuation word-        **)
(** splitting") is exactly this; Unicode-aware analysis is the doc's        **)
(** slice-3 ASSUME-HOST seam (`analyze_text`), not slice 1.                 **)
(**                                                                          **)
(** Object-argument encoding (deviation from a literal reading of design    **)
(** doc §3's dispatch sketch — see this file's own banner further down):    **)
(** jena-text's list-argument form `(property "term" limit)` is ordinary    **)
(** SPARQL collection syntax, which our parser (like Jena's) desugars into  **)
(** an `rdf:first`/`rdf:rest` chain living in a SIBLING `group_graph_pattern`**)
(** joined to the main triple (`SPARQL11.Parser.fst`'s `ggp_join`), not a   **)
(** second triple pattern in the SAME `bgp` list the doc's per-triple hook  **)
(** (`eval_single_tp_store`/`eval_single_tp_backend`) sees. Resolving that   **)
(** generically would need a `group_graph_pattern`-level rewrite pass (a    **)
(** query-planning restructuring out of slice-1 scope, and NOT what real    **)
(** magic-property engines do either — Jena's ARQ intercepts the argument   **)
(** list during algebra compilation, before it would ever become literal    **)
(** `rdf:first`/`rdf:rest` matching against data that doesn't have those    **)
(** triples). This module's `SPARQL11.Parser` caller instead recognizes the **)
(** `text:query` predicate directly at parse time (before the generic       **)
(** collection desugaring runs) and encodes the resolved `fulltext_query`   **)
(** into a single internally-tagged `wf_literal` (this module's            **)
(** `encode_fulltext_literal`/`decode_fulltext_literal`) that both eval      **)
(** hooks decode back out of `tp.tp_o`. User-visible SPARQL syntax is       **)
(** unaffected — `?s text:query "term"`, `(?s) text:query (rdfs:label       **)
(** "term")`, and `(rdfs:label "term" 10)` all parse and evaluate — only    **)
(** the internal AST shape differs from a literal collection expansion.    **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable

(** ------------------------------------------------------------------ **)
(** 1. Vocabulary — jena-text's `http://jena.apache.org/text#` namespace **)
(** ------------------------------------------------------------------ **)

(* design doc §1 recommendation + §7 open decision 1: reuse the IRI
   verbatim, maximizing probe/tool compatibility with jena-text query text. *)
let fulltext_query_pred : wf_iri =
  assert_norm (is_iri "http://jena.apache.org/text#query");
  "http://jena.apache.org/text#query"

(* Internal marker datatype carrying the parsed (field, term, limit)
   argument tuple through the ordinary pattern_term/wf_literal AST — see
   `encode_fulltext_literal`/`decode_fulltext_literal` below and this
   file's banner. Never appears in user-visible RDF data; SPARQL11.Parser
   is the only producer, the two eval hooks the only consumers. *)
let fulltext_args_datatype : wf_iri =
  assert_norm (is_iri "http://jena.apache.org/text#query-args");
  "http://jena.apache.org/text#query-args"

(* design doc §2.2's `fulltext_query` record verbatim: `ftq_field = None`
   is jena-text's bare-string 2-arity form. *)
noeq type fulltext_query = {
  ftq_field : option wf_iri;
  ftq_terms : string;
  ftq_limit : option nat;
}

(** ------------------------------------------------------------------ **)
(** 2. Default tokenizer — design doc §2.1/§2.2, slice 1                **)
(** ------------------------------------------------------------------ **)

let is_ascii_digit (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 0x30 && n <= 0x39

let is_ascii_upper (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 0x41 && n <= 0x5A

let is_ascii_lower_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 0x61 && n <= 0x7A

let is_ascii_alnum (c : FStar.Char.char) : bool =
  is_ascii_digit c || is_ascii_upper c || is_ascii_lower_char c

let ascii_fold_char (c : FStar.Char.char) : FStar.Char.char =
  if is_ascii_upper c then FStar.Char.char_of_int (FStar.Char.int_of_char c + 32) else c

let rec ascii_fold_chars (cs : list FStar.Char.char) : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest -> ascii_fold_char c :: ascii_fold_chars rest

(* ASCII-only case fold — see module banner for why this doesn't reuse
   SPARQL11.Algebra's `string_lowercase_unicode` assume val. *)
let ascii_lowercase (s : string) : Tot string =
  FStar.String.string_of_list (ascii_fold_chars (FStar.String.list_of_string s))

let rec split_words_acc
  (cs : list FStar.Char.char) (cur : list FStar.Char.char) (acc : list string)
  : Tot (list string) (decreases cs) =
  match cs with
  | [] ->
    if List.Tot.length cur = 0 then List.Tot.rev acc
    else List.Tot.rev (FStar.String.string_of_list (List.Tot.rev cur) :: acc)
  | c :: rest ->
    if is_ascii_alnum c
    then split_words_acc rest (c :: cur) acc
    else if List.Tot.length cur = 0
    then split_words_acc rest [] acc
    else split_words_acc rest [] (FStar.String.string_of_list (List.Tot.rev cur) :: acc)

(* Design doc §2.1: "A default tokenizer (whitespace/punctuation split +
   lowercase) lives entirely in F* for slice 1." Non-ASCII bytes act as
   word separators (documented floor, not a bug — see module banner and
   `fulltext_stemming_off_baseline_regressions.sh`-style pin in the local
   test suite; slice 3's `analyze_text` seam is where Unicode analysis
   lands). *)
let default_tokenizer (s : string) : Tot (list string) =
  split_words_acc (FStar.String.list_of_string (ascii_lowercase s)) [] []

(** ------------------------------------------------------------------ **)
(** 3. Match semantics — all-tokens (AND) mode, design doc §7 slice-1   **)
(**    recommendation ("AND-by-default", open decision 3)              **)
(** ------------------------------------------------------------------ **)

let match_tokens (query_tokens candidate_tokens : list string) : Tot bool =
  List.Tot.for_all (fun qt -> List.Tot.mem qt candidate_tokens) query_tokens

let literal_matches_query (ftq : fulltext_query) (l : wf_literal) : Tot bool =
  match_tokens (default_tokenizer ftq.ftq_terms) (default_tokenizer l.lexical_form)

(** ------------------------------------------------------------------ **)
(** 4. Object-argument codec — see module banner for why this exists    **)
(**    instead of resolving a genuine RDF collection at the dispatch    **)
(**    point. `unit_sep` (ASCII Unit Separator, 0x1F) is a control byte  **)
(**    no realistic search term or field IRI contains.                  **)
(** ------------------------------------------------------------------ **)

let unit_sep : FStar.Char.char = FStar.Char.char_of_int 31
let unit_sep_str : string = FStar.String.string_of_list [unit_sep]

let rec split_on_char_acc
  (delim : FStar.Char.char) (cur : list FStar.Char.char)
  (cs : list FStar.Char.char) (acc : list string)
  : Tot (list string) (decreases cs) =
  match cs with
  | [] -> List.Tot.rev (FStar.String.string_of_list (List.Tot.rev cur) :: acc)
  | c :: rest ->
    if c = delim
    then split_on_char_acc delim [] rest (FStar.String.string_of_list (List.Tot.rev cur) :: acc)
    else split_on_char_acc delim (c :: cur) rest acc

let split_on_char (delim : FStar.Char.char) (s : string) : Tot (list string) =
  split_on_char_acc delim [] (FStar.String.list_of_string s) []

// `op_Multiply acc 10`, not `acc * 10` — inside this recursive call `*`
// parses as the tuple-type former, not arithmetic multiplication
// (same trap SPARQL11.Parser.fst's `chars_to_int` already works around).
// Accumulates in `int`, not `nat`: the digit-ness of `cs` (which is what
// makes the running total non-negative) is only checked by the caller
// (`string_to_nat`'s `for_all is_ascii_digit` guard below), not carried
// here as a refinement, so `nat` couldn't be proved inductively anyway.
let rec chars_to_int_digits (cs : list FStar.Char.char) (acc : int) : Tot int (decreases cs) =
  match cs with
  | [] -> acc
  | c :: rest -> chars_to_int_digits rest (op_Multiply acc 10 + (FStar.Char.int_of_char c - 0x30))

let string_to_nat (s : string) : Tot (option nat) =
  let cs = FStar.String.list_of_string s in
  if List.Tot.length cs = 0 then None
  else if List.Tot.for_all is_ascii_digit cs then
    let v = chars_to_int_digits cs 0 in
    if v >= 0 then Some (v <: nat) else None
  else None

(* Encode a resolved fulltext_query into a single wf_literal carrying a
   private marker datatype. `field`/`limit` metadata rides in the lexical
   form (delimited by `unit_sep`), NOT the datatype IRI, so the user's
   raw search term (`ftq_terms`) is never itself parsed/escaped — only
   split out of its two neighbouring delimiter-bounded slots. *)
let encode_fulltext_literal (ftq : fulltext_query) : Tot wf_literal =
  let field_part : string = (match ftq.ftq_field with | None -> "" | Some f -> f) in
  let limit_part : string = (match ftq.ftq_limit with | None -> "" | Some n -> string_of_int n) in
  let lex = field_part ^ unit_sep_str ^ ftq.ftq_terms ^ unit_sep_str ^ limit_part in
  { lexical_form = lex; datatype = fulltext_args_datatype; lang_tag = None }

let decode_fulltext_literal (l : wf_literal) : Tot (option fulltext_query) =
  if l.datatype <> fulltext_args_datatype then None
  else
    match split_on_char unit_sep l.lexical_form with
    | [field_part; term; limit_part] ->
      let field : option wf_iri =
        if FStar.String.length field_part = 0 then None
        else if is_iri field_part then Some field_part else None in
      let limit : option nat =
        if FStar.String.length limit_part = 0 then None else string_to_nat limit_part in
      Some ({ ftq_field = field; ftq_terms = term; ftq_limit = limit })
    | _ -> None

(* True iff a candidate DATA triple's object literal matches a resolved
   fulltext_query — the per-candidate filter both eval hooks apply after
   fetching the field-restricted (or unrestricted) candidate set from the
   backend. Takes the object as `rdf_term` since that is what a `triple`
   record's `.o` field carries (SPARQL11.Algebra/SPARQL11.Store's
   `RDF.Graph.Executable.triple`), independent of the query-side
   `pattern_term`/`wf_literal` encoding this module cannot reference
   (that type lives in SPARQL11.Algebra, which depends on this module —
   see module banner). *)
let object_matches_query (ftq : fulltext_query) (o : rdf_term) : Tot bool =
  match o with
  | T_Literal l -> literal_matches_query ftq l
  | _ -> false
