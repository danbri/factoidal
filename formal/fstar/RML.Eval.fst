module RML.Eval

// Stage 2 of the RML program plan
// (docs/designissues/2026-07-05-rml-program-plan.md): term-map
// evaluation (constant/reference/template, with rml:termType IRI/URI/
// UnsafeIRI/BlankNode/Literal, rml:datatype(Map)/rml:language(Map)
// cartesian products, and RML-Core's IRI-safe/URI-safe percent-encoding
// for template-generated IRIs) plus triples-map evaluation (subject +
// predicate-object maps -> triples, target-graph routing). Joins
// (rml:parentTriplesMap/joinCondition, Stage 5) and RML-CC/RML-FNML
// (Stages 6-7) are out of scope — OB_Join object bindings are decoded
// but skipped here (produce no triples).
//
// Stage 3 addendum: reference/template evaluation was generalized from
// JSON-only to dispatch on `source_row` (see
// reference_natural_values/reference_cast_strings below) so CSV rows
// (RML.Sources' Row_CSV, always-xsd:string natural typing per the
// RML-IO spec) flow through the same term-map machinery JSON rows
// already used. `eval_triples_map` now takes an already-iterated
// `list source_row` directly (format-agnostic); `eval_triples_map_json`
// / `eval_triples_map_csv` are thin per-format convenience wrappers
// that call RML.Sources' json_iterate/csv_iterate first.
//
// Term-generation rules, default-term-type table, natural JSON->RDF
// mapping, and the IRI-safe/URI-safe percent-encoding tables are taken
// verbatim from the RML-Core spec (kg-construct.github.io/rml-core,
// sections 8.3.1/8.4.1/8.4.2/8.5/8.6/11.1/12.1/12.2) and the RML-IO
// Registry's JSONPath natural-mapping fragment
// (raw.githubusercontent.com/kg-construct/rml-io-registry, main,
// json-path/section/natural-rdf-mapping.md), fetched directly rather
// than guessed — see inline comments at each rule below for the exact
// clause being implemented.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open RML.Mapping
open RML.Sources
open Parser.JSON
open SPARQL11.Algebra  // reused: percent_encode_char, is_uri_unreserved, string_encode_uri (rml:URI's "URI-safe" encoding, RFC3986 unreserved)

// ------------------------------------------------------------------
// 1. IRI-safe percent-encoding (rml:IRI's template encoding, RFC3987
//    `iunreserved` production — spec section 8.3.1). rml:URI's
//    "URI-safe" version (RFC3986 `unreserved`, ASCII-only) is
//    SPARQL11.Algebra's existing string_encode_uri (ENCODE_FOR_URI),
//    reused as-is rather than reimplemented.
// ------------------------------------------------------------------

// RFC 3987 ucschar ranges: most of the non-ASCII BMP/supplementary-plane
// codepoints (excludes surrogates, most punctuation/symbol blocks, and
// the private-use areas). Table verified against spec Example 9
// ("Zoë Krüger" -> "Zoë%20Krüger": only the space is encoded, ë/ü are
// within %xA0-D7FF and stay raw).
let is_iunreserved (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  is_uri_unreserved c ||
  (code >= 0xA0 && code <= 0xD7FF) ||
  (code >= 0xF900 && code <= 0xFDCF) ||
  (code >= 0xFDF0 && code <= 0xFFEF) ||
  (code >= 0x10000 && code <= 0x1FFFD) ||
  (code >= 0x20000 && code <= 0x2FFFD) ||
  (code >= 0x30000 && code <= 0x3FFFD) ||
  (code >= 0x40000 && code <= 0x4FFFD) ||
  (code >= 0x50000 && code <= 0x5FFFD) ||
  (code >= 0x60000 && code <= 0x6FFFD) ||
  (code >= 0x70000 && code <= 0x7FFFD) ||
  (code >= 0x80000 && code <= 0x8FFFD) ||
  (code >= 0x90000 && code <= 0x9FFFD) ||
  (code >= 0xA0000 && code <= 0xAFFFD) ||
  (code >= 0xB0000 && code <= 0xBFFFD) ||
  (code >= 0xC0000 && code <= 0xCFFFD) ||
  (code >= 0xD0000 && code <= 0xDFFFD) ||
  (code >= 0xE1000 && code <= 0xEFFFD)

let rec encode_iri_chars (cs : list FStar.Char.char) : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest ->
    if is_iunreserved c then c :: encode_iri_chars rest
    else List.Tot.append (percent_encode_char c) (encode_iri_chars rest)

// rml:IRI's template reference-value transform (IRI-safe, spec 8.3.1).
let string_encode_iri (s : string) : string =
  String.string_of_list (encode_iri_chars (String.list_of_string s))

// ------------------------------------------------------------------
// 2. Natural RDF mapping of JSON values (RML-IO Registry, JSONPath
//    reference formulation's natural-rdf-mapping fragment):
//      number without a fraction/exponent marker -> xsd:integer
//      number with a fraction/exponent marker     -> xsd:double
//      boolean                                    -> xsd:boolean
//      string                                     -> xsd:string
//    null / array / object leaves have no natural RDF literal (no term
//    is generated for that candidate — spec 12.2's "If the value is
//    null, empty, or missing, then no RDF term is generated").
// ------------------------------------------------------------------

let is_frac_or_exp_marker (c : FStar.Char.char) : bool =
  let i = FStar.Char.int_of_char c in i = 0x2E (* '.' *) || i = 0x65 (* 'e' *) || i = 0x45 (* 'E' *)

let json_number_natural_datatype (lex : string) : wf_iri =
  if List.Tot.existsb is_frac_or_exp_marker (String.list_of_string lex)
  then xsd_double else xsd_integer

// (lexical form, natural datatype) for a scalar JSON value; None for
// null/array/object (no natural RDF literal exists for those per 12.2).
let json_natural_value (v : json_val) : option (string & wf_iri) =
  match v with
  | JString s -> Some (s, xsd_string)
  | JNumber s -> Some (s, json_number_natural_datatype s)
  | JBool b   -> Some ((if b then "true" else "false"), xsd_boolean)
  | JNull     -> None
  | JArray _  -> None
  | JObject _ -> None

// Cast-to-string only (used when embedding a reference's value into a
// template expansion — 11.1's "natural RDF lexical form ... used when
// non-string expression evaluation results are used in a string
// context").
let json_natural_cast_string (v : json_val) : option string =
  match json_natural_value v with
  | Some (s, _) -> Some s
  | None -> None

// ------------------------------------------------------------------
// 2b. Stage 3: source-agnostic reference evaluation. RML.Sources'
//     json_reference_values (JSONPath over json_val, natural datatype
//     inferred by json_natural_value: number/bool/string) and
//     csv_reference_values (bare column-name lookup over a CSV row,
//     always xsd:string per the RML-IO spec's "CSV has no natural
//     number/boolean mapping" — RMLSTC0004a's age column round-trips
//     as the plain string "33", not xsd:integer) both reduce to "0 or
//     more (lexical form, natural datatype) pairs" — this is the one
//     dispatch point the rest of the module (template expansion,
//     plain-string evaluation, term-map evaluation) goes through, so
//     adding another source format (XML, Stage 4) only touches this
//     function, not every caller.
// ------------------------------------------------------------------

let reference_natural_values (row : source_row) (path : string) : list (string & wf_iri) =
  match row with
  | Row_JSON _ ->
    List.Tot.concatMap
      (fun v -> match json_natural_value v with Some p -> [p] | None -> [])
      (json_reference_values row path)
  | Row_CSV _ ->
    List.Tot.map (fun v -> (v, xsd_string)) (csv_reference_values row path)

let reference_cast_strings (row : source_row) (path : string) : list string =
  List.Tot.map fst (reference_natural_values row path)

// ------------------------------------------------------------------
// 3. Template expansion: cross-multiply literal segments (verbatim,
//    never encoded) with reference segments (each matched value cast to
//    its natural string, then percent-encoded per the caller-supplied
//    `encode` function — None for BlankNode/Literal/UnsafeIRI targets,
//    Some string_encode_iri for rml:IRI, Some string_encode_uri for
//    rml:URI, per spec 8.3.1's scoping to template-valued term maps
//    only). Structural recursion on the segment list — no fuel needed.
// ------------------------------------------------------------------

let rec build_template_product
    (segs : list template_segment) (encode : option (string -> string)) (row : source_row)
  : Tot (list string) (decreases segs) =
  match segs with
  | [] -> [""]
  | TSeg_Literal l :: rest ->
    let tails = build_template_product rest encode row in
    List.Tot.map (fun t -> l ^ t) tails
  | TSeg_Reference r :: rest ->
    let vals = reference_cast_strings row r in
    let vals_enc = (match encode with Some f -> List.Tot.map f vals | None -> vals) in
    let tails = build_template_product rest encode row in
    List.Tot.concatMap (fun v -> List.Tot.map (fun t -> v ^ t) tails) vals_enc

let eval_template_strings (encode : option (string -> string)) (raw : string) (row : source_row) : list string =
  build_template_product (parse_template raw) encode row

// ------------------------------------------------------------------
// 4. Term-map evaluation.
// ------------------------------------------------------------------

// Which structural role a term map plays — needed for the default
// term-type rule (spec 8.4.1), which depends on position.
type map_role =
  | MR_Subject
  | MR_Predicate
  | MR_Graph
  | MR_Object

let is_reference_form (form : term_map_form) : bool =
  match form with TMF_Reference _ -> true | _ -> false

// spec 8.4.1 Default Term Types (verbatim):
//   "If the term map does not have a rml:termType property, then its
//    term type is: rml:IRI, if it is a subject map, predicate map or
//    graph map; rml:Literal, if it is an object map and at least one of
//    the following conditions is true (rml:IRI, otherwise): it is a
//    reference-valued term map; it has a rml:languageMap property; it
//    has a rml:datatypeMap property."
// (RML.Mapping decodes the rml:datatype/rml:language *shortcuts* into
// the same tmap_datatype/tmap_language fields as the Map forms, so
// checking Some?/None on those fields covers both spellings.)
let effective_term_type (role : map_role) (tm : term_map) : term_type =
  match tm.tmap_termtype with
  | Some tt -> tt
  | None ->
    (match role with
     | MR_Subject | MR_Predicate | MR_Graph -> TT_IRI
     | MR_Object ->
       if is_reference_form tm.tmap_form || Some? tm.tmap_datatype || Some? tm.tmap_language
       then TT_Literal else TT_IRI)

// RML-side stricter absolute-IRI gate (rule #-blast-radius: do NOT
// change the shared RDF.Graph.Executable.is_iri predicate — it is used
// throughout the codebase and other parsers already enforce their own
// concrete-syntax grammars before a value reaches it). is_iri's coarse
// "non-empty + contains a colon" check accepts a base-IRI-prepended
// string that still contains a raw space: RMLTC0019b's subject map is a
// bare `rml:reference "$.FirstName"` (termType defaults to rml:IRI for
// subject maps, no template, so no percent-encoding step ever runs —
// see eval_term_map's TMF_Reference branch) whose value "Juan Daniel"
// has no colon (is_iri false), but combined with the fixture's
// base_iri "http://example.com/" gives "http://example.com/Juan
// Daniel", which DOES contain a colon and previously sailed through as
// "valid". Reject raw control bytes (0x00-0x20, covering space) plus
// the handful of delimiters RFC3987 excludes from every IRI reference
// (<>"{}|\^`) — same exclusion set as Parser.JSONLD.fst's
// jld_forbidden_byte, same "honest subset, not a full grammar" scope.
let rml_forbidden_iri_byte (b : int) : bool =
  (b >= 0 && b <= 0x20) || b = 0x3C (* < *) || b = 0x3E (* > *) || b = 0x22 (* " *)
  || b = 0x7B (* { *) || b = 0x7D (* } *) || b = 0x7C (* | *) || b = 0x5C (* \ *)
  || b = 0x5E (* ^ *) || b = 0x60 (* ` *)

let rec rml_iri_scan_wf (s : string) (pos : nat) (fuel : nat) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else
    let len = String.length s in
    if pos >= len then true
    else if rml_forbidden_iri_byte (FStar.Char.int_of_char (String.index s pos)) then false
    else rml_iri_scan_wf s (pos + 1) (fuel - 1)

let rml_is_valid_absolute_iri (s : string) : bool =
  is_iri s && rml_iri_scan_wf s 0 (String.length s + 1)

// spec 12.2: "If the term type is rml:IRI/rml:UnsafeIRI/rml:URI/
// rml:UnsafeURI: let value be the natural RDF lexical form...; if value
// is a valid absolute IRI/URI, return an IRI/URI generated from value;
// otherwise prepend the base IRI and re-check; otherwise raise a data
// error [-> no term generated, here]."
//
// `strict` selects which absolute-IRI approximation gates the value:
//   - true (rml:IRI / rml:URI): rml_is_valid_absolute_iri (above) —
//     RMLTC0019b's "Juan Daniel" (raw space surviving base-IRI
//     prepending) must raise a data error. Used uniformly for both the
//     IRI and URI branches since a stricter RFC3986-vs-3987
//     absolute-reference distinction isn't implemented elsewhere in
//     the codebase either.
//   - false (rml:UnsafeIRI): the shared coarse is_iri only (non-empty
//     + colon) — producing IRIREF-illegal bytes is UnsafeIRI's entire
//     point (spec 8.3.1 defines it as skipping percent-encoding;
//     RMLTC0027b's expected output carries a literal
//     "<http://example.com/Person/Emily Smith>"), so the strict byte
//     scan must not run for it.
let iri_like_term_gated (strict : bool) (value : string) (base_iri : option string) : option rdf_term =
  let ok (s : string) : bool = if strict then rml_is_valid_absolute_iri s else is_iri s in
  if ok value then Some (T_IRI value)
  else
    match base_iri with
    | Some b -> let combined = b ^ value in if ok combined then Some (T_IRI combined) else None
    | None -> None

// Strict variant under the original name — every non-UnsafeIRI call
// site (datatype maps' eval_iri_valued_strings, finalize_value's
// TT_IRI/TT_URI branch) wants the strict gate.
let iri_like_term (value : string) (base_iri : option string) : option rdf_term =
  iri_like_term_gated true value base_iri

// Evaluate a term map's constant/reference/template expression *only*
// (ignoring tmap_termtype/datatype/language), casting every candidate to
// a plain string. Used for language maps, datatype maps, and (via the
// join-condition child/parent maps, Stage 5) anywhere the spec treats a
// term map as a bare "expression map" rather than a full term map.
let eval_plain_strings (tm : term_map) (row : source_row) : list string =
  match tm.tmap_form with
  | TMF_Constant t ->
    (match t with
     | T_IRI i -> [i]
     | T_Literal l -> [l.lexical_form]
     | T_BNode _ -> [])
  | TMF_Reference r -> reference_cast_strings row r
  | TMF_Template t -> eval_template_strings None t row
  | TMF_Unknown -> []

// Build the well-formed literal(s) for one base (lexical, natural
// datatype) pair, applying spec 8.5/8.6's language-map / datatype-map
// n-ary Cartesian product when present (language takes precedence per
// 12.2's ordering: "if the term map declares a language map... otherwise
// if it declares a datatype map... otherwise the natural RDF literal").
let build_literal_opt (lex : string) (dt : string) (lang : option string) : option rdf_term =
  if is_iri dt then
    let l : literal = { lexical_form = lex; datatype = dt; lang_tag = lang } in
    if literal_wf l then Some (T_Literal l) else None
  else None

// A datatype map "MUST generate a list of IRI values" (spec 8.6) — its
// expression is evaluated through the same IRI term-generation rules as
// any IRI-typed term map (absolute-IRI check + base-IRI prepend for
// reference-valued forms; IRI-safe percent-encoding + base-IRI prepend
// for template-valued forms, matching 8.3.1's default rml:IRI
// behaviour). RMLTC0022c's `rml:datatypeMap [ rml:template
// "datatype#{$.BAR}" ]` only produces the expected
// "http://example.com/datatype#string" once the relative template
// result is resolved against the base IRI this way.
let eval_iri_valued_strings (tm : term_map) (row : source_row) (base_iri : option string) : list string =
  let resolve (s : string) : list string =
    match iri_like_term s base_iri with Some (T_IRI i) -> [i] | _ -> [] in
  match tm.tmap_form with
  | TMF_Constant t -> (match t with T_IRI i -> [i] | _ -> [])
  | TMF_Reference r -> List.Tot.concatMap resolve (reference_cast_strings row r)
  | TMF_Template t -> List.Tot.concatMap resolve (eval_template_strings (Some string_encode_iri) t row)
  | TMF_Unknown -> []

// Minimal BCP47 well-formedness gate (RMLTC0015b: `rml:language
// "a-english"` — a single-letter primary language subtag, invalid per
// BCP47 section 2.1's langtag production: the primary subtag is
// 2*3ALPHA / 4ALPHA / 5*8ALPHA, with single-letter subtags reserved for
// the "i-"/"x-" grandfathered/private-use lead-ins only). Checks the
// FIRST subtag alone (up to the first '-'): 2-8 ASCII letters, or
// exactly "i"/"x" (case-insensitive). NOT a full BCP47 parser — no
// script/region/variant/extension subtag grammar, no IANA registry
// lookup — same "honest subset" scope as Parser.JSONLD.fst's
// jld_lang_tag_wf (which only screens forbidden bytes and would not
// catch this fixture, since "a-english" contains no forbidden byte).
let is_ascii_alpha (c : FStar.Char.char) : bool =
  let i = FStar.Char.int_of_char c in
  (i >= 0x41 && i <= 0x5A) || (i >= 0x61 && i <= 0x7A)

let rec all_ascii_alpha (cs : list FStar.Char.char) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest -> is_ascii_alpha c && all_ascii_alpha rest

let rec find_hyphen (s : string) (pos : nat) (fuel : nat)
  : Tot (option (i:nat{i < String.length s})) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = String.length s in
    if pos >= len then None
    else if FStar.Char.int_of_char (String.index s pos) = 0x2D (* '-' *) then Some pos
    else find_hyphen s (pos + 1) (fuel - 1)

let rml_lang_tag_wf (s : string) : bool =
  let len = String.length s in
  if len = 0 then false
  else
    let first = (match find_hyphen s 0 (len + 1) with
                 | Some i -> String.sub s 0 i
                 | None -> s) in
    let flen = String.length first in
    all_ascii_alpha (String.list_of_string first) &&
    ((flen = 1 && (first = "i" || first = "I" || first = "x" || first = "X")) ||
     (flen >= 2 && flen <= 8))

let literal_terms_for_base
    (tm : term_map) (row : source_row) (base_iri : option string) (natural_dt : wf_iri) (lex : string)
  : list rdf_term =
  match tm.tmap_language with
  | Some lang_tm ->
    List.Tot.concatMap
      (fun lang ->
         if rml_lang_tag_wf lang then
           (match build_literal_opt lex rdf_lang_string (Some lang) with Some t -> [t] | None -> [])
         else [])  // spec 12.2's Literal rule 1: invalid BCP47 language tag -> data error, no term
      (eval_plain_strings lang_tm row)
  | None ->
    (match tm.tmap_datatype with
     | Some dt_tm ->
       List.Tot.concatMap
         (fun dt -> match build_literal_opt lex dt None with Some t -> [t] | None -> [])
         (eval_iri_valued_strings dt_tm row base_iri)
     | None ->
       (match build_literal_opt lex natural_dt None with Some t -> [t] | None -> []))

// A resolved candidate value from a reference (keeps the (lexical,
// natural-datatype) pair reference_natural_values already computed —
// JSON's number/bool/string inference or CSV's always-xsd:string) or
// a template (always a plain string — templates concatenate to text,
// so their natural datatype is always xsd:string per 11.1).
noeq type resolved_value =
  | RV_Value  : string -> wf_iri -> resolved_value
  | RV_String : string -> resolved_value

let resolved_value_natural (rv : resolved_value) : option (string & wf_iri) =
  match rv with
  | RV_Value s dt -> Some (s, dt)
  | RV_String s -> Some (s, xsd_string)

// Finalize one resolved candidate into 0 or 1 RDF terms, per the
// effective term type. TT_Literal may fan out via the language/datatype
// Cartesian product (0 or more), everything else yields 0 or 1.
let finalize_value (tt : term_type) (tm : term_map) (row : source_row) (base_iri : option string) (rv : resolved_value)
  : list rdf_term =
  match resolved_value_natural rv with
  | None -> []
  | Some (s, dt) ->
    (match tt with
     | TT_IRI | TT_URI ->
       (match iri_like_term s base_iri with Some t -> [t] | None -> [])
     | TT_UnsafeIRI ->
       // Lenient gate — see iri_like_term_gated's UnsafeIRI rationale.
       (match iri_like_term_gated false s base_iri with Some t -> [t] | None -> [])
     | TT_BlankNode -> [T_BNode s]
     | TT_Literal -> literal_terms_for_base tm row base_iri dt s)

// Deterministic per-row seed for the one case a term map may have *no*
// expression at all: an explicit rml:termType rml:BlankNode with
// neither rml:constant/reference/template (spec 8.4.2: "a term map MAY
// not have an expression map [when BlankNode]... an RML Processor MUST
// generate a random value"). A truly random value isn't available in
// pure F*; the caller-supplied row_seed (unique per triples-map + row
// index, see RML.Eval.gen_row_triples) stands in for "random" — it is
// unique across rows and triples maps, which is the property the
// generated triples actually depend on (isomorphism-preserving
// comparison, not literal bnode-label equality).
let eval_term_map (role : map_role) (tm : term_map) (row : source_row) (row_seed : string) (base_iri : option string)
  : list rdf_term =
  match tm.tmap_form with
  | TMF_Constant t ->
    (match t with
     | T_IRI _ | T_Literal _ -> [t]
     | T_BNode _ -> [])  // constants may only be IRIs/literals (spec 8.4.2 note) — data error, no term
  | TMF_Unknown ->
    (match tm.tmap_termtype with
     | Some TT_BlankNode -> [T_BNode row_seed]
     | _ -> [])
  | TMF_Reference r ->
    let tt = effective_term_type role tm in
    let leaves = reference_natural_values row r in
    List.Tot.concatMap (fun (s, dt) -> finalize_value tt tm row base_iri (RV_Value s dt)) leaves
  | TMF_Template t ->
    let tt = effective_term_type role tm in
    let encode =
      (match tt with
       | TT_IRI -> Some string_encode_iri
       | TT_URI -> Some string_encode_uri
       | _ -> None) in
    let strs = eval_template_strings encode t row in
    List.Tot.concatMap (fun s -> finalize_value tt tm row base_iri (RV_String s)) strs

// ------------------------------------------------------------------
// 5. Triples-map evaluation (spec 12.1, non-join subset). Joins
//    (referencing object maps, Stage 5) are decoded (OB_Join) but
//    contribute no triples here.
// ------------------------------------------------------------------

// term_map is `noeq` (no decidable equality), so `list term_map = []`
// doesn't typecheck structurally — a plain pattern match on nil/cons
// works regardless of the element type's equality.
let list_nonempty (#a : Type) (l : list a) : bool =
  match l with
  | [] -> false
  | _ -> true

let subject_of_rdf_term (t : rdf_term) : option subject =
  match t with
  | T_IRI i -> Some (S_IRI i)
  | T_BNode b -> Some (S_BNode b)
  | T_Literal _ -> None

let term_to_graph_name (t : rdf_term) : option string =
  match t with
  | T_IRI i -> Some i
  | T_BNode b -> Some ("_:" ^ b)
  | T_Literal _ -> None

let eval_graphs (gms : list term_map) (row : source_row) (row_seed : string) (base_iri : option string) : list string =
  List.Tot.concatMap
    (fun g ->
       List.Tot.concatMap
         (fun t -> match term_to_graph_name t with Some n -> [n] | None -> [])
         (eval_term_map MR_Graph g row row_seed base_iri))
    gms

// A triple plus its target graphs. pt_graphs = [] means the default
// graph ONLY when neither a subject graph map nor a predicate-object
// graph map was declared (spec 12.1: "If sgm is empty -> rml:defaultGraph").
// pt_drop distinguishes the OTHER way to reach an empty target list: a
// graph map WAS declared but produced no valid term (e.g. RMLTC0007h's
// `rml:graphMap [ rml:reference "$.ID"; rml:termType rml:Literal ]` —
// a named graph identifier must be an IRI, so a Literal-typed graph map
// is a data error). That case must NOT fall back to the default graph
// — the triple is dropped entirely (spec 12.1's "Adding Triples to the
// Output Dataset" step 4 only ever ADDS to graphs that are actually in
// the target set; an empty set from a declared-but-invalid graph map
// contributes no membership at all, default or named).
noeq type placed_triple = {
  pt_triple : triple;
  pt_graphs : list string;
  pt_drop   : bool;
}

let eval_pom (row : source_row) (row_seed : string) (base_iri : option string) (pom : predicate_object_map)
  : (list rdf_term & list rdf_term & list string) =
  let predicates = List.Tot.concatMap (fun p -> eval_term_map MR_Predicate p row row_seed base_iri) pom.pom_predicates in
  let objects =
    List.Tot.concatMap
      (fun ob ->
         match ob with
         | OB_TermMap tm -> eval_term_map MR_Object tm row row_seed base_iri
         | OB_Join _ -> [])  // Stage 5
      pom.pom_objects in
  let graphs = eval_graphs pom.pom_graphs row row_seed base_iri in
  (predicates, objects, graphs)

let placed_triples_for_pom
    (subj : subject) (subject_graphs : list string) (has_sgm : bool)
    (row : source_row) (row_seed : string) (base_iri : option string) (pom : predicate_object_map)
  : list placed_triple =
  let (predicates, objects, pog) = eval_pom row row_seed base_iri pom in
  let has_pogm = list_nonempty pom.pom_graphs in
  let target = if (not has_sgm) && (not has_pogm) then [] else subject_graphs @ pog in
  let drop = (has_sgm || has_pogm) && target = [] in
  List.Tot.concatMap
    (fun p ->
       match p with
       | T_IRI pi ->
         List.Tot.concatMap
           (fun o -> [{ pt_triple = { s = subj; p = pi; o = o }; pt_graphs = target; pt_drop = drop }])
           objects
       | _ -> [])  // predicate maps must generate IRIs (spec 8.4) — non-IRI predicate is a data error
    predicates

let class_placed_triples (subj : subject) (subject_graphs : list string) (has_sgm : bool) (classes : list wf_iri)
  : list placed_triple =
  let target = if has_sgm then subject_graphs else [] in
  let drop = has_sgm && target = [] in
  List.Tot.map
    (fun cls -> { pt_triple = { s = subj; p = rdf_type; o = T_IRI cls }; pt_graphs = target; pt_drop = drop })
    classes

// One logical iteration's contribution: the (possibly fanned-out)
// subject(s), each crossed with the rdf:type/class triples and every
// predicate-object map's predicate x object cross product.
let gen_row_triples
    (tmap : triples_map) (sm : subject_map_t) (row : source_row) (row_seed : string) (base_iri : option string)
  : list placed_triple =
  let subj_terms = eval_term_map MR_Subject sm.sm_term row row_seed base_iri in
  let has_sgm = list_nonempty sm.sm_graphs in
  let subject_graphs = eval_graphs sm.sm_graphs row row_seed base_iri in
  List.Tot.concatMap
    (fun subj_term ->
       match subject_of_rdf_term subj_term with
       | None -> []
       | Some subj ->
         let class_triples = class_placed_triples subj subject_graphs has_sgm sm.sm_classes in
         let pom_triples =
           List.Tot.concatMap
             (placed_triples_for_pom subj subject_graphs has_sgm row row_seed base_iri)
             tmap.tm_predicate_object_maps in
         class_triples @ pom_triples)
    subj_terms

// Evaluate one triples map against its already-iterated row list (the
// OCaml-side caller — rule #11 — reads + parses the logical source's
// file and calls RML.Sources' json_iterate/csv_iterate to produce
// `rows`; iteration itself is pure path/tokenizer evaluation, already
// done by the time this function runs, so it is format-agnostic here
// — adding XML (Stage 4) needs no change to this function, only a new
// `xml_iterate` on the caller side).
//
// `default_base_iri` is the RML-Core spec's "execution environment"
// base IRI (4.1.1: "The base IRI MUST be defined within the mapping
// document for each Triples Map OR as execution environment for the
// mapping document") — used only when the triples map has no own
// rml:baseIRI. The vendored rml-core suite supplies this per test via
// metadata.csv's `base_iri` column (RMLTC0019a/0026b need it: no
// in-document rml:baseIRI, yet a relative-IRI subject still resolves).
// The OCaml-side test driver is the one place that reads that column;
// this function just takes the resolved value as a parameter.
let eval_triples_map (tmap : triples_map) (rows : list source_row) (default_base_iri : option string)
  : list placed_triple =
  let base_iri = (match tmap.tm_base_iri with Some b -> Some b | None -> default_base_iri) in
  match tmap.tm_subject_map with
  | Some sm ->
    List.Tot.concatMap
      (fun (idx, row) ->
         let row_seed = tmap.tm_id ^ "#r" ^ string_of_int idx in
         gen_row_triples tmap sm row row_seed base_iri)
      (List.Tot.mapi (fun i r -> (i, r)) rows)
  | None -> []  // no subjectMap: data error -> no triples (matches error=true fixtures)

// Convenience wrapper: iterate a JSON logical source's already-parsed
// root and evaluate in one call. Only fires when the triples map's own
// reference formulation is actually RF_JSONPath — any other
// formulation (or no logical source at all) yields no triples, same
// as the `eval_triples_map` None branch above.
let eval_triples_map_json (tmap : triples_map) (json_root : json_val) (default_base_iri : option string)
  : list placed_triple =
  match tmap.tm_logical_source with
  | Some ls ->
    (match ls.ls_reference_formulation with
     | Some RF_JSONPath ->
       let iterator = (match ls.ls_iterator with Some it -> it | None -> "$") in
       eval_triples_map tmap (json_iterate json_root iterator) default_base_iri
     | _ -> [])
  | None -> []

// Convenience wrapper, Stage 3's CSV counterpart: iterate a CSV logical
// source's raw file text (header row -> per-row column bindings, with
// rml:null filtering applied by RML.Sources' csv_iterate) and evaluate
// in one call.
let eval_triples_map_csv (tmap : triples_map) (csv_text : string) (default_base_iri : option string)
  : list placed_triple =
  match tmap.tm_logical_source with
  | Some ls ->
    (match ls.ls_reference_formulation with
     | Some RF_CSV -> eval_triples_map tmap (csv_iterate csv_text ls.ls_null_values) default_base_iri
     | _ -> [])
  | None -> []

// ------------------------------------------------------------------
// 5b. Joins (RefObjectMap evaluation, Stage 5 of the plan). Semantics
//     taken verbatim from the RML-Core spec's joinconditions.md and
//     output.md sections (fetched directly, 2026-07-05):
//
//     - A join condition is satisfied when evaluating the child map
//       against the child iteration and the parent map against the
//       parent iteration gives an equal result (joinconditions.md
//       "Join Condition"). Child/parent maps are plain expression maps
//       (constant/reference/template only, no termType/datatype/
//       language) — eval_plain_strings is exactly this evaluation
//       (already used for the same purpose by the datatype/language
//       Cartesian product above).
//     - "Equal" is implemented as non-empty intersection between the
//       two (possibly multi-valued, per wildcard references) result
//       lists — verified against RMLTC0030c/d/e/f, whose constant-
//       valued child/parent maps match EVERY row on the other side
//       whenever the constant equals that row's value, not just one.
//     - If a RefObjectMap has NO join conditions at all, the spec
//       requires the two logical sources to be "effectively equal"
//       (same source/iterator/referenceFormulation) — meaning the
//       parent and child iteration lists are the identical, ordered
//       sequence. Pairing is therefore index-aligned (row i of child
//       with row i of parent), not a cross product — verified against
//       RMLTC0008b (a single-row fixture, ambiguous alone, but the
//       "effectively equal" text in joinconditions.md only makes sense
//       under a deterministic same-iteration reading).
//     - WITH join conditions, pairing is a full nested-loop join: every
//       (child_iteration, parent_iteration) pair whose conditions all
//       hold contributes a triple — verified against RMLTC0021a's
//       self-join (3 students, 2 sharing a sport) producing 5 output
//       triples, exactly the nested-loop-join result, not a 1:1 zip.
//     - The generated triple's subject/predicates/graphs come from the
//       CHILD iteration (same as the non-join case); the object is the
//       PARENT triples map's subject map applied to the matching
//       PARENT iteration (output.md's dedicated join algorithm, a
//       second loop distinct from the main predicate/object cross
//       product — which is why OB_Join contributes nothing in
//       eval_pom/placed_triples_for_pom above; this section is its own
//       pass over the same predicate-object maps).
// ------------------------------------------------------------------

// child/parent maps are bare expression maps (constant/reference/
// template) evaluated with eval_plain_strings — no term-type/datatype/
// language machinery applies to a join condition's own values.
let join_condition_holds (jc : join_condition) (child_row : source_row) (parent_row : source_row) : bool =
  let child_vals = eval_plain_strings jc.jc_child child_row in
  let parent_vals = eval_plain_strings jc.jc_parent parent_row in
  List.Tot.existsb (fun v -> List.Tot.mem v parent_vals) child_vals

let join_conditions_hold (jcs : list join_condition) (child_row : source_row) (parent_row : source_row) : bool =
  List.Tot.for_all (fun jc -> join_condition_holds jc child_row parent_row) jcs

// Parent iterations (indexed, for row_seed stability) matching one
// child iteration. Joinless (jcs = []) pairs by identical index
// ("effectively equal" logical sources — see the section comment
// above); with join conditions, filters the WHOLE parent row list by
// join_conditions_hold (a full nested-loop join, not a 1:1 zip).
let matching_parent_rows
    (jcs : list join_condition) (cidx : int) (crow : source_row) (parent_rows_idx : list (int & source_row))
  : list (int & source_row) =
  match jcs with
  | [] -> List.Tot.filter (fun (pidx, _) -> pidx = cidx) parent_rows_idx
  | _ -> List.Tot.filter (fun (_, prow) -> join_conditions_hold jcs crow prow) parent_rows_idx

// One triples map's join-generated placed triples, given an
// already-resolved lookup from a parent-triples-map node_ref to that
// triples map's own record and its already-iterated row list (the
// OCaml-side caller — rule #11 — resolves every triples map's rows up
// front, the same read+iterate it already does for the current
// triples map; the lookup itself is pure in-memory data, not I/O).
let eval_join_pom
    (subj : subject) (subject_graphs : list string) (has_sgm : bool)
    (crow : source_row) (cidx : int) (row_seed : string) (base_iri : option string)
    (lookup_parent : node_ref -> option (triples_map & list source_row))
    (pom : predicate_object_map)
  : list placed_triple =
  let predicates = List.Tot.concatMap (fun p -> eval_term_map MR_Predicate p crow row_seed base_iri) pom.pom_predicates in
  let pog = eval_graphs pom.pom_graphs crow row_seed base_iri in
  let has_pogm = list_nonempty pom.pom_graphs in
  let target = if (not has_sgm) && (not has_pogm) then [] else subject_graphs @ pog in
  let drop = (has_sgm || has_pogm) && target = [] in
  List.Tot.concatMap
    (fun ob ->
       match ob with
       | OB_TermMap _ -> []  // handled by the non-join pass (eval_pom above)
       | OB_Join rom ->
         (match lookup_parent rom.rom_parent_triples_map with
          | None -> []
          | Some (ptmap, prows) ->
            (match ptmap.tm_subject_map with
             | None -> []
             | Some psm ->
               let parent_base = ptmap.tm_base_iri in
               let parent_rows_idx = List.Tot.mapi (fun i r -> (i, r)) prows in
               let matches = matching_parent_rows rom.rom_joins cidx crow parent_rows_idx in
               List.Tot.concatMap
                 (fun (pidx, prow) ->
                    let prow_seed = ptmap.tm_id ^ "#r" ^ string_of_int pidx in
                    let obj_terms = eval_term_map MR_Subject psm.sm_term prow prow_seed parent_base in
                    List.Tot.concatMap
                      (fun obj_term ->
                         List.Tot.concatMap
                           (fun p ->
                              match p with
                              | T_IRI pi -> [{ pt_triple = { s = subj; p = pi; o = obj_term };
                                               pt_graphs = target; pt_drop = drop }]
                              | _ -> [])
                           predicates)
                      obj_terms)
                 matches)))
    pom.pom_objects

// Entry point: join-generated placed triples for a whole triples map,
// looping over its own (child) iterations. Format-agnostic, same shape
// as eval_triples_map — the OCaml driver resolves `rows` (this
// triples map's own iteration list, already computed for the non-join
// pass) and `lookup_parent` once per test, not once per join.
let eval_join_triples_map
    (tmap : triples_map) (rows : list source_row) (default_base_iri : option string)
    (lookup_parent : node_ref -> option (triples_map & list source_row))
  : list placed_triple =
  let base_iri = (match tmap.tm_base_iri with Some b -> Some b | None -> default_base_iri) in
  match tmap.tm_subject_map with
  | None -> []
  | Some sm ->
    let has_sgm = list_nonempty sm.sm_graphs in
    List.Tot.concatMap
      (fun (cidx, crow) ->
         let row_seed = tmap.tm_id ^ "#r" ^ string_of_int cidx in
         let subj_terms = eval_term_map MR_Subject sm.sm_term crow row_seed base_iri in
         let subject_graphs = eval_graphs sm.sm_graphs crow row_seed base_iri in
         List.Tot.concatMap
           (fun subj_term ->
              match subject_of_rdf_term subj_term with
              | None -> []
              | Some subj ->
                List.Tot.concatMap
                  (eval_join_pom subj subject_graphs has_sgm crow cidx row_seed base_iri lookup_parent)
                  tmap.tm_predicate_object_maps)
           subj_terms)
      (List.Tot.mapi (fun i r -> (i, r)) rows)

// ------------------------------------------------------------------
// 6. Placing triples into an rdf_dataset (default graph vs named
//    graphs — spec section 10 / 12.1's "Target graphs" column).
// ------------------------------------------------------------------

let add_to_named_graph (ds : rdf_dataset) (name : string) (t : triple) : rdf_dataset =
  match List.Tot.tryFind (fun (ng : named_graph) -> ng.ng_name = name) ds.ds_named with
  | Some _ ->
    { ds with
      ds_named =
        List.Tot.map
          (fun (ng : named_graph) -> if ng.ng_name = name then { ng with ng_graph = t :: ng.ng_graph } else ng)
          ds.ds_named }
  | None -> { ds with ds_named = ({ ng_name = name; ng_graph = [t] }) :: ds.ds_named }

// rml:defaultGraph (spec section 10) is the sentinel for "route to the
// default graph", not the name of a real named graph — RMLTC0007g,
// RMLTC0028b use `rml:graph rml:defaultGraph` explicitly.
let add_to_graph (ds : rdf_dataset) (name : string) (t : triple) : rdf_dataset =
  if name = rml_defaultGraph then { ds with ds_default = t :: ds.ds_default }
  else add_to_named_graph ds name t

let rec place_into_dataset (ds : rdf_dataset) (pts : list placed_triple) : Tot rdf_dataset (decreases pts) =
  match pts with
  | [] -> ds
  | pt :: rest ->
    let ds1 =
      if pt.pt_drop then ds
      else if pt.pt_graphs = [] then { ds with ds_default = pt.pt_triple :: ds.ds_default }
      else List.Tot.fold_left (fun d g -> add_to_graph d g pt.pt_triple) ds pt.pt_graphs in
    place_into_dataset ds1 rest

// Convenience entry point: join-generated triples straight into an
// existing dataset (composes with eval_triples_map_dataset's non-join
// output — the OCaml driver calls both per triples map and merges).
let eval_join_triples_map_dataset
    (tmap : triples_map) (rows : list source_row) (default_base_iri : option string)
    (lookup_parent : node_ref -> option (triples_map & list source_row)) (ds : rdf_dataset)
  : rdf_dataset =
  place_into_dataset ds (eval_join_triples_map tmap rows default_base_iri lookup_parent)

// Convenience entry point: evaluate one triples map straight to a
// dataset, given its already-iterated row list. See eval_triples_map
// for what default_base_iri means.
let eval_triples_map_dataset
    (tmap : triples_map) (rows : list source_row) (default_base_iri : option string)
  : rdf_dataset =
  place_into_dataset empty_dataset (eval_triples_map tmap rows default_base_iri)

// Convenience entry point: evaluate one triples map against its parsed
// JSON root, straight to a dataset.
let eval_triples_map_json_dataset
    (tmap : triples_map) (json_root : json_val) (default_base_iri : option string)
  : rdf_dataset =
  place_into_dataset empty_dataset (eval_triples_map_json tmap json_root default_base_iri)

// Convenience entry point, Stage 3's CSV counterpart: evaluate one
// triples map against its raw CSV source text, straight to a dataset.
let eval_triples_map_csv_dataset
    (tmap : triples_map) (csv_text : string) (default_base_iri : option string)
  : rdf_dataset =
  place_into_dataset empty_dataset (eval_triples_map_csv tmap csv_text default_base_iri)
