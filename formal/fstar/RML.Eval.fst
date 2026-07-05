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
    let leaves = json_reference_values row r in
    let vals =
      List.Tot.concatMap
        (fun v -> match json_natural_cast_string v with Some s -> [s] | None -> [])
        leaves in
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

// spec 12.2: "If the term type is rml:IRI/rml:UnsafeIRI/rml:URI/
// rml:UnsafeURI: let value be the natural RDF lexical form...; if value
// is a valid absolute IRI/URI, return an IRI/URI generated from value;
// otherwise prepend the base IRI and re-check; otherwise raise a data
// error [-> no term generated, here]." `is_iri` is this codebase's
// existing coarse absolute-IRI approximation (non-empty + contains a
// colon), used uniformly for both the IRI and URI branches since a
// stricter RFC3986-vs-3987 absolute-reference distinction isn't
// implemented elsewhere in the codebase either.
let iri_like_term (value : string) (base_iri : option string) : option rdf_term =
  if is_iri value then Some (T_IRI value)
  else
    match base_iri with
    | Some b -> let combined = b ^ value in if is_iri combined then Some (T_IRI combined) else None
    | None -> None

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
  | TMF_Reference r ->
    List.Tot.concatMap
      (fun v -> match json_natural_cast_string v with Some s -> [s] | None -> [])
      (json_reference_values row r)
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
  | TMF_Reference r ->
    List.Tot.concatMap
      (fun v -> match json_natural_cast_string v with Some s -> resolve s | None -> [])
      (json_reference_values row r)
  | TMF_Template t -> List.Tot.concatMap resolve (eval_template_strings (Some string_encode_iri) t row)
  | TMF_Unknown -> []

let literal_terms_for_base
    (tm : term_map) (row : source_row) (base_iri : option string) (natural_dt : wf_iri) (lex : string)
  : list rdf_term =
  match tm.tmap_language with
  | Some lang_tm ->
    List.Tot.concatMap
      (fun lang -> match build_literal_opt lex rdf_lang_string (Some lang) with Some t -> [t] | None -> [])
      (eval_plain_strings lang_tm row)
  | None ->
    (match tm.tmap_datatype with
     | Some dt_tm ->
       List.Tot.concatMap
         (fun dt -> match build_literal_opt lex dt None with Some t -> [t] | None -> [])
         (eval_iri_valued_strings dt_tm row base_iri)
     | None ->
       (match build_literal_opt lex natural_dt None with Some t -> [t] | None -> []))

// A resolved candidate value from a reference (keeps the original JSON
// scalar, for natural-datatype inference) or a template (always a
// plain string — templates concatenate to text, so their natural
// datatype is always xsd:string per 11.1).
noeq type resolved_value =
  | RV_Json   : json_val -> resolved_value
  | RV_String : string -> resolved_value

let resolved_value_natural (rv : resolved_value) : option (string & wf_iri) =
  match rv with
  | RV_Json v -> json_natural_value v
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
     | TT_IRI | TT_UnsafeIRI | TT_URI ->
       (match iri_like_term s base_iri with Some t -> [t] | None -> [])
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
    let leaves = json_reference_values row r in
    List.Tot.concatMap (fun v -> finalize_value tt tm row base_iri (RV_Json v)) leaves
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

// A triple plus its target graphs ([] means the default graph — spec
// 12.1.1: "If Subject, Predicate, or Object is empty, abort" is handled
// upstream by never constructing a placed_triple for an empty
// component).
noeq type placed_triple = {
  pt_triple : triple;
  pt_graphs : list string;
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
  List.Tot.concatMap
    (fun p ->
       match p with
       | T_IRI pi ->
         List.Tot.concatMap
           (fun o -> [{ pt_triple = { s = subj; p = pi; o = o }; pt_graphs = target }])
           objects
       | _ -> [])  // predicate maps must generate IRIs (spec 8.4) — non-IRI predicate is a data error
    predicates

let class_placed_triples (subj : subject) (subject_graphs : list string) (has_sgm : bool) (classes : list wf_iri)
  : list placed_triple =
  List.Tot.map
    (fun cls -> { pt_triple = { s = subj; p = rdf_type; o = T_IRI cls };
                  pt_graphs = (if has_sgm then subject_graphs else []) })
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

// Evaluate one triples map against its (already read + parsed, by the
// OCaml-side caller — rule #11) JSON logical-source root. Only the
// RF_JSONPath reference formulation is handled this stage (Stage 3/4
// add CSV/XML).
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
let eval_triples_map_json (tmap : triples_map) (json_root : json_val) (default_base_iri : option string)
  : list placed_triple =
  let base_iri = (match tmap.tm_base_iri with Some b -> Some b | None -> default_base_iri) in
  match tmap.tm_subject_map, tmap.tm_logical_source with
  | Some sm, Some ls ->
    (match ls.ls_reference_formulation with
     | Some RF_JSONPath ->
       let iterator = (match ls.ls_iterator with Some it -> it | None -> "$") in
       let rows = json_iterate json_root iterator in
       List.Tot.concatMap
         (fun (idx, row) ->
            let row_seed = tmap.tm_id ^ "#r" ^ string_of_int idx in
            gen_row_triples tmap sm row row_seed base_iri)
         (List.Tot.mapi (fun i r -> (i, r)) rows)
     | _ -> [])
  | _, _ -> []  // no subjectMap, or no logicalSource: data error -> no triples (matches error=true fixtures)

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
      if pt.pt_graphs = [] then { ds with ds_default = pt.pt_triple :: ds.ds_default }
      else List.Tot.fold_left (fun d g -> add_to_graph d g pt.pt_triple) ds pt.pt_graphs in
    place_into_dataset ds1 rest

// Convenience entry point: evaluate one triples map against its parsed
// JSON root, straight to a dataset. See eval_triples_map_json for what
// default_base_iri means.
let eval_triples_map_json_dataset
    (tmap : triples_map) (json_root : json_val) (default_base_iri : option string)
  : rdf_dataset =
  place_into_dataset empty_dataset (eval_triples_map_json tmap json_root default_base_iri)
