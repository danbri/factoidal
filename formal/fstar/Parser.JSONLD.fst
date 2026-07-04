module Parser.JSONLD

// ============================================================================
// JSON-LD deserialization to RDF.
//
// *****************************************************************
// *  THIS MODULE'S jld_* PIPELINE CONSUMES EXPANDED FORM ONLY.    *
// *  An array of node objects whose keys are absolute IRIs or     *
// *  keywords, and whose property values are arrays of node       *
// *  objects / node references / value objects / list objects.    *
// *  It does not itself interpret @context, resolve compact IRIs, *
// *  or resolve terms.                                            *
// *                                                                *
// *  PHASE 3a (JSONLD.Context / JSONLD.Expand, see                *
// *  docs/designissues/2026-07-04-jsonld-program-lessons.md) adds  *
// *  an expansion step in front: parse_jsonld below now runs       *
// *  JSONLD.Expand.expand over any document carrying an inline     *
// *  @context before handing the result to jld_dataset_of_json —   *
// *  it produces exactly the expanded-form json_val this module    *
// *  already expects. A document with no @context member still     *
// *  goes straight to jld_dataset_of_json (Phase 1 path,           *
// *  unchanged) so the existing context-free fixtures keep working *
// *  exactly as before.                                            *
// *****************************************************************
//
// This is the "Deserialize JSON-LD to RDF" step of the JSON-LD 1.1
// Processing Algorithms and API spec (§8), simplified to expanded-form
// input. Supported here:
//   - node objects with absolute-IRI @id, blank-node @id (leading "_:"),
//     or no @id (fresh blank node from a counter-threaded pure allocator);
//   - @type on node objects (rdf:type triples; IRI or blank-node values);
//   - value objects: @value + @language -> language-tagged literal;
//     @value + @type -> typed literal; bare string @value -> xsd:string;
//     boolean @value -> xsd:boolean; number @value -> xsd:integer when
//     the lexeme has no fraction/exponent, xsd:double otherwise;
//   - @list -> rdf:first / rdf:rest / rdf:nil chains (empty list -> nil);
//   - top-level node objects carrying @graph -> named graphs (graph name
//     from @id: IRI, blank-node label — stored with the literal "_:"
//     prefix inside ng_name per the Parser.NQuads convention — or a
//     fresh blank node when @id is absent); a top-level object whose ONLY
//     key is @graph is the document wrapper and feeds the default graph;
//   - nested node objects in property position (their triples are
//     emitted and the node is referenced);
//   - bare JSON scalars in value position (string / boolean / number),
//     interpreted as the Expansion algorithm would wrap them — this
//     leniency keeps the context-free W3C toRdf inputs loadable.
//
// PHASE 3b adds @reverse consumption: a node object's ("@reverse", {predIri:
// [items...]}) field (produced by JSONLD.Expand for a term defined with
// "@reverse", or an inline "@reverse" block — see that module's banner)
// expands each item as an ordinary node reference / node object (exactly
// like jld_expand_value's node-object branch) and emits a triple with the
// item as SUBJECT, predIri as predicate, and the enclosing node as OBJECT
// — jld_expand_reverse_map / _entries / _prop below. A node object may
// carry more than one "@reverse" field-list entry (one inline block plus
// one or more reverse terms); jld_expand_fields already processes every
// field-list entry regardless of key repetition, so no merge step is
// needed on this side either.
//
// Phase-2+ items deliberately NOT handled here (dropped silently, per the
// spec's treatment of non-conforming data where possible):
//   - @context (see banner above);
//   - relative IRIs (dropped — is_iri requires a colon);
//   - @index, @included, @direction, @json (rdf:JSON literals),
//     @graph nested below the top level, generalized RDF (blank-node
//     predicates);
//   - canonical lexical forms for xsd:double per the JSON-LD Data
//     Round-Tripping algorithm (e.g. 2.5 SHOULD serialize as "2.5E0";
//     this phase keeps the validated JSON lexeme verbatim);
//   - duplicate-triple suppression (house parsers keep duplicates:
//     graph_add_unchecked + finalise, no dedup — same policy here).
//
// PERF SHAPE (per the program lessons doc): triples are PREPENDED onto
// accumulator lists (O(1) each, no membership scans) and every graph is
// reversed exactly once at the end via dataset_finalise. Blank-node
// allocation threads a nat counter through the recursion (same pattern
// as Parser.Turtle.fresh_bnode).
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.FastString
open RDF.Graph.Executable
open Parser.JSON
open JSONLD.Context
open JSONLD.Expand

// ================================================================
// RDF vocabulary constants
// ================================================================

let rdf_type_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let rdf_first_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

// ================================================================
// Small helpers
// ================================================================

// Fresh blank node from a threaded counter (cf. Parser.Turtle.fresh_bnode).
// The "_jld_anon" prefix keeps generated labels visually distinct from
// document-supplied "_:..." labels; a malicious document could still
// collide with it, which Phase 2 can guard by namespacing document labels.
let jld_fresh_bnode (ctr:nat) : (bnode_id & nat) =
  (String.concat "" ["_jld_anon"; string_of_int ctr], ctr + 1)

// True when s begins with the two bytes "_:" (blank-node identifier).
let jld_is_bnode_label (s:string) : bool =
  jbyte_at s 0 = 0x5F && jbyte_at s 1 = 0x3A

// Strip the leading "_:" (bnode_id fields store the label without it;
// serializers re-add it).
let jld_strip_bnode_prefix (s:string) : string =
  let n = fs_byte_length s in
  if n >= 2 then fs_byte_sub s 2 (n - 2) else s

// Expanded-form @id string -> subject. Relative IRIs yield None (dropped).
let jld_id_to_subject (s:string) : option subject =
  if jld_is_bnode_label s then Some (S_BNode (jld_strip_bnode_prefix s))
  else if is_iri s then Some (S_IRI s)
  else None

// Keywords all start with a commercial-at byte.
let jld_is_keyword (k:string) : bool =
  jbyte_at k 0 = 0x40

// Expanded form wraps property values in arrays; be lenient about a bare
// object where an array is required.
let jld_as_array (v:json_val) : list json_val =
  match v with
  | JArray items -> items
  | _ -> [v]

// Does a validated JSON number lexeme denote a double (fraction or
// exponent present)? Bytes: 0x2E dot, 0x65 e, 0x45 E.
let rec jld_scan_double_marker (s:string) (pos:nat) (fuel:nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let b = jbyte_at s pos in
    if b < 0 then false
    else if b = 0x2E || b = 0x65 || b = 0x45 then true
    else jld_scan_double_marker s (pos + 1) (fuel - 1)

let jld_number_is_double (s:string) : bool =
  jld_scan_double_marker s 0 (fs_byte_length s + 1)

// Construct a T_Literal only if well-formed. Same shape as
// Parser.JSONResults.mk_literal; duplicated (it is four lines) rather
// than importing that module, whose lenient embedded JSON parser this
// module exists to bypass. Unify when Parser.JSONResults migrates onto
// Parser.JSON.
let jld_make_literal (lexical:string) (dt:string) (lang:option string)
  : option rdf_term =
  if is_iri dt then
    let lit : literal = { lexical_form = lexical; datatype = dt; lang_tag = lang } in
    if literal_wf lit then Some (T_Literal lit) else None
  else None

// A bare JSON scalar in value position, as the Expansion algorithm would
// wrap it: string -> xsd:string, boolean -> xsd:boolean, number ->
// xsd:integer (no fraction/exponent) or xsd:double. Accepting bare
// scalars keeps the context-free W3C toRdf inputs (e.g. toRdf/0001)
// loadable even though strict expanded form array-wraps every value.
let jld_scalar_to_term (v:json_val) : option rdf_term =
  match v with
  | JString str -> jld_make_literal str xsd_string None
  | JBool b -> jld_make_literal (if b then "true" else "false") xsd_boolean None
  | JNumber n ->
    if jld_number_is_double n
    then jld_make_literal n xsd_double None
    else jld_make_literal n xsd_integer None
  | _ -> None

// ================================================================
// Value objects (@value)
// ================================================================

// JSON-LD 1.1 API §8.6 "Object to RDF Conversion", value-object half,
// restricted to expanded form. Returns None for non-conforming value
// objects (both @language and @type; @language on a non-string @value;
// null / structured @value; invalid @type IRI).
let jld_value_object_to_term (obj:json_val) : option rdf_term =
  match json_get_field "@value" obj with
  | None -> None
  | Some v ->
    let lang = json_get_string "@language" obj in
    let dt = json_get_string "@type" obj in
    (match lang, dt with
     | Some _, Some _ -> None
     | Some lg, None ->
       (match v with
        | JString s -> jld_make_literal s rdf_lang_string (Some lg)
        | _ -> None)
     | None, Some d ->
       (match v with
        | JString s -> jld_make_literal s d None
        | JBool b -> jld_make_literal (if b then "true" else "false") d None
        | JNumber n -> jld_make_literal n d None
        | _ -> None)
     | None, None -> jld_scalar_to_term v)

// ================================================================
// @type entries on node objects
// ================================================================

let jld_type_term (t:string) : option rdf_term =
  if jld_is_bnode_label t then Some (T_BNode (jld_strip_bnode_prefix t))
  else if is_iri t then Some (T_IRI t)
  else None

let rec jld_type_prepend_items (subj:subject) (items:list json_val) (acc:list triple)
  : Tot (list triple) (decreases items) =
  match items with
  | [] -> acc
  | JString t :: rest ->
    (match jld_type_term t with
     | Some tm ->
       jld_type_prepend_items subj rest ({ s = subj; p = rdf_type_iri; o = tm } :: acc)
     | None -> jld_type_prepend_items subj rest acc)
  | _ :: rest -> jld_type_prepend_items subj rest acc

let jld_type_prepend (subj:subject) (v:json_val) (acc:list triple) : list triple =
  jld_type_prepend_items subj (jld_as_array v) acc

// ================================================================
// Expansion of node objects / property values / lists
//
// All functions thread (accumulator, counter) and PREPEND triples onto
// the accumulator; the caller reverses once at the end. Fuel bounds the
// recursion; parse_jsonld derives it from json_size, which dominates
// every call-chain length here (one fuel unit per value, array element,
// or object member visited).
// ================================================================

// A property value in expanded form: value object, list object, node
// object, or node reference. Returns the term to link to (None when the
// entry is non-conforming and must be dropped) plus updated acc/counter.
let rec jld_expand_value (v:json_val) (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (option rdf_term & list triple & nat) (decreases fuel) =
  if fuel = 0 then (None, acc, ctr)
  else
    match v with
    | JObject _ ->
      (match json_get_field "@value" v with
       | Some _ -> (jld_value_object_to_term v, acc, ctr)
       | None ->
         (match json_get_field "@list" v with
          | Some lst ->
            let (t, acc1, ctr1) = jld_expand_list (jld_as_array lst) ctr acc (fuel - 1) in
            (Some t, acc1, ctr1)
          | None ->
            let (osubj, acc1, ctr1) = jld_expand_node v ctr acc (fuel - 1) in
            (match osubj with
             | Some subj -> (Some (subject_to_term subj), acc1, ctr1)
             | None -> (None, acc1, ctr1))))
    | _ -> (jld_scalar_to_term v, acc, ctr)

// JSON-LD 1.1 API §8.7 "List Conversion": rdf:first/rdf:rest cells,
// rdf:nil terminator. Non-conforming entries are skipped.
and jld_expand_list (items:list json_val) (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (rdf_term & list triple & nat) (decreases fuel) =
  if fuel = 0 then (T_IRI rdf_nil_iri, acc, ctr)
  else
    match items with
    | [] -> (T_IRI rdf_nil_iri, acc, ctr)
    | item :: rest ->
      let (oterm, acc1, ctr1) = jld_expand_value item ctr acc (fuel - 1) in
      (match oterm with
       | None -> jld_expand_list rest ctr1 acc1 (fuel - 1)
       | Some t ->
         let (cell, ctr2) = jld_fresh_bnode ctr1 in
         let (rest_term, acc2, ctr3) = jld_expand_list rest ctr2 acc1 (fuel - 1) in
         let cell_subj = S_BNode cell in
         (T_BNode cell,
          { s = cell_subj; p = rdf_rest_iri;  o = rest_term } ::
          { s = cell_subj; p = rdf_first_iri; o = t } :: acc2,
          ctr3))

// A node object: subject from @id (fresh bnode when absent), then every
// member. Returns None subject (and prepends nothing) on a malformed @id.
and jld_expand_node (v:json_val) (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (option subject & list triple & nat) (decreases fuel) =
  if fuel = 0 then (None, acc, ctr)
  else
    match v with
    | JObject fields ->
      let (subj_opt, ctr1) =
        (match json_get_field "@id" v with
         | Some (JString id_str) -> (jld_id_to_subject id_str, ctr)
         | Some _ -> (None, ctr)
         | None ->
           let (b, ctr') = jld_fresh_bnode ctr in
           (Some (S_BNode b), ctr')) in
      (match subj_opt with
       | None -> (None, acc, ctr1)
       | Some subj ->
         let (acc1, ctr2) = jld_expand_fields subj fields ctr1 acc (fuel - 1) in
         (Some subj, acc1, ctr2))
    | _ -> (None, acc, ctr)

// Members of a node object. @type emits rdf:type triples; @reverse emits
// swapped-direction triples (jld_expand_reverse_map, PHASE 3b); other
// keywords are skipped (@id was consumed by jld_expand_node; @graph below
// the top level is a Phase-2 item); IRI keys emit property triples;
// non-IRI (relative) keys are dropped.
and jld_expand_fields (subj:subject) (fields:list (string & json_val))
                      (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (list triple & nat) (decreases fuel) =
  if fuel = 0 then (acc, ctr)
  else
    match fields with
    | [] -> (acc, ctr)
    | (key, value) :: rest ->
      let (acc1, ctr1) =
        if key = "@type" then (jld_type_prepend subj value acc, ctr)
        else if key = "@reverse" then jld_expand_reverse_map subj value ctr acc (fuel - 1)
        else if jld_is_keyword key then (acc, ctr)
        else if is_iri key then
          jld_expand_property subj key (jld_as_array value) ctr acc (fuel - 1)
        else (acc, ctr) in
      jld_expand_fields subj rest ctr1 acc1 (fuel - 1)

// A node object's "@reverse" member: {predIri: [items...], ...} (an
// EXPANDED-form-only shape produced by JSONLD.Expand — see that module's
// banner). Each predIri key must already be an absolute IRI (Expand only
// ever produces one via expand_iri); a malformed key is dropped.
and jld_expand_reverse_map (subj:subject) (v:json_val) (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (list triple & nat) (decreases fuel) =
  if fuel = 0 then (acc, ctr)
  else
    match v with
    | JObject entries -> jld_expand_reverse_entries subj entries ctr acc (fuel - 1)
    | _ -> (acc, ctr)

and jld_expand_reverse_entries (subj:subject) (entries:list (string & json_val))
                               (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (list triple & nat) (decreases fuel) =
  if fuel = 0 then (acc, ctr)
  else
    match entries with
    | [] -> (acc, ctr)
    | (prop, value) :: rest ->
      let (acc1, ctr1) =
        if is_iri prop
        then jld_expand_reverse_prop subj prop (jld_as_array value) ctr acc (fuel - 1)
        else (acc, ctr) in
      jld_expand_reverse_entries subj rest ctr1 acc1 (fuel - 1)

// One reverse predicate's array of item values: each item expands as a
// node reference / node object exactly like an ordinary property value
// (jld_expand_node — a bare literal value object has no subject identity
// and is silently dropped, same non-conforming-input leniency as
// elsewhere); the emitted triple points FROM the item TO the enclosing
// node (the direction swap that makes it a "reverse" property).
and jld_expand_reverse_prop (subj:subject) (prop:wf_iri) (vals:list json_val)
                            (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (list triple & nat) (decreases fuel) =
  if fuel = 0 then (acc, ctr)
  else
    match vals with
    | [] -> (acc, ctr)
    | v :: rest ->
      let (osubj, acc1, ctr1) = jld_expand_node v ctr acc (fuel - 1) in
      let acc2 =
        (match osubj with
         | Some vsubj -> { s = vsubj; p = prop; o = subject_to_term subj } :: acc1
         | None -> acc1) in
      jld_expand_reverse_prop subj prop rest ctr1 acc2 (fuel - 1)

// The array of values of one property.
and jld_expand_property (subj:subject) (prop:wf_iri) (vals:list json_val)
                        (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (list triple & nat) (decreases fuel) =
  if fuel = 0 then (acc, ctr)
  else
    match vals with
    | [] -> (acc, ctr)
    | v :: rest ->
      let (oterm, acc1, ctr1) = jld_expand_value v ctr acc (fuel - 1) in
      let acc2 =
        (match oterm with
         | Some t -> { s = subj; p = prop; o = t } :: acc1
         | None -> acc1) in
      jld_expand_property subj prop rest ctr1 acc2 (fuel - 1)

// ================================================================
// Top level: default graph + named graphs
// ================================================================

// Graph name slot for a named graph. Blank-node graph names are stored
// as the literal string "_:<label>" inside the iri-typed ng_name field —
// the Parser.NQuads convention (see that module's header and
// docs/designissues/2026-04-25-nquads-bnode-graph-fix.md).
let jld_graph_name_of_subject (s:subject) : iri =
  match s with
  | S_IRI i -> i
  | S_BNode b -> String.concat "" ["_:"; b]

// Expand every node object inside a @graph array.
let rec jld_expand_graph_nodes (nodes:list json_val) (ctr:nat) (acc:list triple) (fuel:nat)
  : Tot (list triple & nat) (decreases fuel) =
  if fuel = 0 then (acc, ctr)
  else
    match nodes with
    | [] -> (acc, ctr)
    | n :: rest ->
      let (_, acc1, ctr1) = jld_expand_node n ctr acc (fuel - 1) in
      jld_expand_graph_nodes rest ctr1 acc1 (fuel - 1)

// One top-level array entry. dflt and the per-named-graph triple lists
// are reversed accumulators; named collects named graphs in reverse.
let jld_expand_top (v:json_val) (dflt:list triple) (named:list named_graph)
                   (ctr:nat) (fuel:nat)
  : (list triple & list named_graph & nat) =
  match v with
  | JObject fields ->
    (match json_get_field "@graph" v with
     | Some g ->
       let (subj_opt, ctr1) =
         (match json_get_field "@id" v with
          | Some (JString id_str) -> (jld_id_to_subject id_str, ctr)
          | Some _ -> (None, ctr)
          | None ->
            let (b, ctr') = jld_fresh_bnode ctr in
            (Some (S_BNode b), ctr')) in
       (match subj_opt with
        | None -> (dflt, named, ctr1)
        | Some gsubj ->
          let (gtris, ctr2) = jld_expand_graph_nodes (jld_as_array g) ctr1 [] fuel in
          // Non-keyword members of the container node describe the
          // graph-name resource in the DEFAULT graph.
          let (dflt1, ctr3) = jld_expand_fields gsubj fields ctr2 dflt fuel in
          let ng = { ng_name = jld_graph_name_of_subject gsubj; ng_graph = gtris } in
          (dflt1, ng :: named, ctr3))
     | None ->
       let (_, dflt1, ctr1) = jld_expand_node v ctr dflt fuel in
       (dflt1, named, ctr1))
  | _ -> (dflt, named, ctr)

let rec jld_expand_tops (vs:list json_val) (dflt:list triple) (named:list named_graph)
                        (ctr:nat) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (dflt, named, ctr)
  else
    match vs with
    | [] -> (dflt, named, ctr)
    | v :: rest ->
      let (d1, n1, c1) = jld_expand_top v dflt named ctr fuel in
      jld_expand_tops rest d1 n1 c1 (fuel - 1)

// Is @graph the only key of an object? (Then it is the document wrapper
// and its contents belong to the default graph.)
let rec jld_only_graph_keys (fields:list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: rest -> k = "@graph" && jld_only_graph_keys rest

// ================================================================
// Public API
// ================================================================

// Deserialize an already-parsed expanded-form JSON-LD value tree.
// None when the top level is not an array or object.
let jld_dataset_of_json (root:json_val) : option rdf_dataset =
  let fuel = json_size root + 1 in
  match root with
  | JArray tops ->
    let (d, n, _) = jld_expand_tops tops [] [] 0 fuel in
    Some (dataset_finalise { ds_default = d; ds_named = List.Tot.rev n })
  | JObject fields ->
    let tops =
      if jld_only_graph_keys fields then
        (match json_get_field "@graph" root with
         | Some g -> jld_as_array g
         | None -> [root])
      else [root] in
    let (d, n, _) = jld_expand_tops tops [] [] 0 fuel in
    Some (dataset_finalise { ds_default = d; ds_named = List.Tot.rev n })
  | _ -> None

// True when a top-level JSON object document carries an inline @context
// member. A top-level JArray never carries a shared @context (JSON-LD
// @context only applies within an object) and keeps going straight down
// the expanded-form Phase 1 path.
let jld_has_inline_context (root:json_val) : bool =
  match root with
  | JObject fields -> List.Tot.existsb (fun (kv:(string & json_val)) -> fst kv = "@context") fields
  | _ -> false

// Parse a JSON-LD document into an RDF dataset. A document whose top level
// is a JObject carrying an inline @context is run through JSONLD.Expand
// first (PHASE 3a: JSONLD.Context + JSONLD.Expand, inline contexts only —
// see module banner); everything else takes the unchanged Phase 1 path
// straight into jld_dataset_of_json, which requires EXPANDED FORM input.
// None when the input is not valid RFC 8259 JSON, expansion hits an
// out-of-scope feature (module banner), or the top level is not an
// array/object.
let parse_jsonld (input:string) : option rdf_dataset =
  match parse_json input with
  | None -> None
  | Some root ->
    if jld_has_inline_context root then
      (match expand empty_active_context root with
       | None -> None
       | Some expanded -> jld_dataset_of_json expanded)
    else jld_dataset_of_json root
