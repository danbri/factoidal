module JSONLD.FromRdf

// ============================================================================
// JSON-LD 1.1 API — "Serialize RDF as JSON-LD Algorithm"
// (https://www.w3.org/TR/json-ld11-api/#serialize-rdf-as-json-ld-algorithm)
//
// fromRdf: takes an RDF dataset (as produced by Parser.NQuads) and returns
// the EXPANDED-form JSON-LD document as a Parser.JSON.json_val tree. The
// consumer (bin/jsonld-fromrdf-runner) then canonicalizes the result with
// Parser.JSONLD.jcanon_document and compares it, canonically, against the
// suite's expected -out.jsonld fixture.
//
// This module is the WHOLE fromRdf semantics: node-map construction,
// rdf:type -> @type folding, RDF-to-object value conversion (incl.
// useNativeTypes and rdf:JSON), and the RDF-collection -> @list conversion.
// The runner does file I/O, manifest traversal, and string comparison only
// (iron rule #7 / #11).
//
// The reference algorithm is mutation-and-object-identity heavy; here it is
// re-expressed purely/functionally. The list conversion, in particular, is
// done by a recursive `resolve`/`list_from` pass keyed off a GLOBAL
// referenced-once count and a per-node "list shape" predicate, which is
// order-independent (no in-place mutation of shared value objects needed).
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.JSON
open RDF.Graph.Executable

// ----------------------------------------------------------------------------
// Options (the subset of the fromRdf option surface the suite exercises).
// ----------------------------------------------------------------------------
// rdf_direction: the fromRdf `rdfDirection` API option (JSON-LD 1.1 API
// "Serialize RDF as JSON-LD"). None = drop/no special handling; Some
// "i18n-datatype" decodes a literal typed with the
// https://www.w3.org/ns/i18n#<lang>_<dir> datatype back into a value
// object bearing @direction (+ @language); Some "compound-literal"
// collapses a blank node bearing rdf:value/rdf:direction(/rdf:language)
// into such a value object. The two modes are mutually exclusive per the
// suite's cross-paired fixtures (di07/di08 request i18n-datatype but feed
// a COMPOUND literal, which must stay an ordinary node; di09/di10 request
// compound-literal but feed an i18n literal, which must stay a typed
// literal), so each transform is gated strictly on its own mode.
noeq type from_rdf_options = {
  use_native_types : bool;
  use_rdf_type     : bool;
  rdf_direction    : option string;
}

let default_options : from_rdf_options =
  { use_native_types = false; use_rdf_type = false; rdf_direction = None }

// ----------------------------------------------------------------------------
// Fixed vocabulary IRIs (plain strings; predicates/datatypes compare as
// strings). No '*' + ')' sequences here — plain URLs.
// ----------------------------------------------------------------------------
let rdf_type_iri  : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_first_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri  : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri   : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let rdf_json_iri  : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"
let rdf_list_iri  : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"
// Compound-literal (rdfDirection = "compound-literal") vocabulary.
let rdf_value_iri     : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#value"
let rdf_direction_iri : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#direction"
let rdf_language_iri  : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#language"
// i18n datatype prefix (rdfDirection = "i18n-datatype").
let i18n_prefix : string = "https://www.w3.org/ns/i18n#"

// xsd datatype IRIs, as plain strings (RDF.Term's xsd_* are wf_iri).
let sxsd_string  : string = xsd_string
let sxsd_integer : string = xsd_integer
let sxsd_double  : string = xsd_double
let sxsd_boolean : string = xsd_boolean

let strcat (a b : string) : string = String.concat "" [a; b]

// ----------------------------------------------------------------------------
// Intermediate object-value tree. Kept as an eqtype (no `noeq`) so property
// value lists can be de-duplicated with structural `=` (test 0017).
//   OV_Ref  s : a node reference {"@id": s}
//   OV_Val  j : a fully-built value object (a JObject with @value/@type/...)
//   OV_List l : an RDF collection converted to {"@list": [...]}
// ----------------------------------------------------------------------------
type ov =
  | OV_Ref  : string -> ov
  | OV_Val  : json_val -> ov
  | OV_List : list ov -> ov

// A node object under construction.
noeq type fr_node = {
  n_id    : string;
  n_blank : bool;
  n_types : list string;              // @type IRIs, insertion order, deduped
  n_props : list (string & list ov);  // predicate -> values, deduped
}

// A named graph's node map plus its (display) name.
noeq type named_nm = {
  gn_name  : string;
  gn_blank : bool;
  gn_map   : list fr_node;
}

// ----------------------------------------------------------------------------
// Display identifiers.
// ----------------------------------------------------------------------------
let subj_id (s:subject) : string =
  match s with
  | S_IRI i   -> i
  | S_BNode b -> strcat "_:" b

let subj_is_blank (s:subject) : bool = S_BNode? s

// Some (display-id, is_blank) when the object is a node (IRI/bnode); None for
// literals.
let term_node_id (o:rdf_term) : option (string & bool) =
  match o with
  | T_IRI i     -> Some (i, false)
  | T_BNode b   -> Some (strcat "_:" b, true)
  | T_Literal _ -> None

let starts_with_us (s:string) : bool =
  fs_byte_length s >= 2 && fs_byte_at s 0 = 0x5F && fs_byte_at s 1 = 0x3A

// ----------------------------------------------------------------------------
// Node-map primitives.
// ----------------------------------------------------------------------------
let rec find_node (nm:list fr_node) (id:string) : Tot (option fr_node) (decreases nm) =
  match nm with
  | [] -> None
  | n :: tl -> if n.n_id = id then Some n else find_node tl id

let node_exists (nm:list fr_node) (id:string) : bool = Some? (find_node nm id)

let ensure_node (nm:list fr_node) (id:string) (blank:bool) : list fr_node =
  if node_exists nm id then nm
  else nm @ [ { n_id = id; n_blank = blank; n_types = []; n_props = [] } ]

// Append preserving order, dropping structural duplicates.
let rec snoc_unique (#a:eqtype) (xs:list a) (x:a) : Tot (list a) (decreases xs) =
  match xs with
  | [] -> [x]
  | h :: tl -> if h = x then xs else h :: snoc_unique tl x

let rec find_prop (props:list (string & list ov)) (p:string)
  : Tot (option (list ov)) (decreases props) =
  match props with
  | [] -> None
  | (k, vals) :: tl -> if k = p then Some vals else find_prop tl p

let node_prop_single (n:fr_node) (p:string) : option ov =
  match find_prop n.n_props p with
  | Some [v] -> Some v
  | _ -> None

let rec prop_add (props:list (string & list ov)) (p:string) (v:ov)
  : Tot (list (string & list ov)) (decreases props) =
  match props with
  | [] -> [ (p, [v]) ]
  | (k, vals) :: tl ->
    if k = p then (k, snoc_unique vals v) :: tl
    else (k, vals) :: prop_add tl p v

let node_update_prop (nm:list fr_node) (id:string) (p:string) (v:ov) : list fr_node =
  List.Tot.map (fun n -> if n.n_id = id then { n with n_props = prop_add n.n_props p v } else n) nm

let node_update_type (nm:list fr_node) (id:string) (t:string) : list fr_node =
  List.Tot.map (fun n -> if n.n_id = id then { n with n_types = snoc_unique n.n_types t } else n) nm

// ----------------------------------------------------------------------------
// RDF-to-Object value conversion (JSON-LD 1.1 API §10.4).
// ----------------------------------------------------------------------------
let is_dec_digit (c:nat) : bool = c >= 0x30 && c <= 0x39

let rec all_dec_digits (s:string) (pos:nat) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else if pos >= fs_byte_length s then true
  else if is_dec_digit (fs_byte_at s pos) then all_dec_digits s (pos + 1) (fuel - 1)
  else false

// xsd:integer lexical space (approx): optional sign then one-or-more digits.
let is_int_lexeme (s:string) : bool =
  let n = fs_byte_length s in
  if n = 0 then false
  else
    let first = fs_byte_at s 0 in
    let start = if first = 0x2B || first = 0x2D then 1 else 0 in
    start < n && all_dec_digits s start (n - start + 1)

// Position of the first 'e'/'E' at or after pos, or -1.
let rec find_exp_char (s:string) (pos:nat) (fuel:nat) : Tot int (decreases fuel) =
  if fuel = 0 || pos >= fs_byte_length s then (-1)
  else
    let c = fs_byte_at s pos in
    if c = 0x65 || c = 0x45 then pos
    else find_exp_char s (pos + 1) (fuel - 1)

// Count decimal digits from pos to end (ignoring a sign byte).
let rec count_digits_from (s:string) (pos:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 || pos >= fs_byte_length s then 0
  else
    let c = fs_byte_at s pos in
    if is_dec_digit c then 1 + count_digits_from s (pos + 1) (fuel - 1)
    else count_digits_from s (pos + 1) (fuel - 1)

// A double lexeme is "natively serializable" iff it is a syntactically valid
// JSON number AND finite. Non-JSON forms ("+INF", "-INF", "NaN") and
// astronomically large exponents (which overflow to +/-Infinity, e.g.
// "0.1e999999999999999" in test 0027) are NOT native. The exponent-digit
// heuristic (<= 3 exponent digits) rejects the overflow cases while keeping
// ordinary doubles like "1.1E-1".
let is_finite_double (s:string) : bool =
  match parse_json s with
  | Some (JNumber _) ->
    let n = fs_byte_length s in
    let ei = find_exp_char s 0 (n + 1) in
    if ei < 0 then true
    else count_digits_from s (ei + 1) (n + 1) <= 3
  | _ -> false

let native_value (lex:string) (dt:string) : ov =
  if dt = sxsd_boolean then
    // xsd:boolean lexical space is {true, false, 1, 0} (test 0027's
    // boolean-number case: "1"/"0" are valid, "True"/"False"/"notnative"
    // are not and stay typed strings).
    (if lex = "true" || lex = "1" then OV_Val (JObject [("@value", JBool true)])
     else if lex = "false" || lex = "0" then OV_Val (JObject [("@value", JBool false)])
     else OV_Val (JObject [("@value", JString lex); ("@type", JString dt)]))
  else if dt = sxsd_integer then
    (if is_int_lexeme lex then OV_Val (JObject [("@value", JNumber lex)])
     else OV_Val (JObject [("@value", JString lex); ("@type", JString dt)]))
  else if dt = sxsd_double then
    (if is_finite_double lex then OV_Val (JObject [("@value", JNumber lex)])
     else OV_Val (JObject [("@value", JString lex); ("@type", JString dt)]))
  else
    OV_Val (JObject [("@value", JString lex); ("@type", JString dt)])

// True iff `s` begins with the bytes of `pfx`.
let str_has_prefix (s:string) (pfx:string) : bool =
  let ls = fs_byte_length s in
  let lp = fs_byte_length pfx in
  ls >= lp && fs_byte_sub s 0 lp = pfx

// Index of the LAST 0x5F ('_') byte of `s`, or `fs_byte_length s` when
// there is none (a sentinel the caller tests with `>= flen`).
let rec last_us_pos (s:string) (pos:nat) (best:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then best
  else if pos >= fs_byte_length s then best
  else last_us_pos s (pos + 1) (if fs_byte_at s pos = 0x5F then pos else best) (fuel - 1)

// rdfDirection="i18n-datatype" reverse: a literal typed
// https://www.w3.org/ns/i18n#<lang>_<dir> becomes a value object with
// @value = lexical form, @direction = <dir>, and @language = <lang> only
// when <lang> is non-empty (di05: "#_rtl" -> no @language; di06:
// "#en-us_rtl" -> @language "en-us"). Splits the fragment on its LAST
// '_' so a hyphenated language subtag ("en-us") stays intact.
let i18n_value_object (lex:string) (dt:string) : ov =
  let lp = fs_byte_length i18n_prefix in
  let dl = fs_byte_length dt in
  let frag = fs_byte_sub dt lp (if dl >= lp then dl - lp else 0) in
  let flen = fs_byte_length frag in
  let up = last_us_pos frag 0 flen (flen + 1) in
  let lang = if up >= flen then "" else fs_byte_sub frag 0 up in
  let dir  = if up >= flen then frag else fs_byte_sub frag (up + 1) (if flen > up + 1 then flen - up - 1 else 0) in
  let base = [ ("@value", JString lex) ] in
  let with_lang = if fs_byte_length lang > 0 then base @ [ ("@language", JString lang) ] else base in
  OV_Val (JObject (with_lang @ [ ("@direction", JString dir) ]))

// None signals a fatal "invalid JSON literal" error (negative tests js08/js09).
let rdf_to_object (opts:from_rdf_options) (o:rdf_term) : option ov =
  match o with
  | T_IRI i     -> Some (OV_Ref i)
  | T_BNode b   -> Some (OV_Ref (strcat "_:" b))
  | T_Literal l ->
    let lex : string = l.lexical_form in
    let dt  : string = l.datatype in
    (match l.lang_tag with
     | Some tag -> Some (OV_Val (JObject [("@value", JString lex); ("@language", JString tag)]))
     | None ->
       if opts.rdf_direction = Some "i18n-datatype" && str_has_prefix dt i18n_prefix then
         Some (i18n_value_object lex dt)
       else if dt = rdf_json_iri then
         (match parse_json lex with
          | Some j -> Some (OV_Val (JObject [("@value", j); ("@type", JString "@json")]))
          | None   -> None)
       else if dt = sxsd_string then
         Some (OV_Val (JObject [("@value", JString lex)]))
       else if opts.use_native_types then
         Some (native_value lex dt)
       else
         Some (OV_Val (JObject [("@value", JString lex); ("@type", JString dt)])))

// ----------------------------------------------------------------------------
// Node-map construction (per graph).
// ----------------------------------------------------------------------------
let process_triple (opts:from_rdf_options) (nm:list fr_node) (t:triple)
  : option (list fr_node) =
  let s_id = subj_id t.s in
  let s_blank = subj_is_blank t.s in
  let nm1 = ensure_node nm s_id s_blank in
  let nm2 = (match term_node_id t.o with
             | Some (oid, ob) -> ensure_node nm1 oid ob
             | None -> nm1) in
  let p : string = t.p in
  let obj_is_node = (T_IRI? t.o || T_BNode? t.o) in
  if p = rdf_type_iri && not opts.use_rdf_type && obj_is_node then
    (match term_node_id t.o with
     | Some (oid, _) -> Some (node_update_type nm2 s_id oid)
     | None -> Some nm2)
  else
    (match rdf_to_object opts t.o with
     | None -> None
     | Some v -> Some (node_update_prop nm2 s_id p v))

let rec build_nodemap (opts:from_rdf_options) (nm:list fr_node) (ts:list triple)
  : Tot (option (list fr_node)) (decreases ts) =
  match ts with
  | [] -> Some nm
  | t :: tl ->
    (match process_triple opts nm t with
     | None -> None
     | Some nm' -> build_nodemap opts nm' tl)

let rec build_named (opts:from_rdf_options) (ngs:list named_graph)
  : Tot (option (list named_nm)) (decreases ngs) =
  match ngs with
  | [] -> Some []
  | ng :: tl ->
    (match build_nodemap opts [] ng.ng_graph with
     | None -> None
     | Some m ->
       (match build_named opts tl with
        | None -> None
        | Some others ->
          Some ({ gn_name = ng.ng_name; gn_blank = starts_with_us ng.ng_name; gn_map = m } :: others)))

let rec add_graph_names (nm:list fr_node) (named:list named_nm)
  : Tot (list fr_node) (decreases named) =
  match named with
  | [] -> nm
  | g :: tl -> add_graph_names (ensure_node nm g.gn_name g.gn_blank) tl

let rec is_graph_name (named:list named_nm) (id:string) : Tot bool (decreases named) =
  match named with
  | [] -> false
  | g :: tl -> if g.gn_name = id then true else is_graph_name tl id

let rec lookup_graph_map (named:list named_nm) (id:string)
  : Tot (option (list fr_node)) (decreases named) =
  match named with
  | [] -> None
  | g :: tl -> if g.gn_name = id then Some g.gn_map else lookup_graph_map tl id

// ----------------------------------------------------------------------------
// Global "referenced exactly once" count (across ALL graphs — see tests
// 0020/0021, where a blank list node referenced from a second graph is NOT
// collapsed).
// ----------------------------------------------------------------------------
let rec ovs_refids (vs:list ov) : Tot (list string) (decreases vs) =
  match vs with
  | [] -> []
  | OV_Ref x :: tl -> x :: ovs_refids tl
  | _ :: tl -> ovs_refids tl

let rec props_refids (props:list (string & list ov)) : Tot (list string) (decreases props) =
  match props with
  | [] -> []
  | (_, vals) :: tl -> ovs_refids vals @ props_refids tl

let rec nodes_refids (nm:list fr_node) : Tot (list string) (decreases nm) =
  match nm with
  | [] -> []
  | n :: tl -> props_refids n.n_props @ nodes_refids tl

let rec maps_refids (maps:list (list fr_node)) : Tot (list string) (decreases maps) =
  match maps with
  | [] -> []
  | m :: tl -> nodes_refids m @ maps_refids tl

let count_occ (xs:list string) (x:string) : nat =
  List.Tot.length (List.Tot.filter (fun y -> y = x) xs)

let referenced_once (refids:list string) (id:string) : bool = count_occ refids id = 1

// ----------------------------------------------------------------------------
// Compound-literal (rdfDirection = "compound-literal") collapse.
//
// A blank node bearing rdf:value / rdf:direction (/ rdf:language) is folded
// into a value object {"@value": ..., "@language"?: ..., "@direction": ...}
// and every referenced-once reference to it is replaced with that object —
// the exact reverse of jld_compound_literal_term on the toRdf side (di11,
// di12). Gated on cl_mode so an i18n-datatype run (di07/di08) leaves the
// same blank node untouched.
// ----------------------------------------------------------------------------
let rec obj_lookup (fields:list (string & json_val)) (k:string)
  : Tot (option json_val) (decreases fields) =
  match fields with
  | [] -> None
  | (k2, v) :: tl -> if k2 = k then Some v else obj_lookup tl k

// The @value payload of a literal ov (an OV_Val whose JObject carries a
// "@value" field) — lifts a compound literal's rdf:value / rdf:language /
// rdf:direction sub-literals into the emitted value object.
let cl_field (n:fr_node) (p:string) : option json_val =
  match node_prop_single n p with
  | Some (OV_Val (JObject fields)) -> obj_lookup fields "@value"
  | _ -> None

// A compound-literal blank node: one rdf:value and one rdf:direction
// (rdf:language optional). rdf:direction is the property the reference
// algorithm keys its "compound literal subjects" set on.
let is_cl_shape (n:fr_node) : bool =
  n.n_blank
  && Some? (node_prop_single n rdf_value_iri)
  && Some? (node_prop_single n rdf_direction_iri)

let cl_value_object (n:fr_node) : option json_val =
  match cl_field n rdf_value_iri, cl_field n rdf_direction_iri with
  | Some v, Some d ->
    let lang = cl_field n rdf_language_iri in
    Some (JObject ([ ("@value", v) ]
                   @ (match lang with Some l -> [ ("@language", l) ] | None -> [])
                   @ [ ("@direction", d) ]))
  | _, _ -> None

// Collapsible compound literal: a referenced-once blank node of cl-shape.
let is_cl_collapsible (g:list fr_node) (refids:list string) (id:string) : bool =
  match find_node g id with
  | None -> false
  | Some n -> is_cl_shape n && referenced_once refids id

// ----------------------------------------------------------------------------
// RDF collection -> @list conversion.
// ----------------------------------------------------------------------------

// A blank node whose ONLY properties are exactly one rdf:first and one
// rdf:rest (optionally typed rdf:List) — the shape a list cell must have.
let is_list_shape (n:fr_node) : bool =
  n.n_blank &&
  (n.n_types = [] || n.n_types = [rdf_list_iri]) &&
  List.Tot.length n.n_props = 2 &&
  Some? (node_prop_single n rdf_first_iri) &&
  Some? (node_prop_single n rdf_rest_iri)

// A node id is "collapsible" iff it is a referenced-once blank list cell whose
// rest chain terminates at rdf:nil (cycles never reach nil, so they are not
// collapsible — test 0012).
let rec is_collapsible (g:list fr_node) (refids:list string) (id:string) (fuel:nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match find_node g id with
    | None -> false
    | Some n ->
      if not (is_list_shape n) then false
      else if not (referenced_once refids id) then false
      else
        (match node_prop_single n rdf_rest_iri with
         | Some (OV_Ref rt) ->
           if rt = rdf_nil_iri then true
           else is_collapsible g refids rt (fuel - 1)
         | _ -> false)

// list_from: the ordered element list of a collapsible chain starting at `id`.
// resolve: rewrite a single value, expanding a reference to a collapsible list
// head (or to rdf:nil) into a nested @list.
let rec list_from (g:list fr_node) (refids:list string) (cl_mode:bool) (id:string) (fuel:nat)
  : Tot (list ov) (decreases fuel) =
  if fuel = 0 then []
  else
    match find_node g id with
    | None -> []
    | Some n ->
      (match node_prop_single n rdf_first_iri, node_prop_single n rdf_rest_iri with
       | Some fv, Some (OV_Ref rt) ->
         let elem = resolve g refids cl_mode fv (fuel - 1) in
         if rt = rdf_nil_iri then [elem]
         else elem :: list_from g refids cl_mode rt (fuel - 1)
       | _, _ -> [])

and resolve (g:list fr_node) (refids:list string) (cl_mode:bool) (v:ov) (fuel:nat)
  : Tot ov (decreases fuel) =
  if fuel = 0 then v
  else
    match v with
    | OV_Ref x ->
      if x = rdf_nil_iri then OV_List []
      else if is_collapsible g refids x fuel then OV_List (list_from g refids cl_mode x (fuel - 1))
      else if cl_mode && is_cl_collapsible g refids x then
        (match find_node g x with
         | Some n -> (match cl_value_object n with Some j -> OV_Val j | None -> OV_Ref x)
         | None -> OV_Ref x)
      else OV_Ref x
    | OV_Val j -> OV_Val j
    | OV_List l -> OV_List l

let rewrite_node (g:list fr_node) (refids:list string) (cl_mode:bool) (fuel:nat) (n:fr_node) : fr_node =
  { n with n_props =
      List.Tot.map
        (fun (pv:(string & list ov)) ->
           let (p, vals) = pv in
           (p, List.Tot.map (fun v -> resolve g refids cl_mode v fuel) vals))
        n.n_props }

// ----------------------------------------------------------------------------
// JSON emission.
// ----------------------------------------------------------------------------
let rec ov_to_json (v:ov) : Tot json_val (decreases v) =
  match v with
  | OV_Ref id -> JObject [("@id", JString id)]
  | OV_Val j  -> j
  | OV_List l -> JObject [("@list", JArray (ov_list_to_json l))]

and ov_list_to_json (l:list ov) : Tot (list json_val) (decreases l) =
  match l with
  | [] -> []
  | v :: tl -> ov_to_json v :: ov_list_to_json tl

let types_field (types:list string) : list (string & json_val) =
  if Cons? types then [ ("@type", JArray (List.Tot.map (fun (t:string) -> JString t) types)) ]
  else []

let graph_field (gj:option (list json_val)) : list (string & json_val) =
  match gj with
  | Some gs -> [ ("@graph", JArray gs) ]
  | None -> []

let props_fields (props:list (string & list ov)) : list (string & json_val) =
  List.Tot.map
    (fun (pv:(string & list ov)) ->
       let (p, vals) = pv in
       (p, JArray (List.Tot.map ov_to_json vals)))
    props

let node_to_json (n:fr_node) (gj:option (list json_val)) : json_val =
  JObject ( [ ("@id", JString n.n_id) ]
            @ types_field n.n_types
            @ graph_field gj
            @ props_fields n.n_props )

// ----------------------------------------------------------------------------
// Node ordering (byte-order on @id, matching the reference processor and the
// pre-sorted expected fixtures).
// ----------------------------------------------------------------------------
let rec insert_sorted_node (n:fr_node) (xs:list fr_node) : Tot (list fr_node) (decreases xs) =
  match xs with
  | [] -> [n]
  | h :: tl -> if string_lt n.n_id h.n_id then n :: xs else h :: insert_sorted_node n tl

let rec sort_nodes (xs:list fr_node) : Tot (list fr_node) (decreases xs) =
  match xs with
  | [] -> []
  | h :: tl -> insert_sorted_node h (sort_nodes tl)

// ----------------------------------------------------------------------------
// Per-graph node emission.
// ----------------------------------------------------------------------------
let graph_fuel (g:list fr_node) : nat = op_Multiply 4 (List.Tot.length g) + 16

// A named graph's contents (no nested graph names in a 2-level dataset).
// cl_mode drops collapsed compound-literal blank nodes from the survivors
// (their references were rewritten into inline value objects).
let emit_named_nodes (g:list fr_node) (refids:list string) (cl_mode:bool) : list json_val =
  let fuel = graph_fuel g in
  let survivors =
    List.Tot.filter
      (fun n -> not (is_collapsible g refids n.n_id fuel)
                && not (cl_mode && is_cl_collapsible g refids n.n_id)
                && (Cons? n.n_types || Cons? n.n_props))
      g in
  let rewritten = List.Tot.map (rewrite_node g refids cl_mode fuel) survivors in
  let ordered = sort_nodes rewritten in
  List.Tot.map (fun n -> node_to_json n None) ordered

// The default graph: same survivorship, plus graph-name nodes carry @graph.
let emit_default_nodes (dm:list fr_node) (named:list named_nm) (refids:list string) (cl_mode:bool)
  : list json_val =
  let fuel = graph_fuel dm in
  let survivors =
    List.Tot.filter
      (fun n -> not (is_collapsible dm refids n.n_id fuel)
                && not (cl_mode && is_cl_collapsible dm refids n.n_id)
                && (Cons? n.n_types || Cons? n.n_props || is_graph_name named n.n_id))
      dm in
  let rewritten = List.Tot.map (rewrite_node dm refids cl_mode fuel) survivors in
  let ordered = sort_nodes rewritten in
  List.Tot.map
    (fun n ->
       let gj =
         if is_graph_name named n.n_id then
           (match lookup_graph_map named n.n_id with
            | Some gm -> Some (emit_named_nodes gm refids cl_mode)
            | None -> Some [])
         else None in
       node_to_json n gj)
    ordered

// ----------------------------------------------------------------------------
// Entry point. Returns None on a fatal "invalid JSON literal" error; otherwise
// Some (JArray of expanded-form node objects).
// ----------------------------------------------------------------------------
let from_rdf (ds:rdf_dataset) (opts:from_rdf_options) : option json_val =
  match build_nodemap opts [] ds.ds_default with
  | None -> None
  | Some dm0 ->
    (match build_named opts ds.ds_named with
     | None -> None
     | Some named ->
       let dm = add_graph_names dm0 named in
       let all_maps = dm :: List.Tot.map (fun (g:named_nm) -> g.gn_map) named in
       let refids = maps_refids all_maps in
       let cl_mode = (opts.rdf_direction = Some "compound-literal") in
       Some (JArray (emit_default_nodes dm named refids cl_mode)))
