module JSONLD.Expand

// ============================================================================
// JSON-LD 1.1 Expansion — PHASE 3a.
//
// Produces EXPANDED-FORM json_val trees (node objects keyed by absolute
// IRI / keyword, property values array-wrapped, value objects using
// "@value") from compact-or-mixed-form input plus an active context
// (JSONLD.Context). The output feeds Parser.JSONLD's existing jld_*
// pipeline unchanged — see that module's banner for exactly what shape it
// expects and how it interprets it.
//
// Scope (see docs/designissues/2026-07-04-jsonld-program-lessons.md and
// JSONLD.Context's banner for the context-processing half of the cut):
//   - node objects: term / compact-IRI keys -> absolute IRI keys; @id
//     resolution (document-relative expand_iri); @type (string or array,
//     vocab-relative); nested node objects in property position; a node
//     object's own inline @context (re-processed via context_process,
//     scoping to that object and its descendants — this is core context
//     processing, not the term/type-scoped-context FEATURE, which stays
//     out of scope, see below);
//   - value objects: bare scalars wrapped per the term's @type coercion
//     (@id / @vocab / a datatype IRI) and @language (term override or the
//     context default), plus already-compact value objects
//     ({"@value": ..., "@type": "xsd:integer"});
//   - @list: both the explicit {"@list": [...]} shape and a term's
//     "@container": "@list" mapping;
//   - @graph: recursively expanded, passed through as a keyword (Phase 1
//     jld_* already understands @graph at the top level and, via
//     jld_expand_top, at one level of "@id" + "@graph" nesting).
//
// OUT of scope for 3a — expand returns None (a document that needs one of
// these stays an honest FAIL rather than silently-wrong RDF):
//   - @reverse (term-level or inline);
//   - @index / @included / @nest;
//   - @direction (rdf:direction / i18n-datatype literals);
//   - a term whose IRI mapping was itself defined via "@reverse" (used as
//     a plain forward property);
//   - any other node-object keyword this module does not recognize
//     (property- and type-scoped contexts surface here as an unrecognized
//     "@context" INSIDE a term definition, already rejected one layer
//     down by JSONLD.Context.process_term_def_obj).
//
// FUEL: mutual recursion is bounded by an explicit fuel parameter derived
// from Parser.JSON.json_size, the same shape as Parser.JSONLD's own
// jld_expand_* family. The constant factor is more generous than that
// module's (json_size * 2 + 16 instead of + 1) because this module makes
// more than one fuel-consuming hop per json_val node (context extraction,
// term lookup, keyword-alias forwarding) — see expand at the bottom.
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.JSON
open JSONLD.Context

// ================================================================
// Small helpers (no recursion into node/value objects; safe to define
// ahead of the fuel-threaded mutual group below)
// ================================================================

// Expanded form wraps property values in arrays; be lenient about a bare
// value where an array is required (mirrors Parser.JSONLD.jld_as_array).
let jexp_as_array (v:json_val) : list json_val =
  match v with
  | JArray items -> items
  | _ -> [v]

let jexp_has_field (name:string) (fields:list (string & json_val)) : bool =
  List.Tot.existsb (fun (kv:(string & json_val)) -> fst kv = name) fields

// Wrap a bare boolean/number scalar as a value object, applying a term's
// @type coercion when present. @id / @vocab coercion is meaningless for a
// non-string scalar (there is no lexical form to resolve as an IRI), so it
// falls back to the uncoerced value object rather than failing the field.
let jexp_wrap_scalar (type_map:option string) (v:json_val) : json_val =
  match type_map with
  | Some dt ->
    if dt = "@id" || dt = "@vocab" then JObject [("@value", v)]
    else JObject [("@value", v); ("@type", JString dt)]
  | None -> JObject [("@value", v)]

// A value object already given in @value form (compact or expanded): pull
// out @value / @language / @type, expanding a compact-IRI @type via the
// active context. None on a non-conforming shape (both @language and
// @type; @direction present — OUT of scope for 3a).
let jexp_expand_value_object (ac:active_context) (fields:list (string & json_val))
  : option json_val =
  match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@value") fields with
  | None -> None
  | Some (_, v) ->
    if List.Tot.existsb (fun (kv:(string & json_val)) -> fst kv = "@direction") fields then None
    else
      let lang = (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@language") fields with
                  | Some (_, JString s) -> Some s | _ -> None) in
      let typ = (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@type") fields with
                 | Some (_, JString s) -> Some s | _ -> None) in
      (match (lang, typ) with
       | (Some _, Some _) -> None
       | (Some lg, None) -> Some (JObject [("@value", v); ("@language", JString lg)])
       | (None, Some t) ->
         (match expand_iri ac t true with
          | None -> None
          | Some iri -> Some (JObject [("@value", v); ("@type", JString iri)]))
       | (None, None) -> Some (JObject [("@value", v)]))

// Split a node object's members into its (at most one) @context value and
// the rest, so the caller can re-run context_process before expanding the
// remaining members.
let jexp_extract_context (fields:list (string & json_val))
  : (option json_val & list (string & json_val)) =
  let ctxval = (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@context") fields with
                | Some (_, v) -> Some v | None -> None) in
  let rest = List.Tot.filter (fun (kv:(string & json_val)) -> fst kv <> "@context") fields in
  (ctxval, rest)

// @type values: vocab-relative IRI expansion of every string entry;
// non-conforming entries (non-string, or unresolvable) are dropped rather
// than failing the whole node, mirroring Parser.JSONLD.jld_type_prepend's
// existing leniency.
let rec jexp_expand_type_items (ac:active_context) (items:list json_val)
  : Tot (list json_val) (decreases items) =
  match items with
  | [] -> []
  | JString t :: rest ->
    (match expand_iri ac t true with
     | Some iri -> JString iri :: jexp_expand_type_items ac rest
     | None -> jexp_expand_type_items ac rest)
  | _ :: rest -> jexp_expand_type_items ac rest

let expand_type_values (ac:active_context) (value:json_val) : list json_val =
  jexp_expand_type_items ac (jexp_as_array value)

// ================================================================
// Fuel-threaded mutual recursion over the document tree.
//
// Every function below follows the "if fuel = 0 then <safe default> else
// ..." shape from Parser.JSON / Parser.JSONLD, and every recursive call in
// this group passes fuel - 1 (never the same fuel), which is what the
// (decreases fuel) obligation needs. The three-way result shapes used
// here:
//   - option json_val for "expand this required sub-tree": None = fatal
//     (out-of-scope feature hit, or malformed input) and propagates up.
//   - option (option json_val) for "expand this property value":
//     None = fatal; Some None = valid-but-empty (JSON null; drop
//     silently); Some (Some v) = produced v.
// ================================================================

let rec expand_node (ac:active_context) (v:json_val) (fuel:nat)
  : Tot (option json_val) (decreases fuel) =
  if fuel = 0 then None
  else
    match v with
    | JObject fields ->
      let (ctxval, fields1) = jexp_extract_context fields in
      let ac_eff_opt =
        (match ctxval with
         | None -> Some ac
         | Some cv -> context_process ac cv) in
      (match ac_eff_opt with
       | None -> None
       | Some ac_eff ->
         (match expand_fields_list ac_eff fields1 (fuel - 1) with
          | None -> None
          | Some outfields -> Some (JObject outfields)))
    | _ -> None

and expand_fields_list (ac:active_context) (fields:list (string & json_val)) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else
    match fields with
    | [] -> Some []
    | (key, value) :: rest ->
      (match expand_one_field ac key value (fuel - 1) with
       | None -> None
       | Some None -> expand_fields_list ac rest (fuel - 1)
       | Some (Some outkv) ->
         (match expand_fields_list ac rest (fuel - 1) with
          | None -> None
          | Some restout -> Some (outkv :: restout)))

// One member of a node object. @id / @type / @graph are handled directly;
// @reverse / @index / @included / @nest (and any other unrecognized
// keyword) are OUT of scope and fail the whole node; an ordinary
// term/compact-IRI/absolute-IRI key is resolved via expand_iri and, when
// it resolves to a keyword (a keyword ALIAS term), re-dispatched as that
// keyword.
and expand_one_field (ac:active_context) (key:string) (value:json_val) (fuel:nat)
  : Tot (option (option (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else if key = "@id" then
    (match value with
     | JString s ->
       (match expand_iri ac s false with
        | None -> Some None
        | Some iri -> Some (Some ("@id", JString iri)))
     | _ -> None)
  else if key = "@type" then
    Some (Some ("@type", JArray (expand_type_values ac value)))
  else if key = "@graph" then
    Some (Some ("@graph", JArray (expand_graph_items ac (jexp_as_array value) (fuel - 1))))
  else if key = "@reverse" then None
  else if key = "@index" then None
  else if key = "@included" then None
  else if key = "@nest" then None
  else if jldctx_is_keyword key then None
  else
    (match expand_iri ac key true with
     | None -> Some None
     | Some prop_iri ->
       if jldctx_is_keyword prop_iri then
         expand_aliased_field ac prop_iri value (fuel - 1)
       else
         (match jldctx_find_term ac.ac_terms key with
          | Some td ->
            if td.td_reverse then None
            else expand_ordinary_property ac (Some td) prop_iri value (fuel - 1)
          | None -> expand_ordinary_property ac None prop_iri value (fuel - 1)))

// A property whose key already resolved to an absolute IRI (prop_iri) and
// whose term definition (if any) supplies @type coercion / @language
// override / @container:@list.
and expand_ordinary_property (ac:active_context) (term_opt:option term_def) (prop_iri:string)
                              (value:json_val) (fuel:nat)
  : Tot (option (option (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else
    let type_map = (match term_opt with Some td -> td.td_type_mapping | None -> None) in
    let lang_ovr = (match term_opt with Some td -> td.td_language | None -> None) in
    let is_list = (match term_opt with Some td -> td.td_container_list | None -> false) in
    (match expand_property ac type_map lang_ovr (jexp_as_array value) (fuel - 1) with
     | None -> None
     | Some items ->
       if is_list
       then Some (Some (prop_iri, JArray [JObject [("@list", JArray items)]]))
       else Some (Some (prop_iri, JArray items)))

// A term whose IRI mapping is itself a keyword (e.g. "id": "@id") applies
// to its value exactly as that keyword would.
and expand_aliased_field (ac:active_context) (canon_key:string) (value:json_val) (fuel:nat)
  : Tot (option (option (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else expand_one_field ac canon_key value (fuel - 1)

// The array of raw values for one property (already array-wrapped by the
// caller via jexp_as_array).
and expand_property (ac:active_context) (type_map:option string) (lang_ovr:option (option string))
                     (items:list json_val) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | v :: rest ->
      (match expand_item ac type_map lang_ovr v (fuel - 1) with
       | None -> None
       | Some None -> expand_property ac type_map lang_ovr rest (fuel - 1)
       | Some (Some one) ->
         (match expand_property ac type_map lang_ovr rest (fuel - 1) with
          | None -> None
          | Some restout -> Some (one :: restout)))

// One property value: an explicit value object ({"@value": ...}), a list
// object ({"@list": [...]}), a nested node object, a node reference, or a
// bare scalar coerced per type_map / lang_ovr. JSON null produces nothing
// (Some None); @reverse inside a property value is OUT of scope.
and expand_item (ac:active_context) (type_map:option string) (lang_ovr:option (option string))
                (v:json_val) (fuel:nat)
  : Tot (option (option json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match v with
    | JNull -> Some None
    | JObject fields ->
      if jexp_has_field "@value" fields then
        (match jexp_expand_value_object ac fields with
         | None -> None
         | Some vo -> Some (Some vo))
      else if jexp_has_field "@list" fields then
        (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@list") fields with
         | None -> None
         | Some (_, lstval) ->
           (match expand_property ac type_map lang_ovr (jexp_as_array lstval) (fuel - 1) with
            | None -> None
            | Some items -> Some (Some (JObject [("@list", JArray items)]))))
      else if jexp_has_field "@reverse" fields then None
      else
        (match expand_node ac v (fuel - 1) with
         | None -> None
         | Some nodeobj -> Some (Some nodeobj))
    | JString s ->
      (match type_map with
       | None ->
         let eff_lang = (match lang_ovr with Some l -> l | None -> ac.ac_language) in
         (match eff_lang with
          | Some lg -> Some (Some (JObject [("@value", JString s); ("@language", JString lg)]))
          | None -> Some (Some (JObject [("@value", JString s)])))
       | Some dt ->
         if dt = "@id" then
           (match expand_iri ac s false with
            | None -> Some None
            | Some iri -> Some (Some (JObject [("@id", JString iri)])))
         else if dt = "@vocab" then
           (match expand_iri ac s true with
            | None -> Some None
            | Some iri -> Some (Some (JObject [("@id", JString iri)])))
         else
           Some (Some (JObject [("@value", JString s); ("@type", JString dt)])))
    | JBool _ -> Some (Some (jexp_wrap_scalar type_map v))
    | JNumber _ -> Some (Some (jexp_wrap_scalar type_map v))
    | JArray _ -> None

// The contents of a @graph array (or a top-level array of node objects):
// each entry is expanded as a node object; a malformed entry is dropped
// rather than failing the whole graph, matching the leniency already
// established at every other level of this pipeline.
and expand_graph_items (ac:active_context) (items:list json_val) (fuel:nat)
  : Tot (list json_val) (decreases fuel) =
  if fuel = 0 then []
  else
    match items with
    | [] -> []
    | v :: rest ->
      (match expand_node ac v (fuel - 1) with
       | None -> expand_graph_items ac rest (fuel - 1)
       | Some nodeobj -> nodeobj :: expand_graph_items ac rest (fuel - 1))

// ================================================================
// Public API
// ================================================================

// Expand a document (already parsed as a json_val, NOT yet in expanded
// form) against an active context, producing an EXPANDED-FORM json_val
// suitable for Parser.JSONLD.jld_dataset_of_json. None when expansion hits
// an OUT-of-scope feature or the top level is not an object or array.
let expand (ac:active_context) (doc:json_val) : Tot (option json_val) =
  let fuel = op_Multiply 2 (json_size doc) + 16 in
  match doc with
  | JObject _ ->
    (match expand_node ac doc fuel with
     | None -> None
     | Some (JObject []) -> Some (JArray [])
     | Some nodeobj -> Some (JArray [nodeobj]))
  | JArray items -> Some (JArray (expand_graph_items ac items fuel))
  | _ -> None
