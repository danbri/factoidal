module JSONLD.Expand

// ============================================================================
// JSON-LD 1.1 Expansion — PHASE 3a + PHASE 3b (@reverse, map-shaped
// containers).
//
// Produces EXPANDED-FORM json_val trees (node objects keyed by absolute
// IRI / keyword, property values array-wrapped, value objects using
// "@value") from compact-or-mixed-form input plus an active context
// (JSONLD.Context). The output feeds Parser.JSONLD's existing jld_*
// pipeline — see that module's banner for exactly what shape it expects
// and how it interprets it (3b extends that pipeline too, for @reverse
// consumption — the two banners describe matching halves of one feature).
//
// Scope (see docs/designissues/2026-07-04-jsonld-program-lessons.md and
// JSONLD.Context's banner for the context-processing half of the cut):
//   - node objects: term / compact-IRI keys -> absolute IRI keys; @id
//     resolution (document-relative expand_iri, now full RFC 3986
//     against @base — see JSONLD.Context.jldctx_resolve); @type (string or
//     array, vocab-relative); nested node objects in property position; a
//     node object's own inline @context (re-processed via context_process,
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
//     jld_expand_top, at one level of "@id" + "@graph" nesting);
//   - @reverse (3b): a term whose definition carries "@reverse" (used
//     FORWARD, e.g. {"defines": {"@reverse": "rdfs:definedBy"}}) folds its
//     value into an ("@reverse", {predIri: [...]}) output field instead of
//     a plain property; an inline "@reverse": {...} node-object member
//     expands each of ITS keys as an ordinary (forward) term/IRI and
//     folds them the same way. Multiple @reverse-producing entries (an
//     inline block plus one or more reverse terms) may appear as separate
//     ("@reverse", ...) tuples in the output field list — Parser.JSONLD's
//     jld_expand_fields processes every field-list entry regardless of
//     key repetition, so this needs no merge step;
//   - map-shaped containers (3b): a term's "@container": "@index" /
//     "@language" / "@id" / "@type" flattens a JSON-object VALUE into an
//     item list per JSON-LD 1.1 API §5.3.3ish (Container Mapping), using
//     the map key as, respectively: dropped metadata, a "@language" tag
//     (or none for the "@none" key), the item's "@id" (unless already
//     present, or the key is "@none"), or an added "@type" entry (unless
//     the key is "@none"). A term whose ACTUAL value is not a JSON object
//     (e.g. an ordinary array) falls back to plain array processing, per
//     spec — the container mapping only applies to object-shaped values.
//
// OUT of scope for 3b — expand returns None (a document that needs one of
// these stays an honest FAIL rather than silently-wrong RDF):
//   - @included / @nest;
//   - @direction (rdf:direction / i18n-datatype literals);
//   - "@container" combinations involving "@graph" (graph containers;
//     rejected one layer down by JSONLD.Context's container-kind parser);
//   - any other node-object keyword this module does not recognize
//     (property- and type-scoped contexts surface here as an unrecognized
//     "@context" INSIDE a term definition, already rejected one layer
//     down by JSONLD.Context.process_term_def_obj).
//
// FUEL: mutual recursion is bounded by an explicit fuel parameter derived
// from Parser.JSON.json_size, the same shape as Parser.JSONLD's own
// jld_expand_* family. The constant factor is more generous than that
// module's (json_size * 3 + 32, bumped from 3a's * 2 + 16 to cover 3b's
// extra hops for reverse-block / map-container dispatch) because this
// module makes more than one fuel-consuming hop per json_val node (context
// extraction, term lookup, keyword-alias forwarding, container dispatch)
// — see expand at the bottom.
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
// Map-shaped container helpers (@index / @language / @id / @type).
//
// None of these need the fuel-threaded mutual group below: @index
// flattening just drops the key (jexp_flatten_map_entries feeds its
// result back into the ordinary expand_property pipeline, which DOES
// thread fuel), and @language-map expansion never recurses into node
// objects (only ever produces flat value objects). @id/@type map
// expansion DOES need to recurse into node objects (their values may be
// full nested node objects), so those two live inside the mutual group
// further down, right next to expand_item which they call.
// ================================================================

// @index containers (JSON-LD 1.1 API Container Mapping, @index case): the
// map key carries no RDF meaning (an in-document "@index" member on an
// individual item, if present, is separately just an ordinary keyword
// that jld_expand_fields/expand_one_field already drop) — only the
// (possibly array-wrapped) values matter, flattened into one item list.
let rec jexp_flatten_map_entries (entries:list (string & json_val))
  : Tot (list json_val) (decreases entries) =
  match entries with
  | [] -> []
  | (_, v) :: rest -> List.Tot.append (jexp_as_array v) (jexp_flatten_map_entries rest)

// @language containers: each map key is a language tag, or "@none" for an
// entry that gets no @language at all (a plain string value object,
// term-level @language default notwithstanding — an explicit language-map
// key always overrides). Non-string / null entries are dropped, mirroring
// the leniency elsewhere in this module.
let jexp_language_map_item (key:string) (v:json_val) : option json_val =
  match v with
  | JString s ->
    if key = "@none"
    then Some (JObject [("@value", JString s)])
    else Some (JObject [("@value", JString s); ("@language", JString key)])
  | _ -> None

let rec jexp_language_map_entry_items (key:string) (items:list json_val)
  : Tot (list json_val) (decreases items) =
  match items with
  | [] -> []
  | v :: rest ->
    (match jexp_language_map_item key v with
     | Some it -> it :: jexp_language_map_entry_items key rest
     | None -> jexp_language_map_entry_items key rest)

let rec jexp_expand_language_map (entries:list (string & json_val))
  : Tot (list json_val) (decreases entries) =
  match entries with
  | [] -> []
  | (k, v) :: rest ->
    List.Tot.append (jexp_language_map_entry_items k (jexp_as_array v))
                     (jexp_expand_language_map rest)

// @id / @type map post-processing: inject the map key (already IRI-
// expanded by the caller) into an already-expanded item. @id only applies
// when the item doesn't already carry its own "@id" (spec: an explicit
// "@id" in the value wins over the map key); @type never conflicts this
// way — Parser.JSONLD's jld_expand_fields processes EVERY "@type" entry
// in a node object's field list (not just the first, unlike "@id" which
// json_get_field resolves to the first match), so prepending a second
// "@type" tuple rather than merging into any existing "@type" array is
// enough to make both contribute rdf:type triples.
let jexp_set_id_if_absent (iri:string) (item:json_val) : json_val =
  match item with
  | JObject fields ->
    if jexp_has_field "@value" fields then item
    else if jexp_has_field "@id" fields then item
    else JObject (("@id", JString iri) :: fields)
  | _ -> item

let jexp_add_type_to_item (kiri:string) (item:json_val) : json_val =
  match item with
  | JObject fields ->
    if jexp_has_field "@value" fields then item
    else JObject (("@type", JArray [JString kiri]) :: fields)
  | _ -> item

// A container-map key, resolved to either "no override" (the literal
// keyword "@none", OR a term/alias whose OWN mapping IS "@none" — e.g.
// toRdf/m011's {"none": "@none"} lets a document write "none" instead of
// "@none" as a map key — expand_iri would otherwise happily resolve
// "none" to the literal string "@none" and we'd wrongly try to use that
// as an @id/@type value) or the resolved IRI to apply.
let jexp_map_key_iri (ac:active_context) (k:string) (vocab:bool) : option string =
  if k = "@none" then None
  else
    match expand_iri ac k vocab with
    | Some iri -> if iri = "@none" then None else Some iri
    | None -> None

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
// @index is dropped (metadata only — matches Parser.JSONLD's own
// keyword-skip for a node object's OWN "@index" member); @reverse expands
// its inline block (expand_reverse_block_fields); @included / @nest (and
// any other unrecognized keyword) are OUT of scope and fail the whole
// node; an ordinary term/compact-IRI/absolute-IRI key is resolved via
// expand_iri and, when it resolves to a keyword (a keyword ALIAS term),
// re-dispatched as that keyword — UNLESS its term definition carries
// "@reverse" (used forward), in which case it folds into an ("@reverse",
// ...) output field instead of a plain property (expand_reverse_property).
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
  else if key = "@reverse" then
    (match value with
     | JObject rfields ->
       (match expand_reverse_block_fields ac rfields (fuel - 1) with
        | None -> None
        | Some entries -> Some (Some ("@reverse", JObject entries)))
     | _ -> None)
  else if key = "@index" then Some None
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
            if td.td_reverse
            then expand_reverse_property ac (Some td) prop_iri value (fuel - 1)
            else expand_ordinary_property ac (Some td) prop_iri value (fuel - 1)
          | None -> expand_ordinary_property ac None prop_iri value (fuel - 1)))

// A property whose key already resolved to an absolute IRI (prop_iri) and
// whose term definition (if any) supplies @type coercion / @language
// override / @container mapping.
and expand_ordinary_property (ac:active_context) (term_opt:option term_def) (prop_iri:string)
                              (value:json_val) (fuel:nat)
  : Tot (option (option (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else
    let is_list = (match term_opt with Some td -> ck_is_list td.td_container | None -> false) in
    (match expand_property_items ac term_opt value (fuel - 1) with
     | None -> None
     | Some items ->
       if is_list
       then Some (Some (prop_iri, JArray [JObject [("@list", JArray items)]]))
       else Some (Some (prop_iri, JArray items)))

// A term defined with "@reverse" and used FORWARD (e.g. {"defines":
// {"@reverse": "rdfs:definedBy"}} applied as an ordinary node-object key):
// folds its (possibly container-mapped) values into a single-predicate
// "@reverse" map entry rather than a plain property. @container:@list on
// a reverse term is not exercised by the toRdf suite and is not specially
// wrapped here (expand_property_items still honors @index/@language/
// @id/@type container mappings for reverse terms, matching the suite's
// reverse+@index fixture).
and expand_reverse_property (ac:active_context) (term_opt:option term_def) (prop_iri:string)
                             (value:json_val) (fuel:nat)
  : Tot (option (option (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else
    (match expand_property_items ac term_opt value (fuel - 1) with
     | None -> None
     | Some items -> Some (Some ("@reverse", JObject [(prop_iri, JArray items)])))

// An inline "@reverse": {...} node-object member: every key inside is an
// ORDINARY (forward) term/IRI whose meaning is reversed purely by
// appearing in this block (JSON-LD 1.1 API §8.4.15-ish "Reverse
// Properties"); a key that is itself a keyword, or resolves to one via a
// keyword-alias term, is out of scope here (no reverse-of-a-keyword case
// in the toRdf suite).
and expand_reverse_block_fields (ac:active_context) (fields:list (string & json_val)) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else
    match fields with
    | [] -> Some []
    | (key, value) :: rest ->
      if jldctx_is_keyword key then None
      else
        (match expand_iri ac key true with
         | None -> None
         | Some prop_iri ->
           if jldctx_is_keyword prop_iri then None
           else
             let term_opt = jldctx_find_term ac.ac_terms key in
             (match expand_property_items ac term_opt value (fuel - 1) with
              | None -> None
              | Some items ->
                (match expand_reverse_block_fields ac rest (fuel - 1) with
                 | None -> None
                 | Some restout -> Some ((prop_iri, JArray items) :: restout))))

// The item list for one property's value, honoring the term's container
// mapping (if any): @index/@language/@id/@type containers apply ONLY
// when the actual value is a JSON object (a term whose value happens to
// be a plain array falls back to ordinary array processing, per spec —
// e.g. toRdf/e040's "indexes" term declares @container:@index but is
// given a bare array). @list containers are handled by the (single,
// non-map) caller, not here — this always returns the flat item list.
and expand_property_items (ac:active_context) (term_opt:option term_def) (value:json_val) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    let type_map = (match term_opt with Some td -> td.td_type_mapping | None -> None) in
    let lang_ovr = (match term_opt with Some td -> td.td_language | None -> None) in
    let ck = (match term_opt with Some td -> td.td_container | None -> CK_None) in
    match ck, value with
    | CK_Index, JObject entries ->
      expand_property ac type_map lang_ovr (jexp_flatten_map_entries entries) (fuel - 1)
    | CK_Language, JObject entries -> Some (jexp_expand_language_map entries)
    | CK_Id, JObject entries -> jexp_expand_id_map ac entries (fuel - 1)
    | CK_Type, JObject entries -> jexp_expand_type_map ac entries (fuel - 1)
    | _, _ -> expand_property ac type_map lang_ovr (jexp_as_array value) (fuel - 1)

// @id containers: each entry's value expands as an ordinary item (@id
// coercion is meaningless here — the map handles subject identity itself
// — so type_map/lang_ovr are None), then the map key (IRI-expanded
// document-relative, i.e. vocab:false, matching @id's own expansion mode)
// is set as its "@id" UNLESS the key is "@none" or the item already
// carries an explicit "@id".
and jexp_expand_id_map (ac:active_context) (entries:list (string & json_val)) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match entries with
    | [] -> Some []
    | (k, v) :: rest ->
      (match expand_item ac None None v (fuel - 1) with
       | None -> None
       | Some None -> jexp_expand_id_map ac rest (fuel - 1)
       | Some (Some item) ->
         let item1 =
           (match jexp_map_key_iri ac k false with
            | None -> item
            | Some iri -> jexp_set_id_if_absent iri item) in
         (match jexp_expand_id_map ac rest (fuel - 1) with
          | None -> None
          | Some restout -> Some (item1 :: restout)))

// @type containers: each entry's value expands with @id coercion (so a
// bare string becomes a node reference, matching toRdf/m017's "foo":
// {"bar": "baz"} — value "baz" is a plain string, expected to become a
// node reference typed rdf:bar), then the map key (vocab-relative, i.e.
// vocab:true, matching @type's own expansion mode) is added as an extra
// "@type" entry UNLESS the key is "@none".
and jexp_expand_type_map (ac:active_context) (entries:list (string & json_val)) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match entries with
    | [] -> Some []
    | (k, v) :: rest ->
      (match expand_item ac (Some "@id") None v (fuel - 1) with
       | None -> None
       | Some None -> jexp_expand_type_map ac rest (fuel - 1)
       | Some (Some item) ->
         let item1 =
           (match jexp_map_key_iri ac k true with
            | None -> item
            | Some kiri -> jexp_add_type_to_item kiri item) in
         (match jexp_expand_type_map ac rest (fuel - 1) with
          | None -> None
          | Some restout -> Some (item1 :: restout)))

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
  let fuel = op_Multiply 3 (json_size doc) + 32 in
  match doc with
  | JObject _ ->
    (match expand_node ac doc fuel with
     | None -> None
     | Some (JObject []) -> Some (JArray [])
     | Some nodeobj -> Some (JArray [nodeobj]))
  | JArray items -> Some (JArray (expand_graph_items ac items fuel))
  | _ -> None
