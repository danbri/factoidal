module JSONLD.Expand

// ============================================================================
// JSON-LD 1.1 Expansion — PHASE 3a + PHASE 3b (@reverse, map-shaped
// containers) + PHASE 4 (property-scoped / type-scoped contexts,
// @propagate, @nest, graph containers).
//
// Produces EXPANDED-FORM json_val trees (node objects keyed by absolute
// IRI / keyword, property values array-wrapped, value objects using
// "@value") from compact-or-mixed-form input plus an active context
// (JSONLD.Context). The output feeds Parser.JSONLD's existing jld_*
// pipeline — see that module's banner for exactly what shape it expects
// and how it interprets it (PHASE 4 extends that pipeline too, for
// nested "@graph" consumption — the two banners describe matching halves
// of one feature).
//
// Scope (see docs/designissues/2026-07-04-jsonld-program-lessons.md and
// JSONLD.Context's banner for the context-processing half of the cut):
//   - node objects: term / compact-IRI keys -> absolute IRI keys; @id
//     resolution (document-relative expand_iri, full RFC 3986 against
//     @base); @type (string or array, vocab-relative); nested node
//     objects in property position; a node object's own inline @context
//     (re-processed via JSONLD.Context.apply_context_with_propagate,
//     scoping to that object and its descendants);
//   - value objects: bare scalars wrapped per the term's @type coercion
//     (@id / @vocab / a datatype IRI) and @language (term override or the
//     context default), plus already-compact value objects
//     ({"@value": ..., "@type": "xsd:integer"});
//   - @list: both the explicit {"@list": [...]} shape and a term's
//     "@container": "@list" mapping;
//   - @graph: recursively expanded, passed through as a keyword (Phase 1
//     jld_* already understands @graph at the top level and, via
//     jld_expand_top, at one level of "@id" + "@graph" nesting; PHASE 4's
//     Parser.JSONLD update understands it at ANY nesting depth, which is
//     what graph containers below rely on);
//   - @reverse (3b): a term whose definition carries "@reverse" (used
//     FORWARD, e.g. {"defines": {"@reverse": "rdfs:definedBy"}}) folds its
//     value into an ("@reverse", {predIri: [...]}) output field instead of
//     a plain property; an inline "@reverse": {...} node-object member
//     expands each of ITS keys as an ordinary (forward) term/IRI and
//     folds them the same way;
//   - map-shaped containers (3b): a term's "@container": "@index" /
//     "@language" / "@id" / "@type" flattens a JSON-object VALUE into an
//     item list, using the map key as, respectively: dropped metadata, a
//     "@language" tag (or none for the "@none" key), the item's "@id"
//     (unless already present, or the key is "@none"), or an added
//     "@type" entry (unless the key is "@none"). A term whose ACTUAL
//     value is not a JSON object falls back to plain array processing;
//   - PHASE 4 property-scoped / type-scoped contexts: a term whose
//     definition carries an "@context" member (JSONLD.Context.term_def's
//     td_scoped_context) applies that context — via
//     apply_property_scoped_context below (default propagate TRUE) — to
//     build the active context used for expanding THAT PROPERTY's value
//     (ordinary properties: expand_ordinary_property /
//     expand_reverse_property; a keyword-alias term, e.g. an "@nest"
//     alias carrying its own scoped context per toRdf/c037: expand_aliased_field).
//     A node object's @type value(s) apply EACH named type's scoped
//     context in turn — via JSONLD.Context.apply_type_scoped_contexts,
//     called from expand_typed_ac below — default propagate FALSE (the
//     classic property- vs type-scoped @propagate-default asymmetry: see
//     JSONLD.Context's banner and apply_type_scoped_contexts' comment).
//     The "pop back to the pre-scope active context when propagate is
//     false" half of this lives in expand_node: every node object, on
//     entry, first pops ac.ac_previous if the INCOMING active context
//     carries one (set by whichever enclosing scope just applied a
//     non-propagating context), THEN applies its own inline @context (if
//     any) and its own type-scoped contexts on top of that popped base;
//   - PHASE 4 @nest: a "@nest" member (or a term whose mapping resolves
//     to the keyword "@nest", e.g. toRdf/n002) is TRANSPARENT — its
//     value's fields (or, for an array value, per toRdf/n007-n008, every
//     array entry's fields) are expanded exactly as if they were members
//     of the ENCLOSING node object, and merged into its output field
//     list (expand_fields_list appends rather than conses one field per
//     source member, to make this possible — see that function and
//     expand_one_field's "@nest" branch);
//   - PHASE 4 graph containers: a term's "@container" mapping including
//     "@graph" (JSONLD.Context.CK_Graph / CK_GraphId / CK_GraphIndex)
//     wraps each of the term's values in a fresh {"@graph": [<node>]}
//     object (CK_GraphId additionally sets that wrapper's "@id" from the
//     map key; CK_GraphIndex flattens the index map first, DROPPING the
//     index key — toRdf/m013-m014 — same as a plain @index container's
//     key). Parser.JSONLD's PHASE 4 update interprets an "@graph" member
//     found on ANY node object (not just the top level) as introducing a
//     fresh, separate named graph in the dataset.
//
// OUT of scope for PHASE 4 — expand returns None (a document that needs
// one of these stays an honest FAIL rather than silently-wrong RDF):
//   - @included;
//   - @direction (rdf:direction / i18n-datatype literals);
//   - remote contexts (a JString context value — Phase 5 loader);
//   - "@import" as a term-def member, "@prefix";
//   - protecting @base / @vocab / @language themselves (only term
//     definitions are protection-checked — see JSONLD.Context's banner).
//
// FUEL: mutual recursion is bounded by an explicit fuel parameter derived
// from Parser.JSON.json_size, the same shape as Parser.JSONLD's own
// jld_expand_* family. PHASE 4 adds more fuel-consuming hops per node
// (scoped-context application, @nest merge, graph-container wrapping), so
// the constant factor is bumped again (from 3b's *3+32 to *4+48) to keep
// the "if fuel = 0 then None" branches from tripping on real, if deeply
// nested, W3C fixtures (e.g. toRdf/c038's four-deep @nest-aliased scoped
// contexts) — see expand at the bottom.
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
// PHASE 4: scoped-context helpers (no fuel needed — these call
// JSONLD.Context functions, which are themselves fuel-free / structurally
// recursive over the (much smaller) context tree, not the document tree).
// ================================================================

// The term whose key resolved to this property (if any) may carry its own
// scoped ("@context") member — applied here with propagate defaulting to
// TRUE (JSONLD.Context's banner) and override_protected TRUE (a term's
// own scoped context, being scoped to uses of that specific term, is
// always allowed to touch protected terms — toRdf/c012/c019/pr14-16).
let apply_property_scoped_context (ac:active_context) (term_opt:option term_def) : option active_context =
  match term_opt with
  | Some td ->
    (match td.td_scoped_context with
     | Some scoped -> apply_context_with_propagate ac scoped true true
     | None -> Some ac)
  | None -> Some ac

// The RAW (as-written) string entries of a node object's OWN "@type"
// member(s), used to look up type-scoped contexts (JSONLD.Context's
// apply_type_scoped_contexts wants term NAMES, not yet-expanded IRIs).
let rec jexp_raw_type_strings_of_items (items:list json_val) : Tot (list string) (decreases items) =
  match items with
  | [] -> []
  | JString s :: rest -> s :: jexp_raw_type_strings_of_items rest
  | _ :: rest -> jexp_raw_type_strings_of_items rest

let rec jexp_raw_type_strings (fields:list (string & json_val)) : Tot (list string) (decreases fields) =
  match fields with
  | [] -> []
  | (k, v) :: rest ->
    if k = "@type"
    then List.Tot.append (jexp_raw_type_strings_of_items (jexp_as_array v)) (jexp_raw_type_strings rest)
    else jexp_raw_type_strings rest

// Apply every type-scoped context named by this node object's OWN @type
// member(s) (fields1, i.e. AFTER @context extraction but before any
// per-field expansion) on top of ac0 (this node's active context after
// its own inline @context, before any type-scoped modification). A node
// with no @type (or none of its type terms carrying a scoped context)
// leaves ac0 unchanged.
let expand_typed_ac (ac0:active_context) (fields:list (string & json_val)) : option active_context =
  match jexp_raw_type_strings fields with
  | [] -> Some ac0
  | types -> apply_type_scoped_contexts ac0 types

// ================================================================
// Map-shaped container helpers (@index / @language / @id / @type /
// @graph / @graph+@id / @graph+@index).
//
// None of these need the fuel-threaded mutual group below EXCEPT the
// @id/@type/@graph-map variants, which DO need to recurse into node
// objects (their values may be full nested node objects), so those live
// inside the mutual group further down, right next to expand_item /
// expand_node which they call.
// ================================================================

// @index containers (JSON-LD 1.1 API Container Mapping, @index case): the
// map key carries no RDF meaning — only the (possibly array-wrapped)
// values matter, flattened into one item list.
let rec jexp_flatten_map_entries (entries:list (string & json_val))
  : Tot (list json_val) (decreases entries) =
  match entries with
  | [] -> []
  | (_, v) :: rest -> List.Tot.append (jexp_as_array v) (jexp_flatten_map_entries rest)

// @language containers: each map key is a language tag, or "@none" for an
// entry that gets no @language at all. Non-string / null entries are
// dropped, mirroring the leniency elsewhere in this module.
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
// expanded by the caller) into an already-expanded item.
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
// keyword "@none", OR a term/alias whose OWN mapping IS "@none") or the
// resolved IRI to apply.
let jexp_map_key_iri (ac:active_context) (k:string) (vocab:bool) : option string =
  if k = "@none" then None
  else
    match expand_iri ac k vocab with
    | Some iri -> if iri = "@none" then None else Some iri
    | None -> None

// A graph-container value that expands (as an ORDINARY node object) to
// something that ALREADY carries its own "@graph" member (toRdf/e087,
// e101, e106: the map value is itself literally {"@graph": {...}}, not a
// plain node) must NOT be wrapped a second time — JSON-LD 1.1 API's
// Container Mapping @graph case: "if the expanded item is not already a
// graph object, wrap it in one". expand_graph_container_items /
// expand_graph_id_map_one below call this instead of wrapping
// unconditionally.
let jexp_is_graph_object (v:json_val) : bool =
  match v with
  | JObject fields -> jexp_has_field "@graph" fields
  | _ -> false

let jexp_ensure_graph_object (nodeobj:json_val) : json_val =
  if jexp_is_graph_object nodeobj then nodeobj
  else JObject [("@graph", JArray [nodeobj])]

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
//   - option (option (list (string & json_val))) for "expand this node
//     object's ONE member": None = fatal; Some None = drop (JSON null /
//     @index); Some (Some kvs) = zero-or-more output fields (PHASE 4:
//     @nest merges its contents in as MULTIPLE fields, hence a list
//     rather than 3a/3b's single tuple — expand_fields_list appends
//     rather than conses).
// ================================================================

let rec expand_node (ac:active_context) (v:json_val) (fuel:nat)
  : Tot (option json_val) (decreases fuel) =
  if fuel = 0 then None
  else
    // PHASE 4: pop back to the pre-scope active context if the INCOMING ac
    // is the result of a non-propagating context application (a
    // type-scoped context by default, or any scoped/inline context with
    // an explicit "@propagate": false) — see this module's banner and
    // JSONLD.Context.apply_type_scoped_contexts.
    let ac_popped = (match ac.ac_previous with Some prev -> prev | None -> ac) in
    match v with
    | JObject fields ->
      let (ctxval, fields1) = jexp_extract_context fields in
      let ac0_opt =
        (match ctxval with
         | None -> Some ac_popped
         | Some cv -> apply_context_with_propagate ac_popped cv true false) in
      (match ac0_opt with
       | None -> None
       | Some ac0 ->
         (match expand_typed_ac ac0 fields1 with
          | None -> None
          | Some ac_typed ->
            (match expand_fields_list ac_typed fields1 (fuel - 1) with
             | None -> None
             | Some outfields -> Some (JObject outfields))))
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
       | Some (Some outkvs) ->
         (match expand_fields_list ac rest (fuel - 1) with
          | None -> None
          | Some restout -> Some (List.Tot.append outkvs restout)))

// One member of a node object. @id / @type / @graph are handled directly;
// @index is dropped (metadata only); @reverse expands its inline block
// (expand_reverse_block_fields); @nest (PHASE 4) merges its (object- or
// array-of-objects-shaped) value's fields into this node's own output
// field list (expand_nest_array for the array form); @included (and any
// other unrecognized keyword) is OUT of scope and fails the whole node;
// an ordinary term/compact-IRI/absolute-IRI key is resolved via
// expand_iri and, when it resolves to a keyword (a keyword ALIAS term —
// e.g. "@nest" per toRdf/n002/c037), re-dispatched as that keyword
// (expand_aliased_field), first applying that TERM's own property-scoped
// context if it has one (toRdf/c037/c038 tie @nest aliasing to scoped
// contexts) — UNLESS its term definition carries "@reverse" (used
// forward), in which case it folds into an ("@reverse", ...) output field
// instead of a plain property (expand_reverse_property).
and expand_one_field (ac:active_context) (key:string) (value:json_val) (fuel:nat)
  : Tot (option (option (list (string & json_val)))) (decreases fuel) =
  if fuel = 0 then None
  else if key = "@id" then
    (match value with
     | JString s ->
       (match expand_iri ac s false with
        | None -> Some None
        | Some iri -> Some (Some [("@id", JString iri)]))
     | _ -> None)
  else if key = "@type" then
    Some (Some [("@type", JArray (expand_type_values ac value))])
  else if key = "@graph" then
    Some (Some [("@graph", JArray (expand_graph_items ac (jexp_as_array value) (fuel - 1)))])
  else if key = "@reverse" then
    (match value with
     | JObject rfields ->
       (match expand_reverse_block_fields ac rfields (fuel - 1) with
        | None -> None
        | Some entries -> Some (Some [("@reverse", JObject entries)]))
     | _ -> None)
  else if key = "@index" then Some None
  else if key = "@included" then None
  else if key = "@nest" then
    (match value with
     | JObject nfields ->
       (match expand_fields_list ac nfields (fuel - 1) with
        | None -> None
        | Some outs -> Some (Some outs))
     | JArray items ->
       (match expand_nest_array ac items (fuel - 1) with
        | None -> None
        | Some outs -> Some (Some outs))
     | _ -> None)
  else if jldctx_is_keyword key then None
  else
    (match expand_iri ac key true with
     | None -> Some None
     | Some prop_iri ->
       let term_opt = jldctx_find_term ac.ac_terms key in
       if jldctx_is_keyword prop_iri then
         expand_aliased_field ac term_opt prop_iri value (fuel - 1)
       else
         (match term_opt with
          | Some td ->
            if td.td_reverse
            then expand_reverse_property ac (Some td) prop_iri value (fuel - 1)
            else expand_ordinary_property ac (Some td) prop_iri value (fuel - 1)
          | None -> expand_ordinary_property ac None prop_iri value (fuel - 1)))

// PHASE 4: "@nest": [ {...}, {...} ] — every array entry's fields merge
// into the enclosing node object in turn (toRdf/n007/n008); a
// non-object array entry is a malformed @nest value (spec error).
and expand_nest_array (ac:active_context) (items:list json_val) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | JObject nfields :: rest ->
      (match expand_fields_list ac nfields (fuel - 1) with
       | None -> None
       | Some outs ->
         (match expand_nest_array ac rest (fuel - 1) with
          | None -> None
          | Some restouts -> Some (List.Tot.append outs restouts)))
    | _ -> None

// A property whose key already resolved to an absolute IRI (prop_iri) and
// whose term definition (if any) supplies @type coercion / @language
// override / @container mapping / (PHASE 4) a property-scoped @context,
// applied here (default propagate TRUE) before expanding the value.
and expand_ordinary_property (ac:active_context) (term_opt:option term_def) (prop_iri:string)
                              (value:json_val) (fuel:nat)
  : Tot (option (option (list (string & json_val)))) (decreases fuel) =
  if fuel = 0 then None
  else
    match apply_property_scoped_context ac term_opt with
    | None -> None
    | Some ac_eff ->
      let is_list = (match term_opt with Some td -> ck_is_list td.td_container | None -> false) in
      (match expand_property_items ac_eff term_opt value (fuel - 1) with
       | None -> None
       | Some items ->
         if is_list
         then Some (Some [(prop_iri, JArray [JObject [("@list", JArray items)]])])
         else Some (Some [(prop_iri, JArray items)]))

// A term defined with "@reverse" and used FORWARD (e.g. {"defines":
// {"@reverse": "rdfs:definedBy"}} applied as an ordinary node-object key):
// folds its (possibly container-mapped) values into a single-predicate
// "@reverse" map entry rather than a plain property; PHASE 4: also
// applies that term's own property-scoped context first, same as an
// ordinary property.
and expand_reverse_property (ac:active_context) (term_opt:option term_def) (prop_iri:string)
                             (value:json_val) (fuel:nat)
  : Tot (option (option (list (string & json_val)))) (decreases fuel) =
  if fuel = 0 then None
  else
    match apply_property_scoped_context ac term_opt with
    | None -> None
    | Some ac_eff ->
      (match expand_property_items ac_eff term_opt value (fuel - 1) with
       | None -> None
       | Some items -> Some (Some [("@reverse", JObject [(prop_iri, JArray items)])]))

// An inline "@reverse": {...} node-object member: every key inside is an
// ORDINARY (forward) term/IRI whose meaning is reversed purely by
// appearing in this block.
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
// be a plain array falls back to ordinary array processing, per spec).
// PHASE 4: @graph / @graph+@id / @graph+@index containers wrap each
// (possibly map-flattened) value in a fresh {"@graph": [<node>]} object
// — see expand_graph_container_items / expand_graph_id_map below and this
// module's banner. @list containers are handled by the (single, non-map)
// caller, not here — this always returns the flat item list.
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
    | CK_Graph, _ -> Some (expand_graph_container_items ac (jexp_as_array value) (fuel - 1))
    | CK_GraphIndex, JObject entries ->
      Some (expand_graph_container_items ac (jexp_flatten_map_entries entries) (fuel - 1))
    | CK_GraphIndex, _ -> Some (expand_graph_container_items ac (jexp_as_array value) (fuel - 1))
    | CK_GraphId, JObject entries -> Some (expand_graph_id_map ac entries (fuel - 1))
    | CK_GraphId, _ -> Some (expand_graph_container_items ac (jexp_as_array value) (fuel - 1))
    | _, _ -> expand_property ac type_map lang_ovr (jexp_as_array value) (fuel - 1)

// @id containers: each entry's value expands as an ordinary item, then
// the map key is set as its "@id" UNLESS the key is "@none" or the item
// already carries an explicit "@id".
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

// @type containers: each entry's value expands with @id coercion, then
// the map key is added as an extra "@type" entry UNLESS the key is
// "@none".
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

// PHASE 4 graph containers ("@container" includes "@graph"): each value
// item expands as an ordinary NODE object (not a value/list — a graph's
// contents are always nodes), wrapped in a fresh, @id-less
// {"@graph": [<node>]} object. Non-conforming (non-object) entries are
// dropped, matching this module's established leniency elsewhere.
and expand_graph_container_items (ac:active_context) (items:list json_val) (fuel:nat)
  : Tot (list json_val) (decreases fuel) =
  if fuel = 0 then []
  else
    match items with
    | [] -> []
    | v :: rest ->
      (match expand_node ac v (fuel - 1) with
       | None -> expand_graph_container_items ac rest (fuel - 1)
       | Some nodeobj -> jexp_ensure_graph_object nodeobj :: expand_graph_container_items ac rest (fuel - 1))

// "@graph"+"@id" containers (toRdf/e085/e086/m015/m016): the map key
// becomes the WRAPPER's "@id" (the graph's own name), not the inner
// node's — a graph name and its content's subject are independent. A
// map value may itself be array-wrapped (multiple graph objects sharing
// one @id).
and expand_graph_id_map (ac:active_context) (entries:list (string & json_val)) (fuel:nat)
  : Tot (list json_val) (decreases fuel) =
  if fuel = 0 then []
  else
    match entries with
    | [] -> []
    | (k, v) :: rest ->
      List.Tot.append (expand_graph_id_map_one ac k (jexp_as_array v) (fuel - 1))
                       (expand_graph_id_map ac rest (fuel - 1))

and expand_graph_id_map_one (ac:active_context) (k:string) (items:list json_val) (fuel:nat)
  : Tot (list json_val) (decreases fuel) =
  if fuel = 0 then []
  else
    match items with
    | [] -> []
    | v :: rest ->
      (match expand_node ac v (fuel - 1) with
       | None -> expand_graph_id_map_one ac k rest (fuel - 1)
       | Some nodeobj ->
         let graphobj = jexp_ensure_graph_object nodeobj in
         let wrapped =
           (match jexp_map_key_iri ac k false with
            | None -> graphobj
            | Some iri -> jexp_set_id_if_absent iri graphobj) in
         wrapped :: expand_graph_id_map_one ac k rest (fuel - 1))

// A term whose IRI mapping is itself a keyword (e.g. "id": "@id", or
// "nest": "@nest" per toRdf/n002) applies to its value exactly as that
// keyword would. PHASE 4: term_opt carries the ALIASING term's own
// definition, so its property-scoped @context (if any — toRdf/c037/c038
// tie a scoped context to a "@nest"-mapped term) is applied FIRST, same
// as an ordinary property.
and expand_aliased_field (ac:active_context) (term_opt:option term_def) (canon_key:string) (value:json_val) (fuel:nat)
  : Tot (option (option (list (string & json_val)))) (decreases fuel) =
  if fuel = 0 then None
  else
    match apply_property_scoped_context ac term_opt with
    | None -> None
    | Some ac_eff -> expand_one_field ac_eff canon_key value (fuel - 1)

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
  let fuel = op_Multiply 4 (json_size doc) + 48 in
  match doc with
  | JObject _ ->
    (match expand_node ac doc fuel with
     | None -> None
     | Some (JObject []) -> Some (JArray [])
     | Some nodeobj -> Some (JArray [nodeobj]))
  | JArray items -> Some (JArray (expand_graph_items ac items fuel))
  | _ -> None
