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
//   - PHASE 5 @included: a node object's "@included" member (or a term
//     whose mapping resolves to that keyword, e.g. toRdf/in03 — routed
//     through expand_aliased_field exactly like a "@nest" alias) is
//     expanded EXACTLY like "@graph" (expand_graph_items: each entry is
//     a full node object, non-conforming entries dropped) but keeps the
//     "@included" key in the output rather than becoming a fresh named
//     graph — Parser.JSONLD's PHASE 5 update folds its contents into the
//     ENCLOSING graph (not a new one) with no linking triple to the
//     enclosing node, see that module's banner. Multiple "@included"
//     occurrences on one node object (the literal keyword plus one or
//     more aliasing terms, toRdf/in03) each produce their own output
//     field entry — expand_fields_list already merges every field-list
//     entry regardless of key repetition (established by @reverse), so
//     no extra fold step is needed here either.
//
// OUT of scope for PHASE 4/5 — expand returns None (a document that
// needs one of these stays an honest FAIL rather than silently-wrong
// RDF):
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

// True when EVERY member of a node object's field list is "@graph" (the
// document-wrapper shape: {"@context": ..., "@graph": [...]}, whose
// "@graph" contents belong to the DEFAULT graph, not a fresh named graph
// — mirrors Parser.JSONLD.jld_only_graph_keys, duplicated here rather
// than imported since Parser.JSONLD depends on THIS module, not the
// other way around. See `expand`'s JObject case below for why this
// matters: expand_node always produces a single node object, so without
// this check a top-level "{"@graph": [...]}" document — after @context
// extraction leaves exactly that one "@graph" field — would get wrapped
// as `JArray [{"@graph": [...]}]` and Parser.JSONLD's jld_expand_top
// would (correctly, per ITS OWN contract) treat that as a NAMED graph,
// not the default-graph wrapper it actually is (toRdf's "IRI Resolution"
// battery and several other @graph-at-top-level fixtures showed this as
// a spurious extra graph-name column on every triple).
let rec jexp_only_graph_keys (fields:list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: rest -> k = "@graph" && jexp_only_graph_keys rest

// Flatten every "@graph"-keyed field's (array-wrapped) value into one
// item list — used only when jexp_only_graph_keys holds, so `fields`
// consists solely of "@graph" entries.
let rec jexp_collect_graph_values (fields:list (string & json_val)) : Tot (list json_val) (decreases fields) =
  match fields with
  | [] -> []
  | (_, v) :: rest -> List.Tot.append (jexp_as_array v) (jexp_collect_graph_values rest)

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
// out @value / @language / @type / @direction, expanding a compact-IRI
// @type via the active context. @direction, like @language, is
// orthogonal to @type (a typed value carries no direction — the two are
// mutually exclusive, same JSON-LD 1.1 API "value expansion" rule as
// @language+@type) but MAY coexist with @language (toRdf/di02's
// "german_ltr" case: {"@value": ..., "@language": "de", "@direction":
// "ltr"}). An invalid (non-"ltr"/"rtl") @direction is a hard failure —
// mirrors JSONLD.Context's context/term-level "@direction" validation
// (toRdf/di08's illegal-value negative test) — but see this module's
// banner: WHAT the emitted direction lexically becomes at the RDF layer
// (dropped / i18n-datatype / compound-literal) is Parser.JSONLD's
// rdfDirection-option concern, not this function's; here direction is
// just another expanded-form field to carry forward.
// The keys a value object may carry (JSON-LD 1.1 §9.5 / API Expansion's
// "invalid value object" error, toRdf/er37: an extra "@id" fails).
let rec jexp_value_object_keys_valid (fields:list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: rest ->
    (k = "@value" || k = "@language" || k = "@type" || k = "@direction" || k = "@index")
    && jexp_value_object_keys_valid rest

let jexp_expand_value_object (ac:active_context) (fields:list (string & json_val))
  : option json_val =
  match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@value") fields with
  | None -> None
  | Some (_, v) ->
    // Validation battery (toRdf/er29-er31, er37, er39, er40, er54):
    // only the five value-object keys allowed; @index must be a string;
    // @language must be a string (or null); @type must be a SINGLE
    // string and not a blank-node label; a structured (array/object)
    // @value only under @type: @json; @language only on a string @value.
    if not (jexp_value_object_keys_valid fields) then None
    else if (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@index") fields with
             | Some (_, JString _) -> false | Some _ -> true | None -> false) then None
    else if (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@language") fields with
             | Some (_, JString _) -> false | Some (_, JNull) -> false | Some _ -> true | None -> false) then None
    else if (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@type") fields with
             | Some (_, JString _) -> false | Some _ -> true | None -> false) then None
    else
      let lang = (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@language") fields with
                  | Some (_, JString s) -> Some s | _ -> None) in
      let typ = (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@type") fields with
                 | Some (_, JString s) -> Some s | _ -> None) in
      // A blank-node @type on a value object is an "invalid typed
      // value" (toRdf/er40); a structured @value needs @type: @json
      // (toRdf/er29: without it, "invalid value object value"); a
      // language-tagged @value must be a string (toRdf/er39).
      if (match typ with Some t -> fs_byte_length t >= 2 && jbyte_at t 0 = 0x5F && jbyte_at t 1 = 0x3A | None -> false) then None
      else if (match v with JArray _ | JObject _ -> typ <> Some "@json" | _ -> false) then None
      else if Some? lang && (match v with JString _ -> false | JNull -> false | _ -> true) then None
      else
      // Some None: "@direction" absent; Some (Some d): a valid ("ltr"/
      // "rtl") @direction value; None: "@direction" present but invalid
      // (non-string, or a string that isn't "ltr"/"rtl" — JNull IS
      // valid, meaning "explicitly no direction", handled as Some None).
      let dir : option (option string) =
        (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@direction") fields with
         | None -> Some None
         | Some (_, JNull) -> Some None
         | Some (_, JString d) -> if d = "ltr" || d = "rtl" then Some (Some d) else None
         | Some _ -> None) in
      (match dir, typ with
       | None, _ -> None
       | Some (Some d), _ ->
         if Some? typ then None
         else
           (match lang with
            | Some lg -> Some (JObject [("@value", v); ("@language", JString lg); ("@direction", JString d)])
            | None -> Some (JObject [("@value", v); ("@direction", JString d)]))
       | Some None, _ ->
         (match (lang, typ) with
          | (Some _, Some _) -> None
          | (Some lg, None) -> Some (JObject [("@value", v); ("@language", JString lg)])
          | (None, Some t) ->
            (match expand_iri ac t true with
             | None -> None
             | Some iri -> Some (JObject [("@value", v); ("@type", JString iri)]))
          | (None, None) -> Some (JObject [("@value", v)])))

// Split a node object's members into its (at most one) @context value and
// the rest, so the caller can re-run context_process before expanding the
// remaining members.
let jexp_extract_context (fields:list (string & json_val))
  : (option json_val & list (string & json_val)) =
  let ctxval = (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@context") fields with
                | Some (_, v) -> Some v | None -> None) in
  let rest = List.Tot.filter (fun (kv:(string & json_val)) -> fst kv <> "@context") fields in
  (ctxval, rest)

// A node object's @type value must be a string or array of strings
// (JSON-LD 1.1 API Expansion's "invalid type value", toRdf/er28:
// "@type": true fails the document). Checked by expand_one_field's
// @type branch before jexp_expand_type_items' lenient per-entry
// expansion below.
let rec jexp_type_entries_all_strings (items:list json_val) : Tot bool (decreases items) =
  match items with
  | [] -> true
  | JString _ :: rest -> jexp_type_entries_all_strings rest
  | _ -> false

// Every produced reverse-property item must be a node object/reference —
// a value object or list object in reverse position is an "invalid
// reverse property value" (toRdf/er34: a bare string under an inline
// @reverse block; er36: a @list under a reverse term).
let rec jexp_items_all_node_like (items:list json_val) : Tot bool (decreases items) =
  match items with
  | [] -> true
  | JObject fields :: rest ->
    not (jexp_has_field "@value" fields) && not (jexp_has_field "@list" fields)
    && jexp_items_all_node_like rest
  | _ -> false

// A language map's entry values must be strings (or null / arrays of
// strings) — anything else is an "invalid language map value"
// (toRdf/er35: "en": true).
let rec jexp_language_entry_values_valid (items:list json_val) : Tot bool (decreases items) =
  match items with
  | [] -> true
  | JString _ :: rest -> jexp_language_entry_values_valid rest
  | JNull :: rest -> jexp_language_entry_values_valid rest
  | _ -> false

let rec jexp_language_map_valid (entries:list (string & json_val)) : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | (_, v) :: rest -> jexp_language_entry_values_valid (jexp_as_array v) && jexp_language_map_valid rest

// A list object may carry only @list and @index (JSON-LD 1.1 API
// Expansion's "invalid set or list object", toRdf/er41: an extra @id).
let rec jexp_list_object_keys_valid (fields:list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: rest -> (k = "@list" || k = "@index") && jexp_list_object_keys_valid rest

// @type values: vocab-relative IRI expansion of every string entry, with
// DOCUMENT-relative fallback (the Expansion algorithm expands @type with
// both vocab and documentRelative true — toRdf/e059: after "@vocab":
// null resets the vocab mapping, "@type": "document-relative" still
// resolves against @base). Remaining non-conforming entries (non-string
// already rejected by expand_one_field's er28 check; unresolvable) are
// dropped, mirroring Parser.JSONLD.jld_type_prepend's leniency.
let rec jexp_expand_type_items (ac:active_context) (items:list json_val)
  : Tot (list json_val) (decreases items) =
  match items with
  | [] -> []
  | JString t :: rest ->
    (match expand_iri ac t true with
     | Some iri -> JString iri :: jexp_expand_type_items ac rest
     | None ->
       (match expand_iri ac t false with
        | Some iri -> JString iri :: jexp_expand_type_items ac rest
        | None -> jexp_expand_type_items ac rest))
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
// resolved IRI to apply. The @none-ALIAS check always expands
// VOCAB-relative (term lookup applies) even when the key IRI itself
// expands document-relative (vocab=false, @id maps) — expand_iri's
// term-substitution is vocab-gated (toRdf/e048), so without the
// separate vocab=true probe an aliased @none key ("none": "@none")
// in an @id map would base-resolve into a spurious graph/id name
// (toRdf's "id map with @none" / "graph id index map with aliased
// @none").
let jexp_map_key_iri (ac:active_context) (k:string) (vocab:bool) : option string =
  if k = "@none" then None
  else
    let none_alias = (match expand_iri ac k true with
                      | Some i -> i = "@none"
                      | None -> false) in
    if none_alias then None
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

// Property-valued index post-processing (td_index, PHASE 7): inject an
// extra (index_iri, [keyval]) field onto ONE already-expanded item —
// merged into its own field list. `keyval` is the map key ALREADY
// coerced per the index property's own term definition (jexp_
// index_key_field, inside the fuel-threaded group below, since it calls
// expand_item). None (a hard failure, not a silent drop) when the target
// item already carries "@value" — JSON-LD 1.1 API's "invalid @index
// value" / "attempting to add a property to a value object" error
// (toRdf/pi01, pi05: a map value with no @type: @id coercion expands to
// a plain literal value object, which cannot receive an extra property).
// Plain structural recursion over an already-produced item list — no
// fuel needed (mirrors jexp_flatten_map_entries above), so this lives
// OUTSIDE the fuel-threaded mutual group below: its callers
// (jexp_expand_property_index_map / _graph_index_map) are IN that
// group, but a call from a fuel-decreasing function to an ordinary
// (non-mutual) structurally-recursive function needs no cross-group
// termination proof.
let jexp_inject_index_field (index_iri:string) (keyval:json_val) (item:json_val) : option json_val =
  match item with
  | JObject fields ->
    if jexp_has_field "@value" fields then None
    else Some (JObject (List.Tot.append fields [(index_iri, JArray [keyval])]))
  | _ -> None

let rec jexp_inject_index_items (index_iri:string) (keyval:json_val) (items:list json_val)
  : Tot (option (list json_val)) (decreases items) =
  match items with
  | [] -> Some []
  | it :: rest ->
    (match jexp_inject_index_field index_iri keyval it with
     | None -> None
     | Some it1 ->
       (match jexp_inject_index_items index_iri keyval rest with
        | None -> None
        | Some restout -> Some (it1 :: restout)))

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
    // toRdf/er28: a non-string @type entry is an "invalid type value".
    (if jexp_type_entries_all_strings (jexp_as_array value)
     then Some (Some [("@type", JArray (expand_type_values ac value))])
     else None)
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
  else if key = "@included" then
    // Unlike @graph's lenient drop-non-conforming policy, an @included
    // entry that is NOT a node object (a bare string, a value object,
    // a list object — the suite's "Error if @included value is ..."
    // negatives) is a spec error ("invalid @included value"), so
    // expansion fails the whole document rather than dropping it —
    // expand_included_items below, not expand_graph_items.
    (match expand_included_items ac (jexp_as_array value) (fuel - 1) with
     | None -> None
     | Some items -> Some (Some [("@included", JArray items)]))
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
  // An ACTUAL keyword not handled above ("@set" as a node key, etc.) is
  // an error; a keyword LOOKALIKE key ("@ignoreMe") is dropped with a
  // warning (toRdf/pr34/pr35/e119); an at-prefixed key WITHOUT keyword
  // form ("@", "@foo.bar") is an ordinary term key and falls through to
  // expand_iri (e119's "allowed" pair).
  else if jldctx_actual_keyword key then None
  else if jldctx_keyword_lookalike key then Some None
  else
    (match expand_iri ac key true with
     | None -> Some None
     | Some prop_iri ->
       let term_opt = jldctx_find_term ac.ac_terms key in
       if jldctx_actual_keyword prop_iri then
         expand_aliased_field ac term_opt prop_iri value (fuel - 1)
       else if jldctx_keyword_form prop_iri then
         // A term whose mapping RESOLVED to a keyword lookalike (can
         // only happen via a prefix/vocab concatenation, since lookalike
         // term definitions are ignored at context-processing time) —
         // dropped, same as a lookalike key.
         Some None
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
       | Some items ->
         // toRdf/er36: a value/list object under a reverse term is an
         // "invalid reverse property value".
         if jexp_items_all_node_like items
         then Some (Some [("@reverse", JObject [(prop_iri, JArray items)])])
         else None)

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
                // toRdf/er34: a bare literal (or any value/list object)
                // inside an inline @reverse block is an "invalid
                // reverse property value".
                if not (jexp_items_all_node_like items) then None
                else
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
    // Same three-way shape as lang_ovr: None = no per-term override (use
    // the active context's ac_direction default), Some None = term
    // explicitly nulls direction, Some (Some d) = term's own direction.
    let dir_ovr = (match term_opt with Some td -> td.td_direction | None -> None) in
    let idx_prop = (match term_opt with Some td -> td.td_index | None -> None) in
    let ck = (match term_opt with Some td -> td.td_container | None -> CK_None) in
    // PHASE 5: a term coerced "@type": "@json" (JSONLD.Context stores
    // this as td_type_mapping = Some "@json" — expand_iri's keyword
    // branch already lets "@json" through unchanged, so no context-side
    // change was needed) turns its ENTIRE raw value — even when that
    // value is itself a JSON array, e.g. toRdf/js07's `[{"foo":"bar"}]`
    // — into ONE value object carrying the value VERBATIM (JSON-LD 1.1
    // API §5(?) Value Expansion's "@json" case: expansion happens BEFORE
    // the ordinary array-flattening rule below would otherwise split an
    // array value into multiple property values). Parser.JSONLD's
    // jld_value_object_to_term does the actual RFC 8785 JCS-subset
    // canonicalization into an rdf:JSON literal — see that function.
    if type_map = Some "@json" then
      Some [JObject [("@value", value); ("@type", JString "@json")]]
    else
    match ck, value with
    | CK_Index, JObject entries ->
      (match idx_prop with
       // Property-valued index (a term's own "@index": "<name>" alongside
       // "@container": "@index" — see td_index's doc comment): each map
       // entry's key becomes an EXTRA triple on every item it produces
       // (jexp_expand_property_index_map), instead of being dropped as
       // pure metadata.
       | Some name -> jexp_expand_property_index_map ac name type_map lang_ovr dir_ovr entries (fuel - 1)
       | None -> expand_property ac type_map lang_ovr dir_ovr (jexp_flatten_map_entries entries) (fuel - 1))
    | CK_Language, JObject entries ->
      // toRdf/er35: a non-string entry value in a language map is an
      // "invalid language map value".
      if jexp_language_map_valid entries then Some (jexp_expand_language_map entries) else None
    | CK_Id, JObject entries -> jexp_expand_id_map ac entries (fuel - 1)
    | CK_Type, JObject entries -> jexp_expand_type_map ac entries (fuel - 1)
    | CK_Graph, _ -> Some (expand_graph_container_items ac (jexp_as_array value) (fuel - 1))
    | CK_GraphIndex, JObject entries ->
      (match idx_prop with
       | Some name -> jexp_expand_graph_index_map ac name entries (fuel - 1)
       | None -> Some (expand_graph_container_items ac (jexp_flatten_map_entries entries) (fuel - 1)))
    | CK_GraphIndex, _ -> Some (expand_graph_container_items ac (jexp_as_array value) (fuel - 1))
    | CK_GraphId, JObject entries -> Some (expand_graph_id_map ac entries (fuel - 1))
    | CK_GraphId, _ -> Some (expand_graph_container_items ac (jexp_as_array value) (fuel - 1))
    | _, _ -> expand_property ac type_map lang_ovr dir_ovr (jexp_as_array value) (fuel - 1)

// Resolve a property-valued index's map KEY into (the index property's
// own IRI, the key coerced exactly as an ordinary use of that property
// would coerce a bare string value — toRdf/pi08-pi09: the active context
// may separately define e.g. "prop": {"@type": "@vocab"}, which must
// turn the map key into a node reference, not a plain string literal).
// None: the index name doesn't resolve, resolves to a keyword (can't
// name a property), or the coercion itself fails.
and jexp_index_key_field (ac:active_context) (index_name:string) (k:string) (fuel:nat)
  : Tot (option (string & json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match expand_iri ac index_name true with
    | None -> None
    | Some index_iri ->
      if jldctx_is_keyword index_iri then None
      else
        let term_opt2 = jldctx_find_term ac.ac_terms index_name in
        let type_map2 = (match term_opt2 with Some td -> td.td_type_mapping | None -> None) in
        let lang_ovr2 = (match term_opt2 with Some td -> td.td_language | None -> None) in
        let dir_ovr2 = (match term_opt2 with Some td -> td.td_direction | None -> None) in
        (match expand_item ac type_map2 lang_ovr2 dir_ovr2 (JString k) (fuel - 1) with
         | None -> None
         | Some None -> None
         | Some (Some kv) -> Some (index_iri, kv))

// @index containers with a property-valued index (td_index): unlike the
// plain @index case (jexp_flatten_map_entries, which discards the map
// key entirely as metadata), each entry's key is kept and injected as an
// extra property onto every item that entry's value expands to — UNLESS
// the key is the literal "@none" (toRdf/pi10: no property added for that
// entry). None (hard failure) when the coercion (jexp_index_key_field)
// or the injection itself (jexp_inject_index_items — toRdf/pi01, pi05: a
// non-@type:@id-coerced map value expands to a plain literal, which
// cannot receive an extra property) fails.
and jexp_expand_property_index_map (ac:active_context) (index_name:string)
                                    (type_map:option string) (lang_ovr:option (option string))
                                    (dir_ovr:option (option string))
                                    (entries:list (string & json_val)) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match entries with
    | [] -> Some []
    | (k, v) :: rest ->
      (match expand_property ac type_map lang_ovr dir_ovr (jexp_as_array v) (fuel - 1) with
       | None -> None
       | Some items ->
         (match jexp_expand_property_index_map ac index_name type_map lang_ovr dir_ovr rest (fuel - 1) with
          | None -> None
          | Some restout ->
            if k = "@none" then Some (List.Tot.append items restout)
            else
              (match jexp_index_key_field ac index_name k (fuel - 1) with
               | None -> None
               | Some (index_iri, keyval) ->
                 (match jexp_inject_index_items index_iri keyval items with
                  | None -> None
                  | Some items1 -> Some (List.Tot.append items1 restout)))))

// "@graph"+"@index" containers with a property-valued index (toRdf/pi11):
// each entry's values are wrapped as graph objects exactly like the
// plain CK_GraphIndex case (expand_graph_container_items), then the
// index property is injected onto each WRAPPER object (the graph-object
// itself, not its contents — the wrapper is what carries the graph's own
// "@id"/other properties in the enclosing graph, see this module's
// banner on graph containers), UNLESS the key is "@none".
and jexp_expand_graph_index_map (ac:active_context) (index_name:string)
                                 (entries:list (string & json_val)) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match entries with
    | [] -> Some []
    | (k, v) :: rest ->
      let items = expand_graph_container_items ac (jexp_as_array v) (fuel - 1) in
      (match jexp_expand_graph_index_map ac index_name rest (fuel - 1) with
       | None -> None
       | Some restout ->
         if k = "@none" then Some (List.Tot.append items restout)
         else
           (match jexp_index_key_field ac index_name k (fuel - 1) with
            | None -> None
            | Some (index_iri, keyval) ->
              (match jexp_inject_index_items index_iri keyval items with
               | None -> None
               | Some items1 -> Some (List.Tot.append items1 restout))))

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
      (match expand_item ac None None None v (fuel - 1) with
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
      (match expand_item ac (Some "@id") None None v (fuel - 1) with
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
                     (dir_ovr:option (option string)) (items:list json_val) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | v :: rest ->
      (match expand_item ac type_map lang_ovr dir_ovr v (fuel - 1) with
       | None -> None
       | Some None -> expand_property ac type_map lang_ovr dir_ovr rest (fuel - 1)
       | Some (Some one) ->
         (match expand_property ac type_map lang_ovr dir_ovr rest (fuel - 1) with
          | None -> None
          | Some restout -> Some (one :: restout)))

// One property value: an explicit value object ({"@value": ...}), a list
// object ({"@list": [...]}), a nested node object, a node reference, or a
// bare scalar coerced per type_map / lang_ovr / dir_ovr. JSON null
// produces nothing (Some None); @reverse inside a property value is OUT
// of scope.
and expand_item (ac:active_context) (type_map:option string) (lang_ovr:option (option string))
                (dir_ovr:option (option string)) (v:json_val) (fuel:nat)
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
        // toRdf/er41: a list object carrying anything besides @list and
        // @index is an "invalid set or list object".
        (if not (jexp_list_object_keys_valid fields) then None
         else
         match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@list") fields with
         | None -> None
         | Some (_, lstval) ->
           (match expand_property ac type_map lang_ovr dir_ovr (jexp_as_array lstval) (fuel - 1) with
            | None -> None
            | Some items -> Some (Some (JObject [("@list", JArray items)]))))
      else if jexp_has_field "@reverse" fields then None
      else if jexp_has_field "@language" fields then
        // toRdf/e008's "drop-lang-only" case: an object carrying
        // "@language" but NO "@value" (already checked above) expands
        // to a value object whose only member is @language, which the
        // Expansion algorithm drops entirely — @language cannot appear
        // on a node object, so this is unambiguous.
        Some None
      else
        (match expand_node ac v (fuel - 1) with
         | None -> None
         | Some nodeobj -> Some (Some nodeobj))
    | JString s ->
      (match type_map with
       | None ->
         let eff_lang = (match lang_ovr with Some l -> l | None -> ac.ac_language) in
         let eff_dir = (match dir_ovr with Some d -> d | None -> ac.ac_direction) in
         let base_fields = ("@value", JString s) ::
           (match eff_lang with Some lg -> [("@language", JString lg)] | None -> []) in
         (match eff_dir with
          | Some d -> Some (Some (JObject (List.Tot.append base_fields [("@direction", JString d)])))
          | None -> Some (Some (JObject base_fields)))
       | Some dt ->
         if dt = "@id" then
           (match expand_iri ac s false with
            | None -> Some None
            | Some iri -> Some (Some (JObject [("@id", JString iri)])))
         else if dt = "@vocab" then
           // @vocab coercion falls back document-relative (the spec's
           // vocab=true + documentRelative=true pairing — toRdf/e057: a
           // value that is neither a term nor vocab-resolvable still
           // resolves against @base).
           (match expand_iri ac s true with
            | Some iri -> Some (Some (JObject [("@id", JString iri)]))
            | None ->
              (match expand_iri ac s false with
               | Some iri -> Some (Some (JObject [("@id", JString iri)]))
               | None -> Some None))
         else
           Some (Some (JObject [("@value", JString s); ("@type", JString dt)])))
    | JBool _ -> Some (Some (jexp_wrap_scalar type_map v))
    | JNumber _ -> Some (Some (jexp_wrap_scalar type_map v))
    | JArray _ -> None

// The contents of a @graph array (or a top-level array of node objects):
// each entry is expanded as a node object; a malformed entry is dropped
// rather than failing the whole graph, matching the leniency already
// established at every other level of this pipeline. FREE-FLOATING
// entries (toRdf/e045/e047: a bare scalar, a value object, a list
// object — none can produce triples with no enclosing property) are
// dropped; an "@set" object at this level is transparent, its contents
// spliced in as entries of THIS level (e047's set of free-floating
// strings + node objects).
and expand_graph_items (ac:active_context) (items:list json_val) (fuel:nat)
  : Tot (list json_val) (decreases fuel) =
  if fuel = 0 then []
  else
    match items with
    | [] -> []
    | JObject fields :: rest ->
      if jexp_has_field "@value" fields || jexp_has_field "@list" fields then
        expand_graph_items ac rest (fuel - 1)
      else
        (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@set") fields with
         | Some (_, setval) ->
           List.Tot.append (expand_graph_items ac (jexp_as_array setval) (fuel - 1))
                            (expand_graph_items ac rest (fuel - 1))
         | None ->
           (match expand_node ac (JObject fields) (fuel - 1) with
            | None -> expand_graph_items ac rest (fuel - 1)
            | Some nodeobj -> nodeobj :: expand_graph_items ac rest (fuel - 1)))
    | _ :: rest -> expand_graph_items ac rest (fuel - 1)

// PHASE 5 @included contents: STRICT, unlike expand_graph_items — every
// entry must be a node object (JSON-LD 1.1 API Expansion, the @included
// case's "invalid @included value" error: not a string, not a value
// object carrying "@value", not a list object carrying "@list"), and a
// node-object entry that fails to expand fails the whole document.
and expand_included_items (ac:active_context) (items:list json_val) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | JObject fields :: rest ->
      if jexp_has_field "@value" fields || jexp_has_field "@list" fields then None
      else
        (match expand_node ac (JObject fields) (fuel - 1) with
         | None -> None
         | Some nodeobj ->
           (match expand_included_items ac rest (fuel - 1) with
            | None -> None
            | Some restout -> Some (nodeobj :: restout)))
    | _ -> None

// PHASE 6 (issue #275): the TOP-LEVEL document array, unlike a nested
// "@graph" member's contents (expand_graph_items, still lenient — a
// non-conforming entry there is dropped per spec), is STRICT: a
// top-level entry whose OWN context processing fails (a remote
// context that can't be loaded, an invalid remote context, an
// "@import" cycle, ...) must fail the WHOLE document, not silently
// vanish from the output. Silently dropping it would turn a
// NegativeEvaluationTest expecting "loading remote context failed"
// into a spuriously-passing EMPTY dataset (toRdf/er05: a one-element
// top-level array whose sole entry has an invalid remote context).
// Mirrors expand_included_items' strict shape (no @value/@list
// special-casing needed here: a malformed top-level entry simply
// fails expand_node on its own terms).
and expand_top_items (ac:active_context) (items:list json_val) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | JObject fields :: rest ->
      // Free-floating value/list objects at the top level produce no
      // RDF and are dropped (toRdf/e045's sibling shapes); everything
      // else stays STRICT per the banner above.
      if jexp_has_field "@value" fields || jexp_has_field "@list" fields then
        expand_top_items ac rest (fuel - 1)
      else
        (match expand_node ac (JObject fields) (fuel - 1) with
         | None -> None
         | Some nodeobj ->
           (match expand_top_items ac rest (fuel - 1) with
            | None -> None
            | Some restout -> Some (nodeobj :: restout)))
    | _ :: rest ->
      // A bare scalar at the top level is free-floating: dropped.
      expand_top_items ac rest (fuel - 1)

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
  | JObject fields0 ->
    // A top-level value or list object is free-floating (toRdf/e045:
    // {"@value": "free-floating value"} -> empty dataset), checked on
    // the RAW field list (a value object cannot carry @context, so no
    // extraction needed first).
    if jexp_has_field "@value" fields0 || jexp_has_field "@list" fields0 then Some (JArray [])
    else
    (match expand_node ac doc fuel with
     | None -> None
     | Some (JObject []) -> Some (JArray [])
     | Some (JObject fields1) ->
       if jexp_only_graph_keys fields1
       then Some (JArray (jexp_collect_graph_values fields1))
       else Some (JArray [JObject fields1])
     | Some nodeobj -> Some (JArray [nodeobj]))
  | JArray items ->
    (match expand_top_items ac items fuel with
     | None -> None
     | Some outs -> Some (JArray outs))
  | _ -> None
