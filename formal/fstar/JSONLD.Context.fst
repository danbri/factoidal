module JSONLD.Context

// ============================================================================
// JSON-LD 1.1 Context Processing — PHASE 3a (inline contexts only) + PHASE 3b
// (@reverse term definitions, map-shaped containers, RFC 3986 base
// resolution) + PHASE 4 (property-scoped / type-scoped contexts,
// @propagate, @protected, graph-container container kinds).
//
// Implements a subset of the JSON-LD 1.1 API "Context Processing" algorithm
// (spec section 4 / "Create Term Definition"), restricted to contexts given
// INLINE as a JSON object value or an array of such (no remote-document
// loading yet — see docs/designissues/2026-07-04-jsonld-program-lessons.md,
// phase 4 "Loader assume-val", still a LATER phase despite the shared "4"
// numbering with this file's Phase 4 feature slice — this module's Phase 4
// is docs/designissues/2026-07-04-jsonld-program-lessons.md's phase 3
// continued, not its phase 4 loader work).
//
// Supported here:
//   - simple term definitions: "term": "IRI-or-compact-IRI-or-keyword";
//   - expanded term definitions: "term": { "@id"/"@reverse", "@type",
//     "@container": "@list"/"@set"/"@index"/"@language"/"@id"/"@type"/
//     "@graph" (or an array combining one of those with "@set", or "@graph"
//     with "@id"/"@index"), "@language", "@context" (a SCOPED context,
//     stored raw/unprocessed — see td_scoped_context below — property- or
//     type-scoped application is JSONLD.Expand's job), "@protected";
//   - "@vocab", "@base", "@language", "@version" (accepted; "@base" is
//     resolved against any previous "@base" per RFC 3986 — see
//     jldctx_resolve below — "@version" is otherwise ignored);
//   - "@propagate" (accepted, must be a JSON boolean when present — a
//     context-object member consumed here only for validation; the actual
//     propagate DECISION is made by the caller via jldctx_scan_propagate,
//     since "does this active context persist into nested node objects"
//     is an EXPANSION-time question, not a context-processing one);
//   - "@protected" (both as a context-object-level default applying to
//     every sibling term def per jldctx_scan_bool_key, and as a per-term
//     override): redefining a protected term with a DIFFERENT definition
//     is an honest context_process failure (None) UNLESS the caller passes
//     override_protected = true (property-/type-scoped context application
//     always does, per spec — see JSONLD.Expand.apply_property_scoped_context
//     / apply_type_scoped_contexts); redefining with an IDENTICAL
//     definition is always allowed (term_defs_compatible);
//   - compact-IRI + term-based prefix expansion (expand_iri below);
//   - context reset via JNull, INCLUDING the protected-term-nullification
//     check (a null context that would silently drop a protected term is
//     itself an error unless override_protected is true) and per-term
//     null ("term": null undefines that term, same protection check);
//   - an array of contexts, folded left to right;
//   - RFC 3986 relative-IRI resolution against @base: jldctx_resolve reuses
//     SPARQL11.IRI.Resolve.resolve_iri (a dependency-free-of-SPARQL11.Algebra
//     utility over RDF.Graph.Executable's wf_iri only — importing it here
//     does not invert the semantic-core/pragmatics stratification, since
//     that module has no reverse dependency on JSONLD.*; see
//     skills/fstar-module-style/SKILL.md).
//
// OUT of scope (a document that needs any of these gets an honest None
// from context_process, rather than a silently wrong active context):
//   - remote contexts (a JString context value — Phase 4 loader, the OTHER
//     phase 4, see banner note above);
//   - "@import" / "@nest" as a term-def member / "@prefix";
//   - "@protected" / "@propagate" protecting @base / @vocab / @language
//     themselves (only TERM definitions are protection-checked here — no
//     toRdf fixture in this program's target slice needs vocab/base/
//     language protection, only term protection, per the pr0x fixtures).
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.JSON
open RDF.Graph.Executable
open SPARQL11.IRI.Resolve

// ================================================================
// Types
// ================================================================

// One term's definition. td_iri is either an absolute IRI or a keyword
// (e.g. "@id") when the term is a keyword ALIAS (as in {"id": "@id"}).
// td_type_mapping holds an already-expanded @type coercion target: an
// absolute IRI, or the literal keywords "@id" / "@vocab" for IRI-valued
// coercion (@json / @none are OUT of scope: term defs requesting them are
// rejected in process_term_def_obj below).
// A term's "@container" mapping. CK_None also covers the explicit "@set"
// marker (array-vs-single is already handled uniformly by callers via
// jexp_as_array, so @set needs no distinct representation). CK_List is
// kept as a bool-shaped case for the pre-3b callers that only ever asked
// "is this @list"; 3b adds the four map-shaped containers; PHASE 4 adds
// the three graph-container shapes (CK_Graph covers bare "@graph" and
// "@graph"+"@set", which behave identically since @set only affects
// single-vs-array leniency, already handled uniformly elsewhere).
type container_kind =
  | CK_None
  | CK_List
  | CK_Index
  | CK_Language
  | CK_Id
  | CK_Type
  | CK_Graph
  | CK_GraphId
  | CK_GraphIndex

let ck_is_none (k:container_kind) : bool = match k with | CK_None -> true | _ -> false
let ck_is_list (k:container_kind) : bool = match k with | CK_List -> true | _ -> false

// td_scoped_context: the RAW (unprocessed) "@context" value found inside
// this term's definition object, if any — a property-scoped context when
// the term is used as an ordinary property key, or a type-scoped context
// when the term is used as an @type value. Deferred rather than processed
// here because propagate/override_protected depend on HOW the term is
// used (JSONLD.Expand.apply_property_scoped_context /
// apply_type_scoped_contexts apply it at the point of use).
// td_protected: whether this term definition may NOT be silently replaced
// by a later, different context (JSON-LD 1.1 API "@protected").
type term_def = {
  td_iri            : string;
  td_type_mapping   : option string;
  td_container      : container_kind;
  td_reverse        : bool;
  // None: no per-term override, use the active context's default language.
  // Some None: term explicitly carries no language ("@language": null).
  // Some (Some lg): term explicitly carries language lg.
  td_language       : option (option string);
  td_scoped_context : option json_val;
  td_protected      : bool;
}

// ac_previous: Some ac0 marks THIS active context as the result of a
// NON-PROPAGATING context application (a type-scoped context by default,
// or any scoped/inline context whose "@propagate" member is explicitly
// false) — ac0 is what a NESTED node object should use instead of this
// active context (JSONLD.Expand.expand_node "pops" to it on entry). None
// means this active context propagates normally into nested node objects.
type active_context = {
  ac_terms    : list (string & term_def);
  ac_vocab    : option string;
  ac_base     : option string;
  ac_language : option string;
  ac_previous : option active_context;
}

let empty_active_context : active_context =
  { ac_terms = []; ac_vocab = None; ac_base = None; ac_language = None; ac_previous = None }

// ================================================================
// Small string / list helpers
// ================================================================

// Keywords all start with a commercial-at byte (mirrors
// Parser.JSONLD.jld_is_keyword; duplicated rather than imported since
// Parser.JSONLD must not be a dependency of this module).
let jldctx_is_keyword (s:string) : bool =
  fs_byte_length s > 0 && jbyte_at s 0 = 0x40

let rec jldctx_find_term (terms:list (string & term_def)) (name:string)
  : Tot (option term_def) (decreases terms) =
  match terms with
  | [] -> None
  | (k, td) :: rest -> if k = name then Some td else jldctx_find_term rest name

// True when any term in `terms` is protected — used to reject a context
// reset (JNull) that would silently drop protection.
let rec jldctx_any_protected (terms:list (string & term_def)) : Tot bool (decreases terms) =
  match terms with
  | [] -> false
  | (_, td) :: rest -> td.td_protected || jldctx_any_protected rest

// Remove every occurrence of `name` from a term list (a per-term
// "term": null definition undefines it).
let rec jldctx_remove_term (terms:list (string & term_def)) (name:string)
  : Tot (list (string & term_def)) (decreases terms) =
  match terms with
  | [] -> []
  | (k, td) :: rest ->
    if k = name then jldctx_remove_term rest name
    else (k, td) :: jldctx_remove_term rest name

// Scan a context object's OWN fields (not recursing into nested term-def
// objects) for the last JBool value of `keyname`, or `dflt` if absent /
// non-boolean. Used both for the context-level "@protected" default (see
// context_process_fields) and, by JSONLD.Expand, for "@propagate".
let rec jldctx_scan_bool_key (fields:list (string & json_val)) (keyname:string) (dflt:bool)
  : Tot bool (decreases fields) =
  match fields with
  | [] -> dflt
  | (k, JBool b) :: rest -> if k = keyname then jldctx_scan_bool_key rest keyname b else jldctx_scan_bool_key rest keyname dflt
  | _ :: rest -> jldctx_scan_bool_key rest keyname dflt

// Same scan, but over a whole context VALUE (object, or array of such —
// contexts are folded left to right, so a later array entry's explicit
// value wins, matching context_process_array's own left-to-right fold).
let rec jldctx_scan_propagate (ctx:json_val) (dflt:bool) : Tot bool (decreases ctx) =
  match ctx with
  | JObject fields -> jldctx_scan_bool_key fields "@propagate" dflt
  | JArray items -> jldctx_scan_propagate_items items dflt
  | _ -> dflt

and jldctx_scan_propagate_items (items:list json_val) (dflt:bool) : Tot bool (decreases items) =
  match items with
  | [] -> dflt
  | hd :: tl -> jldctx_scan_propagate_items tl (jldctx_scan_propagate hd dflt)

// Two term definitions are "the same" for protected-redefinition purposes
// when EVERY observable part of the definition is identical (JSON-LD 1.1
// API "Create Term Definition", the protected-term-redefinition check):
// IRI, type coercion, container, reverse-ness, language override, AND the
// term's own scoped context — toRdf/pr26 redefines "Foo" a second time
// with the SAME @id but WITHOUT the first definition's nested scoped
// @context, which must be rejected as an incompatible redefinition (a
// term's scoped context is as much a part of its "mapping" as its IRI).
// td_protected itself is NOT compared: a protected term may be
// re-declared protected-or-not, as long as everything it actually MAPS TO
// stays the same (toRdf/pr23/pr24 redeclare identically, including
// protected-ness; pr08's "scope1"/"scope2" declare fresh, previously
// undefined terms with differing protected-ness, not a redefinition at
// all).
let term_defs_compatible (a b:term_def) : bool =
  a.td_iri = b.td_iri && a.td_type_mapping = b.td_type_mapping &&
  a.td_container = b.td_container && a.td_reverse = b.td_reverse &&
  a.td_language = b.td_language && a.td_scoped_context = b.td_scoped_context

// Guard applied at every term-definition site: a protected existing term
// may only be replaced by an identical definition, UNLESS override_protected
// is set (property-/type-scoped context application always passes true —
// JSONLD.Expand.apply_property_scoped_context / apply_type_scoped_contexts).
let jldctx_check_redefine (ac:active_context) (key:string) (new_td:term_def) (override_protected:bool) : bool =
  match jldctx_find_term ac.ac_terms key with
  | None -> true
  | Some existing ->
    if existing.td_protected && not override_protected
    then term_defs_compatible existing new_td
    else true

// Position of the first colon byte in s, scanning from pos, or None.
let rec jldctx_find_colon (s:string) (pos:nat) (fuel:nat)
  : Tot (option (p:nat{p < fs_byte_length s})) (decreases fuel) =
  if fuel = 0 then None
  else
    let n = fs_byte_length s in
    if pos >= n then None
    else if jbyte_at s pos = 0x3A then Some pos
    else jldctx_find_colon s (pos + 1) (fuel - 1)

// RFC 3986 reference resolution, reusing SPARQL11.IRI.Resolve.resolve_iri
// (which takes a wf_iri base). base here is an ordinary string because
// active_context.ac_base is populated incrementally (see the "@base"
// handling in context_process_one_field below) and F* cannot statically
// know it is well-formed; the runtime is_iri check refines it to wf_iri
// for the call, with a safe fallback to the unresolved base on failure —
// mirrors resolve_iri's own is_iri-checked-result fallback.
let jldctx_resolve (base:string) (relative:string) : string =
  if is_iri base then resolve_iri base relative else base

// IRI Expansion (JSON-LD 1.1 API §5.1), simplified: no local-context /
// forward-reference lookahead (terms are resolved against the ALREADY
// built-up active context, which is enough for the sequential term
// definitions this phase supports). @base-relative values get full RFC
// 3986 resolution (jldctx_resolve); @vocab-relative values stay a plain
// suffix concatenation, matching the spec's vocab-mapping IRI expansion
// (not a reference-resolution against a base).
let jldctx_expand_fallback (ac:active_context) (value:string) (vocab:bool)
  : Tot (option string) =
  if vocab then
    (match ac.ac_vocab with
     | Some v -> Some (String.concat "" [v; value])
     | None -> None)
  else
    (match ac.ac_base with
     | Some b -> Some (jldctx_resolve b value)
     | None -> None)

let expand_iri (ac:active_context) (value:string) (vocab:bool) : Tot (option string) =
  let n = fs_byte_length value in
  if n = 0 then None
  else if jldctx_is_keyword value then Some value
  else
    match jldctx_find_term ac.ac_terms value with
    | Some td -> Some td.td_iri
    | None ->
      (match jldctx_find_colon value 0 (n + 1) with
       | None -> jldctx_expand_fallback ac value vocab
       | Some c ->
         if c = 0 then jldctx_expand_fallback ac value vocab
         else
           let prefix = fs_byte_sub value 0 c in
           if prefix = "_" then Some value
           else if jbyte_at value (c + 1) = 0x2F && jbyte_at value (c + 2) = 0x2F then Some value
           else
             (match jldctx_find_term ac.ac_terms prefix with
              | None -> Some value
              | Some ptd ->
                if jldctx_is_keyword ptd.td_iri then None
                else
                  let suffix = fs_byte_sub value (c + 1) (n - c - 1) in
                  Some (String.concat "" [ptd.td_iri; suffix])))

// ================================================================
// @container value parsing
// ================================================================

// A single "@container" string entry, or None for a non-container keyword.
let jldctx_container_kind_of_string (s:string) : option container_kind =
  if s = "@list" then Some CK_List
  else if s = "@set" then Some CK_None
  else if s = "@index" then Some CK_Index
  else if s = "@language" then Some CK_Language
  else if s = "@id" then Some CK_Id
  else if s = "@type" then Some CK_Type
  else if s = "@graph" then Some CK_Graph
  else None

// An "@container" array (e.g. ["@graph", "@id"]): collect which of the
// combinable flags are present (graph / id / index / language / type /
// set), rejecting any other string, then combine them once at the end
// (jldctx_container_kind_of_flags) — a plain fold-and-keep-first-nonzero
// (3b's approach) cannot express "@graph"+"@id" as a THIRD distinct kind,
// which PHASE 4's graph containers need.
let rec jldctx_container_flags (items:list json_val)
    (has_graph has_id has_index has_lang has_type:bool)
  : Tot (option (bool & bool & bool & bool & bool)) (decreases items) =
  match items with
  | [] -> Some (has_graph, has_id, has_index, has_lang, has_type)
  | JString s :: rest ->
    if s = "@set" then jldctx_container_flags rest has_graph has_id has_index has_lang has_type
    else if s = "@graph" then jldctx_container_flags rest true has_id has_index has_lang has_type
    else if s = "@id" then jldctx_container_flags rest has_graph true has_index has_lang has_type
    else if s = "@index" then jldctx_container_flags rest has_graph has_id true has_lang has_type
    else if s = "@language" then jldctx_container_flags rest has_graph has_id has_index true has_type
    else if s = "@type" then jldctx_container_flags rest has_graph has_id has_index has_lang true
    else None
  | _ -> None

let jldctx_container_kind_of_flags (has_graph has_id has_index has_lang has_type:bool) : option container_kind =
  if has_graph then
    (if has_id then Some CK_GraphId
     else if has_index then Some CK_GraphIndex
     else Some CK_Graph)
  else if has_id then Some CK_Id
  else if has_index then Some CK_Index
  else if has_lang then Some CK_Language
  else if has_type then Some CK_Type
  else Some CK_None

let jldctx_container_kind_of_items (items:list json_val) : option container_kind =
  match jldctx_container_flags items false false false false false with
  | None -> None
  | Some (g, i, ix, lg, ty) -> jldctx_container_kind_of_flags g i ix lg ty

// ================================================================
// Expanded (object-form) term definitions
// ================================================================

// One left-to-right pass over a term-definition object's members,
// threading the (id, reverse, type, container-kind, language, scoped-
// context, protected-override) fields collected so far. None anywhere
// below means an unsupported / malformed member — process_term_def_obj
// turns that into an honest context_process failure rather than a
// silently incomplete term.
let rec jldctx_term_obj_fields
    (ac:active_context)
    (idf:option string) (revf:option string) (typef:option string)
    (contk:container_kind) (langf:option (option string))
    (ctxf:option json_val) (protf:option bool)
    (fields:list (string & json_val))
  : Tot (option (option string & option string & option string & container_kind &
                 option (option string) & option json_val & option bool))
        (decreases fields) =
  match fields with
  | [] -> Some (idf, revf, typef, contk, langf, ctxf, protf)
  | (k, v) :: rest ->
    if k = "@id" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac (Some e) revf typef contk langf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@reverse" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac idf (Some e) typef contk langf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@type" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac idf revf (Some e) contk langf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@container" then
      (match v with
       | JString s ->
         (match jldctx_container_kind_of_string s with
          | Some ck -> jldctx_term_obj_fields ac idf revf typef ck langf ctxf protf rest
          | None -> None)
       | JArray items ->
         (match jldctx_container_kind_of_items items with
          | Some ck -> jldctx_term_obj_fields ac idf revf typef ck langf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@language" then
      (match v with
       | JString s -> jldctx_term_obj_fields ac idf revf typef contk (Some (Some s)) ctxf protf rest
       | JNull -> jldctx_term_obj_fields ac idf revf typef contk (Some None) ctxf protf rest
       | _ -> None)
    else if k = "@context" then
      // A property- or type-scoped context: stored RAW (unprocessed) — see
      // td_scoped_context's doc comment. Any json_val shape is accepted
      // here (even one that will later fail to process); the failure
      // surfaces at point-of-use in JSONLD.Expand, not here.
      jldctx_term_obj_fields ac idf revf typef contk langf (Some v) protf rest
    else if k = "@protected" then
      (match v with
       | JBool b -> jldctx_term_obj_fields ac idf revf typef contk langf ctxf (Some b) rest
       | _ -> None)
    else
      // @index, @nest, @prefix, or any other unrecognized member: OUT of
      // scope.
      None

let process_term_def_obj (ac:active_context) (key:string) (fields:list (string & json_val))
                          (default_protected:bool) (override_protected:bool)
  : Tot (option active_context) =
  match jldctx_term_obj_fields ac None None None CK_None None None None fields with
  | None -> None
  | Some (idf, revf, typef, contk, langf, ctxf, protf) ->
    let protected = (match protf with Some b -> b | None -> default_protected) in
    (match (idf, revf) with
     | (Some _, Some _) -> None
     | (Some iri, None) ->
       let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                  td_reverse = false; td_language = langf;
                  td_scoped_context = ctxf; td_protected = protected } in
       if jldctx_check_redefine ac key td override_protected
       then Some ({ ac with ac_terms = (key, td) :: ac.ac_terms }) else None
     | (None, Some iri) ->
       let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                  td_reverse = true; td_language = langf;
                  td_scoped_context = ctxf; td_protected = protected } in
       if jldctx_check_redefine ac key td override_protected
       then Some ({ ac with ac_terms = (key, td) :: ac.ac_terms }) else None
     | (None, None) ->
       (match expand_iri ac key true with
        | None -> None
        | Some iri ->
          let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                     td_reverse = false; td_language = langf;
                     td_scoped_context = ctxf; td_protected = protected } in
          if jldctx_check_redefine ac key td override_protected
          then Some ({ ac with ac_terms = (key, td) :: ac.ac_terms }) else None))

// One context-object member: "@base" / "@vocab" / "@language" / "@version" /
// "@protected" / "@propagate", or an ordinary term definition (simple
// string form, expanded object form, or null = undefine). Any other
// keyword member is unsupported and fails honestly.
//
// "@base" resolves the new value against the PREVIOUS base (RFC 3986 §5.1.1,
// JSON-LD 1.1 API §4/context-processing step on @base): a document with
// nested contexts each supplying a relative "@base" chains correctly, not
// just a single flat concatenation.
//
// default_protected: this context OBJECT's own ambient "@protected"
// setting (pre-scanned once per object by context_process_fields), used
// as every sibling term's protected-ness unless it has its own "@protected"
// member. override_protected: true when this whole context_process call
// is a property-/type-scoped context application (JSONLD.Expand), which
// per spec is allowed to touch protected terms.
let context_process_one_field (ac:active_context) (key:string) (value:json_val)
                               (default_protected:bool) (override_protected:bool)
  : Tot (option active_context) =
  if key = "@base" then
    (match value with
     | JString s ->
       let resolved = (match ac.ac_base with
                       | Some b -> jldctx_resolve b s
                       | None -> s) in
       Some ({ ac with ac_base = Some resolved })
     | JNull -> Some ({ ac with ac_base = None })
     | _ -> None)
  else if key = "@vocab" then
    (match value with
     | JString s -> Some ({ ac with ac_vocab = Some s })
     | JNull -> Some ({ ac with ac_vocab = None })
     | _ -> None)
  else if key = "@language" then
    (match value with
     | JString s -> Some ({ ac with ac_language = Some s })
     | JNull -> Some ({ ac with ac_language = None })
     | _ -> None)
  else if key = "@version" then Some ac
  else if key = "@protected" then
    (match value with JBool _ -> Some ac | _ -> None)
  else if key = "@propagate" then
    (match value with JBool _ -> Some ac | _ -> None)
  else if jldctx_is_keyword key then None
  else
    (match value with
     | JNull ->
       (match jldctx_find_term ac.ac_terms key with
        | Some existing ->
          if existing.td_protected && not override_protected then None
          else Some ({ ac with ac_terms = jldctx_remove_term ac.ac_terms key })
        | None -> Some ac)
     | JString s ->
       (match expand_iri ac s true with
        | None -> None
        | Some iri ->
          let td = { td_iri = iri; td_type_mapping = None; td_container = CK_None;
                     td_reverse = false; td_language = None;
                     td_scoped_context = None; td_protected = default_protected } in
          if jldctx_check_redefine ac key td override_protected
          then Some ({ ac with ac_terms = (key, td) :: ac.ac_terms }) else None)
     | JObject termfields -> process_term_def_obj ac key termfields default_protected override_protected
     | _ -> None)

// ================================================================
// Top level: process an inline @context value (object, array, string, or
// null) against an active context. override_protected: true only for a
// property-/type-scoped context application (JSONLD.Expand); an ordinary
// node object's own inline "@context" member always passes false.
// ================================================================

let rec context_process (ac:active_context) (ctx:json_val) (override_protected:bool)
  : Tot (option active_context) (decreases ctx) =
  match ctx with
  | JNull ->
    if (not override_protected) && jldctx_any_protected ac.ac_terms then None
    else Some ({ ac with ac_terms = []; ac_vocab = None; ac_language = None })
  | JString _ -> None // remote context loading: a later phase (see banner)
  | JArray items -> context_process_array ac items override_protected
  | JObject fields -> context_process_fields ac fields (jldctx_scan_bool_key fields "@protected" false) override_protected
  | _ -> None

and context_process_array (ac:active_context) (items:list json_val) (override_protected:bool)
  : Tot (option active_context) (decreases items) =
  match items with
  | [] -> Some ac
  | hd :: tl ->
    (match context_process ac hd override_protected with
     | None -> None
     | Some ac1 -> context_process_array ac1 tl override_protected)

and context_process_fields (ac:active_context) (fields:list (string & json_val))
                           (default_protected:bool) (override_protected:bool)
  : Tot (option active_context) (decreases fields) =
  match fields with
  | [] -> Some ac
  | (key, value) :: rest ->
    (match context_process_one_field ac key value default_protected override_protected with
     | None -> None
     | Some ac1 -> context_process_fields ac1 rest default_protected override_protected)

// ================================================================
// @propagate-aware context application (JSON-LD 1.1 API §4/§5, the
// "propagate" thread) — used by JSONLD.Expand for a node object's own
// inline @context AND for a term's property-scoped context.
// default_propagate: true for both of those call sites (an ordinary or
// property-scoped context propagates into nested node objects unless it
// explicitly opts out via "@propagate": false); type-scoped context
// application (apply_type_scoped_contexts below) needs its own combining
// logic instead (a node object's @type can name several terms, each with
// its own scoped context, all folded against ONE shared "previous",
// not a per-term one — see that function's comment).
// ================================================================

let apply_context_with_propagate (ac:active_context) (ctxval:json_val)
                                  (default_propagate:bool) (override_protected:bool)
  : option active_context =
  match context_process ac ctxval override_protected with
  | None -> None
  | Some ac1 ->
    let propagate = jldctx_scan_propagate ctxval default_propagate in
    Some (if propagate then ac1 else { ac1 with ac_previous = Some ac })

// ================================================================
// Type-scoped context application (JSON-LD 1.1 API Expansion algorithm):
// for a node object's @type value(s), each type TERM (looked up in the
// context as it stood BEFORE any type-scoped modification — ac0 in
// apply_type_scoped_contexts below) that itself has a scoped context gets
// that context applied, in ASCENDING LEXICOGRAPHIC order of the type
// strings AS WRITTEN (toRdf/c011: @type ["t2","t1"] sorts to
// ["t1","t2"], so t2's mapping — applied SECOND — wins, matching the
// expected output). Default propagate is FALSE (unlike property-scoped
// contexts): by default the combined result does NOT persist past this
// node object's own fields into a nested node-object VALUE — JSONLD.Expand
// implements that "pop back to ac0" via ac_previous, which is why every
// step below needs to end up pointing at the SAME ac0 (not each other) —
// see toRdf/c017: two non-propagating type contexts (Bar then Foo) must
// both un-apply together when recursing into a "nested" property value,
// not just the LAST one applied.
// ================================================================

let rec jldctx_insert_sorted (x:string) (xs:list string) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> [x]
  | y :: rest -> if string_lt x y then x :: xs else y :: jldctx_insert_sorted x rest

let rec jldctx_sort_strings (xs:list string) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> jldctx_insert_sorted x (jldctx_sort_strings rest)

let rec jldctx_apply_type_scoped (ac:active_context) (types:list string) (any_non_propagating:bool)
  : Tot (option (active_context & bool)) (decreases types) =
  match types with
  | [] -> Some (ac, any_non_propagating)
  | t :: rest ->
    (match jldctx_find_term ac.ac_terms t with
     | Some td ->
       (match td.td_scoped_context with
        | Some scoped ->
          (match context_process ac scoped true with
           | None -> None
           | Some ac1 ->
             let propagate = jldctx_scan_propagate scoped false in
             jldctx_apply_type_scoped ac1 rest (any_non_propagating || not propagate))
        | None -> jldctx_apply_type_scoped ac rest any_non_propagating)
     | None -> jldctx_apply_type_scoped ac rest any_non_propagating)

// raw_types: the @type value's string entries AS WRITTEN (not yet
// IRI-expanded — term lookup for type-scoped contexts happens by term
// NAME against ac0, per spec). ac0: the active context BEFORE any
// type-scoped modification (after this node's own inline @context, if
// any, but before @type is consulted).
let apply_type_scoped_contexts (ac0:active_context) (raw_types:list string) : option active_context =
  match jldctx_apply_type_scoped ac0 (jldctx_sort_strings raw_types) false with
  | None -> None
  | Some (ac1, any_non_propagating) ->
    Some (if any_non_propagating then { ac1 with ac_previous = Some ac0 } else ac1)
