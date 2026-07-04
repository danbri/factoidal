module JSONLD.Context

// ============================================================================
// JSON-LD 1.1 Context Processing — PHASE 3a (inline contexts only).
//
// Implements a subset of the JSON-LD 1.1 API "Context Processing" algorithm
// (spec section 4 / "Create Term Definition"), restricted to contexts given
// INLINE as a JSON object value or an array of such (no remote-document
// loading yet — see docs/designissues/2026-07-04-jsonld-program-lessons.md,
// phase 4 "Loader assume-val").
//
// Supported here:
//   - simple term definitions: "term": "IRI-or-compact-IRI-or-keyword";
//   - expanded term definitions: "term": { "@id"/"@reverse", "@type",
//     "@container": "@list"/"@set" (or an array containing those),
//     "@language" };
//   - "@vocab", "@base", "@language", "@version" (accepted, ignored);
//   - compact-IRI + term-based prefix expansion (expand_iri below);
//   - context reset via JNull;
//   - an array of contexts, folded left to right.
//
// OUT of scope for 3a (a document that needs any of these gets an honest
// None from context_process, rather than a silently wrong active context):
//   - remote contexts (a JString context value — Phase 4 loader);
//   - scoped (property- or type-scoped) contexts: any unrecognized keyword
//     inside a term-definition object (e.g. a nested "@context") or at the
//     top level (e.g. "@protected", "@import", "@propagate");
//   - "@container" values other than "@list" / "@set" (the map-shaped
//     containers: @index, @language, @id, @type as containers);
//   - full RFC 3986 relative-IRI resolution against @base (expand_iri below
//     does a naive concatenation only — sufficient for the toRdf fixtures
//     this phase targets, which do not exercise @base resolution).
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.JSON

// ================================================================
// Types
// ================================================================

// One term's definition. td_iri is either an absolute IRI or a keyword
// (e.g. "@id") when the term is a keyword ALIAS (as in {"id": "@id"}).
// td_type_mapping holds an already-expanded @type coercion target: an
// absolute IRI, or the literal keywords "@id" / "@vocab" for IRI-valued
// coercion (@json / @none are OUT of scope: term defs requesting them are
// rejected in process_term_def_obj below).
type term_def = {
  td_iri          : string;
  td_type_mapping : option string;
  td_container_list : bool;
  td_reverse      : bool;
  // None: no per-term override, use the active context's default language.
  // Some None: term explicitly carries no language ("@language": null).
  // Some (Some lg): term explicitly carries language lg.
  td_language     : option (option string);
}

type active_context = {
  ac_terms    : list (string & term_def);
  ac_vocab    : option string;
  ac_base     : option string;
  ac_language : option string;
}

let empty_active_context : active_context =
  { ac_terms = []; ac_vocab = None; ac_base = None; ac_language = None }

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

// Position of the first colon byte in s, scanning from pos, or None.
let rec jldctx_find_colon (s:string) (pos:nat) (fuel:nat)
  : Tot (option (p:nat{p < fs_byte_length s})) (decreases fuel) =
  if fuel = 0 then None
  else
    let n = fs_byte_length s in
    if pos >= n then None
    else if jbyte_at s pos = 0x3A then Some pos
    else jldctx_find_colon s (pos + 1) (fuel - 1)

// IRI Expansion (JSON-LD 1.1 API §5.1), simplified: no local-context /
// forward-reference lookahead (terms are resolved against the ALREADY
// built-up active context, which is enough for the sequential term
// definitions this phase supports), no full relative-IRI resolution.
let jldctx_expand_fallback (ac:active_context) (value:string) (vocab:bool)
  : Tot (option string) =
  if vocab then
    (match ac.ac_vocab with
     | Some v -> Some (String.concat "" [v; value])
     | None -> None)
  else
    (match ac.ac_base with
     | Some b -> Some (String.concat "" [b; value])
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

let rec jldctx_container_items_ok (items:list json_val) : Tot bool (decreases items) =
  match items with
  | [] -> true
  | JString s :: rest -> (s = "@list" || s = "@set") && jldctx_container_items_ok rest
  | _ -> false

let rec jldctx_container_has_list (items:list json_val) : Tot bool (decreases items) =
  match items with
  | [] -> false
  | JString s :: rest -> s = "@list" || jldctx_container_has_list rest
  | _ -> false

// ================================================================
// Expanded (object-form) term definitions
// ================================================================

// One left-to-right pass over a term-definition object's members,
// threading the (id, reverse, type, container-is-list, language) fields
// collected so far. None anywhere below means an unsupported / malformed
// member — process_term_def_obj turns that into an honest context_process
// failure rather than a silently incomplete term.
let rec jldctx_term_obj_fields
    (ac:active_context)
    (idf:option string) (revf:option string) (typef:option string)
    (contlist:bool) (langf:option (option string))
    (fields:list (string & json_val))
  : Tot (option (option string & option string & option string & bool & option (option string)))
        (decreases fields) =
  match fields with
  | [] -> Some (idf, revf, typef, contlist, langf)
  | (k, v) :: rest ->
    if k = "@id" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac (Some e) revf typef contlist langf rest
          | None -> None)
       | _ -> None)
    else if k = "@reverse" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac idf (Some e) typef contlist langf rest
          | None -> None)
       | _ -> None)
    else if k = "@type" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac idf revf (Some e) contlist langf rest
          | None -> None)
       | _ -> None)
    else if k = "@container" then
      (match v with
       | JString s ->
         if s = "@list" then jldctx_term_obj_fields ac idf revf typef true langf rest
         else if s = "@set" then jldctx_term_obj_fields ac idf revf typef contlist langf rest
         else None
       | JArray items ->
         if jldctx_container_items_ok items
         then jldctx_term_obj_fields ac idf revf typef
                (contlist || jldctx_container_has_list items) langf rest
         else None
       | _ -> None)
    else if k = "@language" then
      (match v with
       | JString s -> jldctx_term_obj_fields ac idf revf typef contlist (Some (Some s)) rest
       | JNull -> jldctx_term_obj_fields ac idf revf typef contlist (Some None) rest
       | _ -> None)
    else
      // @protected, @index, @nest, @prefix, a nested @context (scoped
      // context), or any other unrecognized member: OUT of scope for 3a.
      None

let process_term_def_obj (ac:active_context) (key:string) (fields:list (string & json_val))
  : Tot (option active_context) =
  match jldctx_term_obj_fields ac None None None false None fields with
  | None -> None
  | Some (idf, revf, typef, contlist, langf) ->
    (match (idf, revf) with
     | (Some _, Some _) -> None
     | (Some iri, None) ->
       let td = { td_iri = iri; td_type_mapping = typef; td_container_list = contlist;
                  td_reverse = false; td_language = langf } in
       Some ({ ac with ac_terms = (key, td) :: ac.ac_terms })
     | (None, Some iri) ->
       let td = { td_iri = iri; td_type_mapping = typef; td_container_list = contlist;
                  td_reverse = true; td_language = langf } in
       Some ({ ac with ac_terms = (key, td) :: ac.ac_terms })
     | (None, None) ->
       (match expand_iri ac key true with
        | None -> None
        | Some iri ->
          let td = { td_iri = iri; td_type_mapping = typef; td_container_list = contlist;
                     td_reverse = false; td_language = langf } in
          Some ({ ac with ac_terms = (key, td) :: ac.ac_terms })))

// One context-object member: "@base" / "@vocab" / "@language" / "@version",
// or an ordinary term definition (simple string form or expanded object
// form). Any other keyword member is unsupported and fails honestly.
let context_process_one_field (ac:active_context) (key:string) (value:json_val)
  : Tot (option active_context) =
  if key = "@base" then
    (match value with
     | JString s -> Some ({ ac with ac_base = Some s })
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
  else if jldctx_is_keyword key then None
  else
    (match value with
     | JNull -> Some ac
     | JString s ->
       (match expand_iri ac s true with
        | None -> None
        | Some iri ->
          let td = { td_iri = iri; td_type_mapping = None; td_container_list = false;
                     td_reverse = false; td_language = None } in
          Some ({ ac with ac_terms = (key, td) :: ac.ac_terms }))
     | JObject termfields -> process_term_def_obj ac key termfields
     | _ -> None)

// ================================================================
// Top level: process an inline @context value (object, array, string, or
// null) against an active context.
// ================================================================

let rec context_process (ac:active_context) (ctx:json_val) : Tot (option active_context) (decreases ctx) =
  match ctx with
  | JNull -> Some ({ ac with ac_terms = []; ac_vocab = None; ac_language = None })
  | JString _ -> None // remote context loading: Phase 4 (JSONLD.Loader), not this phase
  | JArray items -> context_process_array ac items
  | JObject fields -> context_process_fields ac fields
  | _ -> None

and context_process_array (ac:active_context) (items:list json_val)
  : Tot (option active_context) (decreases items) =
  match items with
  | [] -> Some ac
  | hd :: tl ->
    (match context_process ac hd with
     | None -> None
     | Some ac1 -> context_process_array ac1 tl)

and context_process_fields (ac:active_context) (fields:list (string & json_val))
  : Tot (option active_context) (decreases fields) =
  match fields with
  | [] -> Some ac
  | (key, value) :: rest ->
    (match context_process_one_field ac key value with
     | None -> None
     | Some ac1 -> context_process_fields ac1 rest)
