module JSONLD.Context

// ============================================================================
// JSON-LD 1.1 Context Processing — PHASE 3a (inline contexts only) + PHASE 3b
// (@reverse term definitions, map-shaped containers, RFC 3986 base
// resolution).
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
//     "@container": "@list"/"@set"/"@index"/"@language"/"@id"/"@type" (or
//     an array containing one of those plus "@set"), "@language" };
//   - "@vocab", "@base", "@language", "@version" (accepted; "@base" is
//     resolved against any previous "@base" per RFC 3986 — see
//     jldctx_resolve below — "@version" is otherwise ignored);
//   - compact-IRI + term-based prefix expansion (expand_iri below);
//   - context reset via JNull;
//   - an array of contexts, folded left to right;
//   - RFC 3986 relative-IRI resolution against @base: jldctx_resolve reuses
//     SPARQL11.IRI.Resolve.resolve_iri (a dependency-free-of-SPARQL11.Algebra
//     utility over RDF.Graph.Executable's wf_iri only — importing it here
//     does not invert the semantic-core/pragmatics stratification, since
//     that module has no reverse dependency on JSONLD.*; see
//     skills/fstar-module-style/SKILL.md).
//
// OUT of scope for 3b (a document that needs any of these gets an honest
// None from context_process, rather than a silently wrong active context):
//   - remote contexts (a JString context value — Phase 4 loader);
//   - scoped (property- or type-scoped) contexts: a nested "@context"
//     inside a term-definition object;
//   - "@protected" / "@import" / "@propagate" / "@nest" (as a term-def
//     member) / "@prefix";
//   - "@container" combinations involving "@graph" (graph containers).
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
// "is this @list"; 3b adds the four map-shaped containers.
type container_kind =
  | CK_None
  | CK_List
  | CK_Index
  | CK_Language
  | CK_Id
  | CK_Type

let ck_is_none (k:container_kind) : bool = match k with | CK_None -> true | _ -> false
let ck_is_list (k:container_kind) : bool = match k with | CK_List -> true | _ -> false

type term_def = {
  td_iri          : string;
  td_type_mapping : option string;
  td_container    : container_kind;
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

// A single "@container" string entry, or None for anything unsupported
// ("@graph" — graph containers stay out of scope for 3b — or a non-container
// keyword).
let jldctx_container_kind_of_string (s:string) : option container_kind =
  if s = "@list" then Some CK_List
  else if s = "@set" then Some CK_None
  else if s = "@index" then Some CK_Index
  else if s = "@language" then Some CK_Language
  else if s = "@id" then Some CK_Id
  else if s = "@type" then Some CK_Type
  else None

// An "@container" array (e.g. ["@index", "@set"]): every entry must parse,
// "@graph" anywhere rejects the whole array (graph containers out of
// scope), and the array's overall kind is the first non-CK_None entry
// (an array of only "@set" degenerates to CK_None, same as a bare "@set").
let rec jldctx_container_kind_of_items (items:list json_val) (acc:container_kind)
  : Tot (option container_kind) (decreases items) =
  match items with
  | [] -> Some acc
  | JString s :: rest ->
    if s = "@graph" then None
    else
      (match jldctx_container_kind_of_string s with
       | None -> None
       | Some k -> jldctx_container_kind_of_items rest (if ck_is_none k then acc else k))
  | _ -> None

// ================================================================
// Expanded (object-form) term definitions
// ================================================================

// One left-to-right pass over a term-definition object's members,
// threading the (id, reverse, type, container-kind, language) fields
// collected so far. None anywhere below means an unsupported / malformed
// member — process_term_def_obj turns that into an honest context_process
// failure rather than a silently incomplete term.
let rec jldctx_term_obj_fields
    (ac:active_context)
    (idf:option string) (revf:option string) (typef:option string)
    (contk:container_kind) (langf:option (option string))
    (fields:list (string & json_val))
  : Tot (option (option string & option string & option string & container_kind & option (option string)))
        (decreases fields) =
  match fields with
  | [] -> Some (idf, revf, typef, contk, langf)
  | (k, v) :: rest ->
    if k = "@id" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac (Some e) revf typef contk langf rest
          | None -> None)
       | _ -> None)
    else if k = "@reverse" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac idf (Some e) typef contk langf rest
          | None -> None)
       | _ -> None)
    else if k = "@type" then
      (match v with
       | JString s ->
         (match expand_iri ac s true with
          | Some e -> jldctx_term_obj_fields ac idf revf (Some e) contk langf rest
          | None -> None)
       | _ -> None)
    else if k = "@container" then
      (match v with
       | JString s ->
         (match jldctx_container_kind_of_string s with
          | Some ck -> jldctx_term_obj_fields ac idf revf typef ck langf rest
          | None -> None)
       | JArray items ->
         (match jldctx_container_kind_of_items items CK_None with
          | Some ck -> jldctx_term_obj_fields ac idf revf typef ck langf rest
          | None -> None)
       | _ -> None)
    else if k = "@language" then
      (match v with
       | JString s -> jldctx_term_obj_fields ac idf revf typef contk (Some (Some s)) rest
       | JNull -> jldctx_term_obj_fields ac idf revf typef contk (Some None) rest
       | _ -> None)
    else
      // @protected, @index, @nest, @prefix, a nested @context (scoped
      // context), or any other unrecognized member: OUT of scope for 3b.
      None

let process_term_def_obj (ac:active_context) (key:string) (fields:list (string & json_val))
  : Tot (option active_context) =
  match jldctx_term_obj_fields ac None None None CK_None None fields with
  | None -> None
  | Some (idf, revf, typef, contk, langf) ->
    (match (idf, revf) with
     | (Some _, Some _) -> None
     | (Some iri, None) ->
       let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                  td_reverse = false; td_language = langf } in
       Some ({ ac with ac_terms = (key, td) :: ac.ac_terms })
     | (None, Some iri) ->
       let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                  td_reverse = true; td_language = langf } in
       Some ({ ac with ac_terms = (key, td) :: ac.ac_terms })
     | (None, None) ->
       (match expand_iri ac key true with
        | None -> None
        | Some iri ->
          let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                     td_reverse = false; td_language = langf } in
          Some ({ ac with ac_terms = (key, td) :: ac.ac_terms })))

// One context-object member: "@base" / "@vocab" / "@language" / "@version",
// or an ordinary term definition (simple string form or expanded object
// form). Any other keyword member is unsupported and fails honestly.
//
// "@base" resolves the new value against the PREVIOUS base (RFC 3986 §5.1.1,
// JSON-LD 1.1 API §4/context-processing step on @base): a document with
// nested contexts each supplying a relative "@base" chains correctly, not
// just a single flat concatenation.
let context_process_one_field (ac:active_context) (key:string) (value:json_val)
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
  else if jldctx_is_keyword key then None
  else
    (match value with
     | JNull -> Some ac
     | JString s ->
       (match expand_iri ac s true with
        | None -> None
        | Some iri ->
          let td = { td_iri = iri; td_type_mapping = None; td_container = CK_None;
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
