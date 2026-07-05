module JSONLD.Context

// ============================================================================
// JSON-LD 1.1 Context Processing — PHASE 3a (inline contexts only) + PHASE 3b
// (@reverse term definitions, map-shaped containers, RFC 3986 base
// resolution) + PHASE 4 (property-scoped / type-scoped contexts,
// @propagate, @protected, graph-container container kinds) + PHASE 6
// (remote contexts + "@import", JSONLD.Loader wiring — issue #275).
//
// Implements a subset of the JSON-LD 1.1 API "Context Processing" algorithm
// (spec section 4 / "Create Term Definition"), restricted to contexts given
// INLINE as a JSON object value or an array of such, PLUS remote contexts
// (a JString context value, or an "@import" member) via
// JSONLD.Loader.jsonld_load_document — see "Remote contexts" below.
//
// Remote contexts (PHASE 6, issue #275):
//   - a JString context value is resolved against the active context's
//     current @base (jldctx_resolve_context_iri), loaded via
//     jsonld_load_document, parsed as JSON, and its OWN top-level
//     "@context" member is processed recursively against the CURRENT
//     active context — exactly as if that member's value had appeared
//     inline. A document that is not valid JSON, or has no top-level
//     "@context" member, is an honest context_process failure (None).
//   - "@import" (a context-OBJECT member, JSON-LD 1.1 API §4.1 step
//     "Import") names a context to load and process FIRST, before this
//     object's own (non-@import) members — jldctx_extract_import splits
//     it out of the field list; context_process folds the imported
//     context's fields into `ac`, then context_process_fields folds this
//     object's remaining fields on top (later/local wins, matching the
//     spec's "merge, local replaces imported" semantics via ordinary
//     left-to-right term redefinition).
//   - recursion is bounded two ways: `fuel` (jld_remote_context_fuel,
//     decremented on every remote fetch — NOT on ordinary inline
//     recursion, so a large inline context never runs it out; see the
//     `%[fuel; ...]` decreases clauses below) caps chain DEPTH, and
//     `visited` (the list of already-loaded absolute IRIs on the current
//     chain) rejects a document that (directly or via a cycle of
//     @import/remote-context references) tries to load itself again.
//   - the loader itself is I/O (rule #11 ASSUME-IO): this module only
//     calls `jsonld_load_document : string -> option string` and treats
//     its result as an opaque (JSON, hopefully) document body; which
//     bytes come back for which IRI is a consumer-binary concern (see
//     JSONLD.Loader.fst's banner and
//     minimal_regrettable_glue_code_each_with_an_open_issue/275_jsonld_document_loader.sh).
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
//     override_protected = true — ONLY property-scoped context application
//     does that unconditionally (JSONLD.Expand.apply_property_scoped_context,
//     per spec); type-scoped context application
//     (jldctx_apply_type_scoped) passes override_protected = false, same
//     as an ordinary embedded/inline context — the JSON-LD 1.1 API
//     Expansion algorithm's @type-key loop never mentions override
//     protected at all, so it takes the Context Processing algorithm's
//     default (false). Redefining with an IDENTICAL definition is always
//     allowed regardless (term_defs_compatible), and the STORED
//     definition retains the EXISTING protected flag in that case
//     (jldctx_resolve_redefine — toRdf/pr42);
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
//   - "@import" as a TERM-DEF member (only as a context-object member,
//     the spec's actual location for it, is supported) / "@prefix";
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
open JSONLD.Loader

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
// PAIRED with the active context's ac_doc_url AS IT STOOD when this term
// was defined (process_term_def_obj) — issue #275/tc031: if the raw value
// is (or contains) a remote-context STRING reference, resolving it later
// (at point of use, potentially from a DIFFERENT document/active
// context) must use the document THIS scoped context was WRITTEN in, not
// whatever document happens to be current at the point of use.
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
  // Same three-way shape as td_language, for "@direction" ("ltr" / "rtl").
  td_direction      : option (option string);
  // PHASE 7 (property-valued index, issue TBD): a term's own "@index"
  // member ("@container": "@index" (or a container including "@graph")
  // plus "@index": "<term-or-compact-IRI>") names a PROPERTY that
  // JSONLD.Expand injects onto each map-entry item instead of dropping
  // the map key as pure metadata — see that module's
  // jexp_expand_property_index_map / jexp_index_key_field. Stored RAW
  // (not yet IRI-expanded): resolving it, AND finding ITS OWN term
  // definition for @type/@language/@direction coercion of the injected
  // value, are both point-of-USE questions (the active context may
  // define "prop" with its own "@type": "@vocab", toRdf/pi08-pi09),
  // exactly like an ordinary property key — not a term-definition-time
  // one.
  td_index          : option string;
  td_scoped_context : option (json_val & option string);
  td_protected      : bool;
  // JSON-LD 1.1 "prefix flag" (Create Term Definition step 24 / IRI
  // Expansion's compact-IRI step): only a term whose prefix flag is true
  // may serve as the prefix half of a compact IRI. Simple string-form
  // definitions get TRUE iff their expanded IRI ends in a gen-delim byte
  // (:/?#[]@ — "ex": "http://example.org/ns#" is a prefix, "ex":
  // "http://example.org/ns" is not); object-form definitions default
  // FALSE unless they carry an explicit "@prefix": true (toRdf/e124,
  // e125, and the "Does not expand a Compact IRI using a non-prefix
  // term" fixture).
  td_prefix         : bool;
}

// ac_previous: Some ac0 marks THIS active context as the result of a
// NON-PROPAGATING context application (a type-scoped context by default,
// or any scoped/inline context whose "@propagate" member is explicitly
// false) — ac0 is what a NESTED node object should use instead of this
// active context (JSONLD.Expand.expand_node "pops" to it on entry). None
// means this active context propagates normally into nested node objects.
type active_context = {
  ac_terms     : list (string & term_def);
  ac_vocab     : option string;
  ac_base      : option string;
  ac_language  : option string;
  // Context-level default base direction ("@direction": "ltr"/"rtl" on a
  // context object itself, mirrors ac_language) — None when no context in
  // the chain has set one (or the closest one reset it via JNull).
  ac_direction : option string;
  ac_previous  : option active_context;
  // PHASE 8 (processingMode, issue TBD): true when this active context is
  // being built under the JSON-LD 1.0 processing mode (the manifest's
  // `option.processingMode: "json-ld-1.0"` — toRdf/c029, ep02, tn01,
  // er21, pi01, so01). False (JSON-LD 1.1, the default) unless the
  // caller of parse_jsonld explicitly asked for 1.0. Carried as a FIELD
  // of active_context (rather than a fresh parameter threaded through
  // every Context/Expand function) since active_context is already the
  // one value every context-processing and expansion call passes down —
  // piggy-backing here needs zero signature changes in JSONLD.Expand.fst.
  // 1.1-only constructs (this module's own `context_process_one_field` /
  // `jldctx_term_obj_fields` / the "@import" branch of `context_process`)
  // check this flag and fail honestly rather than silently accepting
  // 1.1-only syntax under a declared 1.0 processing mode.
  ac_mode10    : bool;
  // PHASE 6 follow-up (issue #275 diagnosis, tc031 "@context resolutions
  // respect relative URLs"): the URL of the DOCUMENT whose CONTENT is
  // currently being read as context material — distinct from ac_base
  // (which "@base" directives can rewrite mid-context). A remote-context
  // STRING reference (context_process's JString branch) or an "@import"
  // reference resolves against ac_doc_url, never against ac_base — RFC
  // 3986's "the base IRI of a retrieved representation is that
  // resource's own URI", independent of any in-content @base rewrite.
  // Seeded once, at the top-level entry (JSONLD.Expand.expand, from
  // ac_base before any context processing has touched it — piggy-backed
  // exactly like ac_mode10, zero signature changes needed elsewhere);
  // updated ONLY by context_process's own JString/"@import" branches when
  // they actually fetch a document (to that document's own resolved
  // URL, for processing ITS content), and RESTORED on the surrounding
  // active_context once that fetch's content has been folded in, so
  // sibling context-array entries / fields keep resolving against the
  // ORIGINAL document. A term's OWN scoped "@context" (td_scoped_context)
  // snapshots ac_doc_url AT DEFINITION time (process_term_def_obj) since
  // it is resolved LATER, at point of use, by JSONLD.Expand — see that
  // field's doc comment.
  ac_doc_url   : option string;
  // ac_original_base: the document's OWN base IRI, fixed at the very
  // start of processing (JSONLD.Expand.expand seeds this from ac_base,
  // same point/reasoning as ac_doc_url) and never subsequently rewritten
  // by any "@base" directive. JSON-LD 1.1 API Context Processing: an
  // ENTIRE local context reset via JNull ("@context": null) restores the
  // active context's base IRI to this original value (spec: "necessary
  // ... to retain the original default base IRI") — toRdf/te060's outer
  // "@context": null nested object resolves its relative "@id" against
  // the DOCUMENT's base, not whatever @base happened to be active when
  // the reset was encountered. NOTE this is UNLIKE an ordinary "@base"
  // member being individually set to null (context_process_one_field's
  // "@base" handling, unaffected by this field) — THAT sets ac_base to
  // None outright (no restoration), per toRdf/te060's OWN "@base is set
  // to none" sibling object, whose now-unresolvable relative "@id"
  // ends up an invalid (non-absolute) IRI and is dropped by the existing
  // invalid-IRI triple filtering, not resolved against anything.
  ac_original_base : option string;
  // PHASE 6 follow-up (tso06 "@propagate: false on property-scoped
  // context with @import"): a ONE-SHOT flag consumed by
  // JSONLD.Expand.expand_node's own entry-popping check. Set true by
  // apply_property_scoped_context exactly when it ALSO freshly sets
  // ac_previous (a non-propagating property-scoped context result) —
  // that ac_eff is used DIRECTLY as the `ac` argument for expanding the
  // property's OWN value (the scope's direct target, e.g. tso06's "bar"
  // value), which must NOT immediately pop back (it would discard the
  // very scope just computed for it) — UNLIKE a type-scoped context's
  // ac_previous (set by JSONLD.Context.jldctx_apply_type_scoped), which
  // is consumed strictly ONE level down (this node's OWN fields use the
  // type-scoped ac directly, computed fresh INSIDE expand_node itself,
  // never re-entering expand_node for the SAME node), so type-scoped's
  // ac_previous never needs this suppression. expand_node clears the
  // flag unconditionally on every entry (one-shot), so it correctly
  // stops suppressing by the time a GRANDCHILD of the scoped value is
  // reached — see that function's updated comment.
  ac_suppress_pop : bool;
}

let empty_active_context : active_context =
  { ac_terms = []; ac_vocab = None; ac_base = None; ac_language = None;
    ac_direction = None; ac_previous = None; ac_mode10 = false;
    ac_doc_url = None; ac_original_base = None; ac_suppress_pop = false }

// ================================================================
// Small string / list helpers
// ================================================================

// Keywords all start with a commercial-at byte (mirrors
// Parser.JSONLD.jld_is_keyword; duplicated rather than imported since
// Parser.JSONLD must not be a dependency of this module).
let jldctx_is_keyword (s:string) : bool =
  fs_byte_length s > 0 && jbyte_at s 0 = 0x40

// The ACTUAL JSON-LD 1.1 keywords (JSON-LD 1.1 §1.7 "Syntax Tokens and
// Keywords"). Distinct from "has the form of a keyword" below: the spec
// treats a non-keyword string that merely LOOKS like one ("@ignoreMe")
// as ignorable-with-a-warning, while genuinely at-prefixed strings that
// do NOT look like keywords ("@", "@foo.bar") are ordinary term/IRI
// material (toRdf/e119-e122, pr34-pr39).
let jldctx_actual_keyword (s:string) : bool =
  s = "@base" || s = "@container" || s = "@context" || s = "@direction"
  || s = "@graph" || s = "@id" || s = "@import" || s = "@included"
  || s = "@index" || s = "@json" || s = "@language" || s = "@list"
  || s = "@nest" || s = "@none" || s = "@prefix" || s = "@propagate"
  || s = "@protected" || s = "@reverse" || s = "@set" || s = "@type"
  || s = "@value" || s = "@version" || s = "@vocab"

let jldctx_is_alpha_byte (b:int) : bool =
  (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A)

let rec jldctx_all_alpha_from (s:string) (pos:nat) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else
    let n = fs_byte_length s in
    if pos >= n then true
    else if jldctx_is_alpha_byte (jbyte_at s pos) then jldctx_all_alpha_from s (pos + 1) (fuel - 1)
    else false

// RFC 3986 §3.1 scheme character: ALPHA / DIGIT / "+" / "-" / "."
// (used to tell a genuine URI scheme prefix apart from a colon that
// merely sits inside a fragment/path component — see
// expand_iri_gen's compact-IRI branch).
let jldctx_is_scheme_char (b:int) : bool =
  jldctx_is_alpha_byte b || (b >= 0x30 && b <= 0x39) || b = 0x2B || b = 0x2D || b = 0x2E

let rec jldctx_all_scheme_chars_from (s:string) (pos:nat) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else
    let n = fs_byte_length s in
    if pos >= n then true
    else if jldctx_is_scheme_char (jbyte_at s pos) then jldctx_all_scheme_chars_from s (pos + 1) (fuel - 1)
    else false

// "Has the form of a keyword" (JSON-LD 1.1 API §4.1.5 / Create Term
// Definition): "@" followed by one or more ALPHA bytes only. "@" alone
// (nothing after the at) and "@foo.bar" (a dot) do NOT have keyword
// form. Includes the actual keywords themselves — callers that need
// "keyword-LIKE but not a real keyword" use jldctx_keyword_lookalike.
let jldctx_keyword_form (s:string) : bool =
  let n = fs_byte_length s in
  n >= 2 && jbyte_at s 0 = 0x40 && jldctx_all_alpha_from s 1 n

let jldctx_keyword_lookalike (s:string) : bool =
  jldctx_keyword_form s && not (jldctx_actual_keyword s)

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
  a.td_language = b.td_language && a.td_direction = b.td_direction &&
  a.td_index = b.td_index && a.td_scoped_context = b.td_scoped_context &&
  a.td_prefix = b.td_prefix

// Any byte of `s` is a slash — used (with jldctx_find_colon) to reject
// an explicit "@prefix" member on a term name that cannot be a prefix
// (toRdf/er49; JSON-LD 1.1 API Create Term Definition step 24).
let rec jldctx_slash_from (s:string) (pos:nat) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let n = fs_byte_length s in
    if pos >= n then false
    else if jbyte_at s pos = 0x2F then true
    else jldctx_slash_from s (pos + 1) (fuel - 1)

let jldctx_key_has_slash (s:string) : bool =
  jldctx_slash_from s 0 (fs_byte_length s + 1)

// Last byte of `s` is an RFC 3986 gen-delim (":" "/" "?" "#" "[" "]"
// "@") — the JSON-LD 1.1 test for whether a simple string-form term
// definition is usable as a compact-IRI prefix (td_prefix's doc).
let jldctx_ends_gen_delim (s:string) : bool =
  let n = fs_byte_length s in
  n > 0 &&
  (let b = jbyte_at s (n - 1) in
   b = 0x3A || b = 0x2F || b = 0x3F || b = 0x23 || b = 0x5B || b = 0x5D || b = 0x40)

// The term_def to ACTUALLY store for a redefinition site: a protected
// existing term may only be replaced by an identical definition, UNLESS
// override_protected is set (property-scoped context application always
// passes true — JSONLD.Expand.apply_property_scoped_context; type-scoped
// context application (jldctx_apply_type_scoped) passes false, per that
// function's own comment — it gets NO blanket override right). Beyond a
// plain allow/reject bool, JSON-LD 1.1 API Create Term Definition's protected-redefinition
// step doesn't just allow a compatible redefinition through, it says "Set
// definition to previous definition to retain the value of protected" —
// i.e. the STORED definition is the OLD (existing) one, not the new one,
// so a later, still-compatible redefinition that happens to omit its own
// "@protected" entry (defaulting to false) does not silently un-protect
// the term (toRdf/pr42: a protected term redefined identically by a
// context object with no "@protected" member must stay protected, so
// that a THIRD, incompatible redefinition still errors). Every other
// path (no existing term, or override_protected/unprotected-existing)
// stores new_td unchanged, matching the ordinary "later wins" rule.
let jldctx_resolve_redefine (ac:active_context) (key:string) (new_td:term_def) (override_protected:bool)
  : option term_def =
  match jldctx_find_term ac.ac_terms key with
  | None -> Some new_td
  | Some existing ->
    if existing.td_protected && not override_protected
    then (if term_defs_compatible existing new_td then Some existing else None)
    else Some new_td

// Position of the first colon byte in s, scanning from pos, or None.
let rec jldctx_find_colon (s:string) (pos:nat) (fuel:nat)
  : Tot (option (p:nat{p < fs_byte_length s})) (decreases fuel) =
  if fuel = 0 then None
  else
    let n = fs_byte_length s in
    if pos >= n then None
    else if jbyte_at s pos = 0x3A then Some pos
    else jldctx_find_colon s (pos + 1) (fuel - 1)

// True when `s` contains a colon at a byte position that is NEITHER the
// first NOR the last byte of s (part of the JSON-LD 1.1 API Create Term
// Definition self-consistency gate — see jldctx_term_needs_self_check).
let jldctx_colon_not_at_edges (s:string) : bool =
  let n = fs_byte_length s in
  (match jldctx_find_colon s 0 (n + 1) with
   | Some c -> c > 0 && c < n - 1
   | None -> false)

// A term NAME that is itself compact-IRI- or absolute-IRI-shaped (a
// colon not at the very first/last byte) or contains a slash anywhere
// triggers a MANDATORY self-consistency check whenever the term also
// carries an explicit "@id" mapping (JSON-LD 1.1 API Create Term
// Definition: "If the term contains a colon (:) anywhere but as the
// first or last character of term, or if it contains a slash (/)
// anywhere: ... If the result of IRI expanding term ... is not the same
// as the IRI mapping of definition, an invalid IRI mapping error has
// been detected"). Checked by process_term_def_obj's (Some iri, None)
// [@id-present] arm — toRdf/er43 (a term name that IS an absolute IRI,
// given an unrelated "@id" alias to the keyword @type), toRdf/er48 (a
// slash-shaped relative-IRI term name, which cannot expand to an IRI at
// all with no @base/@vocab in scope).
let jldctx_term_needs_self_check (s:string) : bool =
  jldctx_colon_not_at_edges s || jldctx_key_has_slash s

// A blank node identifier ("_:xyz") — legal as an @id/@reverse IRI
// mapping, but NOT as an @type mapping (JSON-LD 1.1 API Create Term
// Definition: "if the expanded type is neither @id, nor @json, nor
// @none, nor @vocab, nor an IRI, an invalid type mapping error" — a
// blank node identifier is none of those — toRdf/er13).
let jldctx_is_bnode_id (s:string) : bool =
  fs_byte_length s >= 2 && jbyte_at s 0 = 0x5F && jbyte_at s 1 = 0x3A

// A cyclic IRI mapping (JSON-LD 1.1 API Create Term Definition's
// `defined` map: "If defined contains the entry term and the associated
// value is false, a cyclic IRI mapping error has been detected"): an
// @id/@reverse value that is a compact IRI whose PREFIX is the very
// term key CURRENTLY being defined, when that key has no term
// definition yet in `ac` (i.e. its own definition is still in progress
// — the "defined[term] = false" case; a key that DOES already have an
// entry in `ac` was fully defined by an EARLIER context application or
// an earlier field of this same context object, which is not a cycle)
// — toRdf/er10: {"term": {"@id": "term:term"}} needs "term" as a
// prefix to expand its own @id value.
// Mirrors expand_iri_gen's OWN guard order before it would actually
// perform a compact-IRI prefix lookup on `key` — a colon match that
// expand_iri_gen would instead shortcut via the "_" blank-node marker,
// the non-scheme-shaped-prefix fallback, or the "//" authority marker
// (an already-absolute IRI, e.g. toRdf/e067's "http": "http://example.
// com/...", where the VALUE happens to start with the same "http"
// prefix as the TERM being defined — this is an ordinary absolute IRI,
// not a dependency on the term "http"'s own in-progress definition)
// is NOT a cyclic reference at all; only a genuine compact-IRI-prefix
// dependency on `key` itself, still undefined, is.
let jldctx_self_cyclic (ac:active_context) (key:string) (raw:string) : bool =
  let n = fs_byte_length raw in
  (match jldctx_find_colon raw 0 (n + 1) with
   | Some c ->
     c > 0 &&
     (let prefix = fs_byte_sub raw 0 c in
      prefix <> "_" &&
      jldctx_all_scheme_chars_from prefix 0 c &&
      not (jbyte_at raw (c + 1) = 0x2F && jbyte_at raw (c + 2) = 0x2F) &&
      prefix = key &&
      None? (jldctx_find_term ac.ac_terms key))
   | None -> false)

// RFC 3986 reference resolution, reusing SPARQL11.IRI.Resolve.resolve_iri
// (which takes a wf_iri base). base here is an ordinary string because
// active_context.ac_base is populated incrementally (see the "@base"
// handling in context_process_one_field below) and F* cannot statically
// know it is well-formed; the runtime is_iri check refines it to wf_iri
// for the call, with a safe fallback to the unresolved base on failure —
// mirrors resolve_iri's own is_iri-checked-result fallback.
let jldctx_resolve (base:string) (relative:string) : string =
  if is_iri base then resolve_iri base relative else base

// ================================================================
// Remote contexts (PHASE 6, issue #275): a JString context value or an
// "@import" member names a context by reference rather than value.
// ================================================================

// Depth budget for remote-context / "@import" chains — decremented only
// when a fetch actually happens (see the `%[fuel; ...]` decreases clauses
// below), so an inline context with many term definitions never
// consumes it. 32 is generous for any realistic chain (the toRdf suite's
// deepest chain is 2: a document's own remote context "@import"-ing one
// further context).
let jld_remote_context_fuel : nat = 32

// Resolve a context reference (the JString context value, or an
// "@import" member's value) against ac_doc_url — the URL of the document
// whose CONTENT is currently being read, per RFC 3986 §5.1 (issue #275
// tc031: NOT ac_base, which an in-content "@base" directive may already
// have rewritten by the time a LATER array entry/field names a remote
// context — the loading document's own URL never moves just because its
// content set @base). Falls back to ac_base when ac_doc_url is unset
// (the external `expandContext` API-option entry point, which seeds
// neither field — see JSONLD.Expand.expand's banner) so that path keeps
// its prior (ac_base-relative) behavior unchanged. Without either, only
// an already-absolute IRI is usable (mirrors jldctx_expand_fallback's own
// no-base behavior).
let jldctx_resolve_context_iri (ac:active_context) (raw:string) : option string =
  match ac.ac_doc_url with
  | Some d -> Some (jldctx_resolve d raw)
  | None ->
    (match ac.ac_base with
     | Some b -> Some (jldctx_resolve b raw)
     | None -> if is_iri raw then Some raw else None)

// Split a context object's fields into its (at most one) "@import" value
// and the rest — mirrors JSONLD.Expand.jexp_extract_context's shape for
// "@context" extraction from a node object's own fields.
let jldctx_extract_import (fields:list (string & json_val))
  : (option string & list (string & json_val)) =
  let importval =
    (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@import") fields with
     | Some (_, JString s) -> Some s
     | _ -> None) in
  let rest = List.Tot.filter (fun (kv:(string & json_val)) -> fst kv <> "@import") fields in
  (importval, rest)

// Fetch `resolved`, parse it as JSON, and return its top-level
// "@context" member's value. None on any failure: not loadable, not
// valid JSON, or no "@context" member (JSON-LD 1.1 API §4.1's "loading
// remote context failed" / "invalid remote context" errors — the toRdf
// suite's negative tests for exactly these two cases, e.g. "Error
// dereferencing a remote context" / "Invalid remote context").
let jldctx_fetch_remote_context (resolved:string) : option json_val =
  match jsonld_load_document resolved with
  | None -> None
  | Some raw ->
    (match parse_json raw with
     | None -> None
     | Some doc -> json_get_field "@context" doc)

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

// `in_ctx`: true when called DURING context processing (Create Term
// Definition — the spec's "local context is not null" condition), where
// compact-IRI prefix lookup applies regardless of the prefix flag
// (toRdf/e050: the term KEY "issue:raisedBy" resolves through the
// object-form — hence flag-false — term "issue"); at expansion time
// (in_ctx false) the flag gates prefix use ("Does not expand a Compact
// IRI using a non-prefix term").
let expand_iri_gen (ac:active_context) (value:string) (vocab:bool) (in_ctx:bool) : Tot (option string) =
  let n = fs_byte_length value in
  if n = 0 then
    // RFC 3986 §5.4: the EMPTY reference resolves to the base itself
    // (minus any fragment; query preserved) — the "urn:ex:p": "" case
    // of the toRdf IRI Resolution battery. Only meaningful
    // document-relative; an empty TERM/vocab-relative key stays
    // unresolvable (the suite's "Definition for the empty term"
    // negative expects empty terms to be rejected).
    (if vocab then None else jldctx_expand_fallback ac value false)
  else if jldctx_actual_keyword value then Some value
  else
    // Full-term substitution applies only vocab-relative (toRdf/e048:
    // "Terms are ignored in @id" — an @id value equal to a defined
    // term's name still resolves document-relative against @base, NOT
    // through the term). Compact-IRI PREFIX lookup (the colon branch
    // below) stays available for both modes, per the same fixture's
    // "compact-iris:are-considered" @id.
    let term_hit = if vocab then jldctx_find_term ac.ac_terms value else None in
    match term_hit with
    | Some td -> Some td.td_iri
    | None ->
      // A keyword LOOKALIKE ("@ignoreMe") expands to itself — spec-wise
      // it expands to null with a warning, but every consumer of this
      // function's output already drops a colon-less non-IRI string at
      // the RDF layer (toRdf/e122: the node reference {"@id":
      // "@ignoreMe"} and its linking triple vanish), while returning
      // None here would instead DROP THE @id MEMBER and mint a fresh
      // blank node — observably wrong. Context-processing call sites
      // never see this branch (they pre-check with
      // jldctx_keyword_lookalike before calling — see
      // context_process_one_field / jldctx_term_obj_fields).
      if jldctx_keyword_form value then Some value
      else
      (match jldctx_find_colon value 0 (n + 1) with
       | None -> jldctx_expand_fallback ac value vocab
       | Some c ->
         if c = 0 then jldctx_expand_fallback ac value vocab
         else
           let prefix = fs_byte_sub value 0 c in
           if prefix = "_" then Some value
           // RFC 3986 §3.1: a URI scheme is `ALPHA *(ALPHA / DIGIT / "+"
           // / "-" / ".")` — every byte before the colon must be a
           // scheme-legal character for that colon to be a scheme (or
           // compact-IRI prefix) delimiter at all. A value like
           // "#Test:2" has its colon INSIDE a fragment (introduced by
           // "#", not a scheme character), so it can never be an
           // absolute-or-compact IRI — treating it as one leaves it
           // unresolved against @base/@vocab (toRdf/e109: "IRI expansion
           // of fragments including ':'"). Falls through to the plain
           // base/vocab fallback instead.
           else if not (jldctx_all_scheme_chars_from prefix 0 c) then
             jldctx_expand_fallback ac value vocab
           else if jbyte_at value (c + 1) = 0x2F && jbyte_at value (c + 2) = 0x2F then Some value
           else
             (match jldctx_find_term ac.ac_terms prefix with
              | None -> Some value
              | Some ptd ->
                if jldctx_is_keyword ptd.td_iri then None
                // JSON-LD 1.1 prefix flag (td_prefix's doc comment): a
                // term not usable as a prefix leaves the compact-IRI-
                // shaped value untouched — it already has a colon, so
                // downstream treats it as an (odd but well-formed) IRI.
                // Context processing (in_ctx) bypasses the gate — see
                // this function's banner.
                else if not (in_ctx || ptd.td_prefix) then Some value
                else
                  let suffix = fs_byte_sub value (c + 1) (n - c - 1) in
                  Some (String.concat "" [ptd.td_iri; suffix])))

// Expansion-time IRI expansion (prefix flag honored) — the widely-used
// entry point; context processing uses jldctx_expand_iri_ctx below.
let expand_iri (ac:active_context) (value:string) (vocab:bool) : Tot (option string) =
  expand_iri_gen ac value vocab false

let jldctx_expand_iri_ctx (ac:active_context) (value:string) (vocab:bool) : Tot (option string) =
  expand_iri_gen ac value vocab true

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
    (dirf:option (option string)) (idxf:option string)
    (ctxf:option json_val) (protf:option bool)
    (fields:list (string & json_val))
  : Tot (option (option string & option string & option string & container_kind &
                 option (option string) & option (option string) & option string &
                 option json_val & option bool))
        (decreases fields) =
  match fields with
  | [] -> Some (idf, revf, typef, contk, langf, dirf, idxf, ctxf, protf)
  | (k, v) :: rest ->
    if k = "@id" then
      (match v with
       | JString s ->
         // An @id value that LOOKS like (but is not) a keyword is
         // ignored — the entry is skipped and the term's IRI mapping
         // falls back to @vocab + term name (toRdf/e120's "ignoreMe":
         // {"@id": "@ignoreMe"} -> vocab/ignoreMe). Actual keywords
         // ("id": {"@id": "@id"}) still alias normally.
         if jldctx_keyword_lookalike s
         then jldctx_term_obj_fields ac idf revf typef contk langf dirf idxf ctxf protf rest
         else
         (match jldctx_expand_iri_ctx ac s true with
          // JSON-LD 1.1 API Create Term Definition: "if [the resulting
          // IRI mapping] equals @context, an invalid keyword alias error
          // has been detected" (toRdf/er19 — aliasing an ordinary term
          // to the @context keyword itself).
          | Some e -> if e = "@context" then None
                      else jldctx_term_obj_fields ac (Some e) revf typef contk langf dirf idxf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@reverse" then
      (match v with
       | JString s ->
         (match jldctx_expand_iri_ctx ac s true with
          | Some e -> jldctx_term_obj_fields ac idf (Some e) typef contk langf dirf idxf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@type" then
      (match v with
       | JString s ->
         (match jldctx_expand_iri_ctx ac s true with
          // JSON-LD 1.1 API Create Term Definition: "If the expanded type
          // is @json or @none, and processing mode is json-ld-1.0, an
          // invalid type mapping error has been detected" (toRdf/tn01 —
          // "@type: @none is illegal in 1.0"). Separately: "Otherwise, if
          // the expanded type is neither @id, nor @json, nor @none, nor
          // @vocab, nor an IRI, an invalid type mapping error has been
          // detected" — a blank node identifier is none of those
          // (toRdf/er13: "_:not-an-iri" expands unchanged, per
          // expand_iri_gen's "_" prefix branch, to a syntactically
          // colon-bearing but type-mapping-illegal blank node id).
          | Some e ->
            if ac.ac_mode10 && (e = "@json" || e = "@none") then None
            else if e = "@id" || e = "@json" || e = "@none" || e = "@vocab" then
              jldctx_term_obj_fields ac idf revf (Some e) contk langf dirf idxf ctxf protf rest
            else if jldctx_is_bnode_id e then None
            else jldctx_term_obj_fields ac idf revf (Some e) contk langf dirf idxf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@container" then
      // JSON-LD 1.1 API Create Term Definition: "If the container value
      // is @graph, @id, or @type, or is otherwise not a string [i.e. an
      // array], generate an invalid container mapping error and abort
      // processing if processing mode is json-ld-1.0" (toRdf/ter21 —
      // "Invalid container mapping"). @list/@set/@index/@language single-
      // string containers stay legal in 1.0; every array-shaped
      // "@container" value is 1.1-only.
      (match v with
       | JString s ->
         (match jldctx_container_kind_of_string s with
          | Some ck ->
            if ac.ac_mode10 && (ck = CK_Graph || ck = CK_Id || ck = CK_Type) then None
            else jldctx_term_obj_fields ac idf revf typef ck langf dirf idxf ctxf protf rest
          | None -> None)
       | JArray items ->
         if ac.ac_mode10 then None
         else
         (match jldctx_container_kind_of_items items with
          | Some ck -> jldctx_term_obj_fields ac idf revf typef ck langf dirf idxf ctxf protf rest
          | None -> None)
       | _ -> None)
    else if k = "@language" then
      (match v with
       | JString s -> jldctx_term_obj_fields ac idf revf typef contk (Some (Some s)) dirf idxf ctxf protf rest
       | JNull -> jldctx_term_obj_fields ac idf revf typef contk (Some None) dirf idxf ctxf protf rest
       | _ -> None)
    else if k = "@direction" then
      (match v with
       | JString s ->
         if s = "ltr" || s = "rtl"
         then jldctx_term_obj_fields ac idf revf typef contk langf (Some (Some s)) idxf ctxf protf rest
         else None
       | JNull -> jldctx_term_obj_fields ac idf revf typef contk langf (Some None) idxf ctxf protf rest
       | _ -> None)
    else if k = "@index" then
      // PHASE 7 (property-valued index): stored RAW (unresolved) — see
      // td_index's doc comment — because the property this names must be
      // resolved (and its OWN term definition looked up for @type/
      // @language/@direction coercion) at the point of USE, exactly like
      // an ordinary property key (JSONLD.Expand.jexp_index_key_field), not
      // at term-definition time. A keyword value (toRdf/pi03: "@index":
      // "@index") is rejected outright — keywords can never name a
      // property.
      // "@index" is 1.1-only (Create Term Definition: "If processing mode
      // is json-ld-1.0 or container mapping does not include @index, an
      // invalid term definition has been detected").
      if ac.ac_mode10 then None
      else
      (match v with
       | JString s -> if jldctx_is_keyword s then None
                       else jldctx_term_obj_fields ac idf revf typef contk langf dirf (Some s) ctxf protf rest
       | _ -> None)
    else if k = "@context" then
      // A property- or type-scoped context: stored RAW (unprocessed) — see
      // td_scoped_context's doc comment. Any json_val shape is accepted
      // here (even one that will later fail to process); the failure
      // surfaces at point-of-use in JSONLD.Expand, not here. 1.1-only
      // (Create Term Definition: "If processing mode is json-ld-1.0, an
      // invalid term definition has been detected").
      if ac.ac_mode10 then None
      else jldctx_term_obj_fields ac idf revf typef contk langf dirf idxf (Some v) protf rest
    else if k = "@protected" then
      // "@protected" (the per-term override) is 1.1-only (Create Term
      // Definition: "If value has an @protected entry ... If processing
      // mode is json-ld-1.0, an invalid term definition has been
      // detected").
      if ac.ac_mode10 then None
      else
      (match v with
       | JBool b -> jldctx_term_obj_fields ac idf revf typef contk langf dirf idxf ctxf (Some b) rest
       | _ -> None)
    else if k = "@prefix" then
      // Validated here (must be a boolean), CONSUMED by
      // process_term_def_obj's separate jldctx_scan_bool_key pass —
      // keeps this accumulator tuple from growing an eleventh slot.
      (match v with
       | JBool _ -> jldctx_term_obj_fields ac idf revf typef contk langf dirf idxf ctxf protf rest
       | _ -> None)
    else
      // @nest or any other unrecognized member: OUT of scope.
      None

// Pair a term's raw scoped-@context value (if any) with the document URL
// in effect AT THIS MOMENT (ac.ac_doc_url — the ac passed into
// process_term_def_obj, current for the WHOLE of this term-definition
// object's own processing, since no remote fetch happens mid-way through
// parsing one term's sibling members) — see td_scoped_context's doc
// comment / tc031.
let jldctx_wrap_scoped (ac:active_context) (ctxf:option json_val) : option (json_val & option string) =
  match ctxf with
  | Some c -> Some (c, ac.ac_doc_url)
  | None -> None

let process_term_def_obj (ac:active_context) (key:string) (fields:list (string & json_val))
                          (default_protected:bool) (override_protected:bool)
  : Tot (option active_context) =
  // Cyclic IRI mapping pre-check (jldctx_self_cyclic's doc comment):
  // scanned against the RAW (unexpanded) @id/@reverse string values,
  // before jldctx_term_obj_fields ever calls jldctx_expand_iri_ctx on
  // them — toRdf/er10.
  let self_ref =
    (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@id") fields with
     | Some (_, JString s) -> jldctx_self_cyclic ac key s
     | _ -> false) ||
    (match List.Tot.find (fun (kv:(string & json_val)) -> fst kv = "@reverse") fields with
     | Some (_, JString s) -> jldctx_self_cyclic ac key s
     | _ -> false) in
  if self_ref then None else
  match jldctx_term_obj_fields ac None None None CK_None None None None None None fields with
  | None -> None
  | Some (idf, revf, typef, contk, langf, dirf, idxf, ctxf, protf) ->
    // toRdf/pi02: a term's "@index" member is only meaningful when its
    // OWN "@container" mapping actually includes "@index" (plain or
    // "@graph"+"@index") — anything else is a spec error, not a
    // silently-ignored member.
    if Some? idxf && not (contk = CK_Index || contk = CK_GraphIndex) then None
    // JSON-LD 1.1 API Create Term Definition, the @container:@type
    // step: "If the container mapping of definition includes @type:
    // If type mapping in definition is undefined, set it to @id. If
    // type mapping in definition is neither @id nor @vocab, an invalid
    // type mapping error has been detected" (toRdf/m020: "@type":
    // "literal" on a "@container": "@type" term).
    else if contk = CK_Type && Some? typef && typef <> Some "@id" && typef <> Some "@vocab" then None
    else
    let protected = (match protf with Some b -> b | None -> default_protected) in
    // Object-form definitions are compact-IRI prefixes only on explicit
    // request (td_prefix's doc comment). An EXPLICIT @prefix member is
    // itself validated (JSON-LD 1.1 API Create Term Definition step 24):
    // the term name may not contain a colon or slash (toRdf/er49:
    // "./something" cannot be a prefix), and a true prefix flag may not
    // sit on a keyword alias (toRdf/pr33: {"@id": "@type", "@prefix":
    // true}).
    let has_prefix_member =
      List.Tot.existsb (fun (kv:(string & json_val)) -> fst kv = "@prefix") fields in
    let prefix_flag = jldctx_scan_bool_key fields "@prefix" false in
    if has_prefix_member &&
       Some? (jldctx_find_colon key 0 (fs_byte_length key + 1)) then None
    else if has_prefix_member && jldctx_key_has_slash key then None
    else
    (match (idf, revf) with
     | (Some _, Some _) -> None
     | (Some iri, None) ->
       if prefix_flag && jldctx_is_keyword iri then None
       // JSON-LD 1.1 API Create Term Definition self-consistency check
       // (jldctx_term_needs_self_check's doc comment): a term name that
       // is itself compact-IRI-/absolute-IRI-shaped or slash-bearing
       // must IRI-expand to the SAME mapping its explicit @id just
       // produced — toRdf/er43, toRdf/er48. 1.1-only: the whole
       // colon-in-term self-consistency step is new in the JSON-LD 1.1
       // API's Create Term Definition (er43's manifest twin te026, a
       // json-ld-1.0-specVersion POSITIVE, redefines the rdf:type IRI
       // with "@id": "@type" — "uses @type syntax NOW illegal", i.e.
       // legal under 1.0).
       // The key is expanded with its OWN entry stripped: the preview
       // pass (jldctx_preview_prefixes) may have pre-registered this
       // very term, and full-term substitution through that entry would
       // make the check vacuously succeed (toRdf/er48: "./something"
       // must fail to expand as a term name, not resolve through its
       // own preview registration).
       else if (not ac.ac_mode10) && jldctx_term_needs_self_check key &&
               jldctx_expand_iri_ctx ({ ac with ac_terms = jldctx_remove_term ac.ac_terms key }) key true <> Some iri then None
       else
       let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                  td_reverse = false; td_language = langf; td_direction = dirf; td_index = idxf;
                  td_scoped_context = jldctx_wrap_scoped ac ctxf; td_protected = protected; td_prefix = prefix_flag } in
       (match jldctx_resolve_redefine ac key td override_protected with
        | Some final_td -> Some ({ ac with ac_terms = (key, final_td) :: ac.ac_terms })
        | None -> None)
     | (None, Some iri) ->
       // JSON-LD 1.1 API Create Term Definition, @reverse's @container
       // step: "reverse properties only support set- and index-
       // containers" — CK_None also covers the bare "@set" marker (see
       // container_kind's doc comment); any other container_kind sharing
       // a "@reverse" is an invalid reverse property (toRdf/er17: a
       // @reverse term declaring "@container": "@list").
       if not (contk = CK_None || contk = CK_Index) then None
       else
       let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                  td_reverse = true; td_language = langf; td_direction = dirf; td_index = idxf;
                  td_scoped_context = jldctx_wrap_scoped ac ctxf; td_protected = protected; td_prefix = prefix_flag } in
       (match jldctx_resolve_redefine ac key td override_protected with
        | Some final_td -> Some ({ ac with ac_terms = (key, final_td) :: ac.ac_terms })
        | None -> None)
     | (None, None) ->
       // No explicit @id/@reverse: the term's OWN mapping is derived
       // from its NAME via the colon-prefix / slash / @type / vocab
       // fallback chain ONLY (JSON-LD 1.1 API Create Term Definition's
       // tail branches) — NEVER via "full term substitution" (looking
       // `key` up as an ALREADY-DEFINED term, which expand_iri_gen's
       // vocab-relative branch also does, for expanding ordinary
       // VALUES). Strip any EXISTING entry for `key` before expanding
       // so a redefinition-without-@id never resolves through its own
       // stale, about-to-be-replaced mapping.
       (match jldctx_expand_iri_ctx ({ ac with ac_terms = jldctx_remove_term ac.ac_terms key }) key true with
        | None -> None
        | Some iri ->
          let td = { td_iri = iri; td_type_mapping = typef; td_container = contk;
                     td_reverse = false; td_language = langf; td_direction = dirf; td_index = idxf;
                     td_scoped_context = jldctx_wrap_scoped ac ctxf; td_protected = protected; td_prefix = prefix_flag } in
          (match jldctx_resolve_redefine ac key td override_protected with
           | Some final_td -> Some ({ ac with ac_terms = (key, final_td) :: ac.ac_terms })
           | None -> None)))

// ================================================================
// Top level: process an inline @context value (object, array, string, or
// null) against an active context. override_protected: true only for a
// property-/type-scoped context application (JSONLD.Expand); an ordinary
// node object's own inline "@context" member always passes false.
// ================================================================

// The six "special" context-object keywords the JSON-LD 1.1 API
// Context Processing algorithm updates BEFORE any ordinary term
// definition is processed ("We first update the base IRI, the default
// base direction, the default language, context propagation, the
// processing mode, and the vocabulary mapping by processing six
// specific keywords: @base, @direction, @language, @propagate,
// @version, and @vocab. These are handled before any other entries in
// the local context because they affect how the other entries are
// processed"). Used only by the "@import" merge below
// (jldctx_merge_import / the @import branch of context_process):
// ordinary (non-@import) context objects here still process fields in
// literal JSON order, a narrower simplification that already matches
// every other fixture in this suite (test authors always write these
// keywords first in an ordinary context object); @import is the one
// construct that can introduce a term definition TEXTUALLY BEFORE a
// keyword that must, per spec, still take effect first (toRdf/so09:
// the imported context's own "term" needs the CONTAINING context's
// LATER-written "@vocab" override already in place before "term" is
// resolved).
let jldctx_is_special_context_key (k:string) : bool =
  k = "@base" || k = "@vocab" || k = "@language" || k = "@direction" ||
  k = "@propagate" || k = "@version"

let rec jldctx_partition_special (fields:list (string & json_val))
  : Tot (list (string & json_val) & list (string & json_val)) (decreases fields) =
  match fields with
  | [] -> ([], [])
  | (k, v) :: rest ->
    let (sp, ord) = jldctx_partition_special rest in
    if jldctx_is_special_context_key k then ((k, v) :: sp, ord) else (sp, (k, v) :: ord)

// "@import" (JSON-LD 1.1 API §4.1: "Set context to the result of
// merging context into import context, replacing common entries with
// those from context" — a plain key-level union, with the CONTAINING
// (local) context's own entry winning on collision): every
// imported_fields entry whose key is ALSO present in local_fields is
// dropped (local_fields' own copy is the one that survives), then
// local_fields is appended — toRdf/so08/so09/so10/so11's "the
// containing context is merged into the source context".
let rec jldctx_merge_import (imported_fields local_fields:list (string & json_val))
  : Tot (list (string & json_val)) (decreases imported_fields) =
  match imported_fields with
  | [] -> local_fields
  | (k, v) :: rest ->
    if List.Tot.existsb (fun (kv:(string & json_val)) -> fst kv = k) local_fields
    then jldctx_merge_import rest local_fields
    else (k, v) :: jldctx_merge_import rest local_fields

// Forward-reference pre-pass (JSON-LD 1.1 API Create Term Definition's
// `defined` map: "If the prefix is an entry in local context, then its
// term definition must first be created, through recursion, before
// continuing" — full support needs recursive dependency resolution
// with cycle detection, which this module does not implement; this is
// a narrow approximation covering the overwhelmingly common case). A
// plain SIMPLE-STRING-FORM term/prefix declaration (e.g. "ex":
// "http://example.org/") is pre-registered into `ac` BEFORE the main
// left-to-right field pass, so an EARLIER field in the SAME context
// object that uses it as a compact-IRI prefix resolves correctly
// (toRdf/t0034 "context properties reordering": "link": {"@id":
// "ex:link"} appears before "ex" is defined; toRdf/e007 "date
// type-coercion": "ex:date": {"@type": "xsd:dateTime"} appears before
// "xsd" is defined). Only NEW keys (not already in `ac.ac_terms`) are
// previewed — never shadows an existing (possibly protected) entry
// during the preview window. The main pass still runs afterward and
// OVERWRITES each preview entry at its own textual position with the
// fully-validated definition (respecting @protected, redefinition-
// compatibility, the cyclic/self-consistency checks above, etc.) — the
// preview is purely an early-availability shim, never authoritative.
// Object-form term defs (which can themselves depend on further
// not-yet-defined terms) are NOT previewed — the general recursive
// case remains an open gap.
let rec jldctx_preview_prefixes (ac:active_context) (fields:list (string & json_val))
  : Tot active_context (decreases fields) =
  match fields with
  | [] -> ac
  | (k, JString s) :: rest ->
    if jldctx_actual_keyword k || jldctx_keyword_lookalike k || jldctx_keyword_lookalike s
       || jldctx_is_keyword k || k = "" || Some? (jldctx_find_term ac.ac_terms k)
    then jldctx_preview_prefixes ac rest
    else
      (match jldctx_expand_iri_ctx ac s true with
       | None -> jldctx_preview_prefixes ac rest
       | Some iri ->
         if jldctx_is_keyword iri then jldctx_preview_prefixes ac rest
         else
           let td = { td_iri = iri; td_type_mapping = None; td_container = CK_None;
                      td_reverse = false; td_language = None; td_direction = None; td_index = None;
                      td_scoped_context = None; td_protected = false;
                      td_prefix = jldctx_ends_gen_delim iri } in
           jldctx_preview_prefixes ({ ac with ac_terms = (k, td) :: ac.ac_terms }) rest)
  | _ :: rest -> jldctx_preview_prefixes ac rest

// fuel: remote-fetch depth budget (jld_remote_context_fuel at every
// external entry point — see apply_context_with_propagate /
// jldctx_apply_type_scoped below); decremented ONLY on an actual fetch
// (JString branch, "@import" branch), never on ordinary inline
// recursion — so `%[fuel; ctx]` / `%[fuel; items]` below decrease via
// their SECOND (structural) component for every inline call, exactly
// as the pre-remote-loading version did via plain `decreases ctx` /
// `decreases items`, and via the FIRST component only when a fetch
// actually consumes depth. visited: absolute IRIs already fetched on
// this chain (cycle guard — see jldctx_fetch_remote_context's callers).
let rec context_process (ac:active_context) (ctx:json_val) (override_protected:bool)
                         (fuel:nat) (visited:list string)
  : Tot (option active_context) (decreases %[fuel; ctx]) =
  match ctx with
  | JNull ->
    // JSON-LD 1.1 API Context Processing, resetting the active context
    // by setting it to null: "initialize result ... setting both base
    // IRI and original base URL to the value of original base URL in
    // active context" (toRdf/te060 "context completely reset" — the
    // reset restores the DOCUMENT's base, it does not merely clear it —
    // see ac_original_base's doc comment for the CONTRASTING "@base":
    // null member-level behavior, which stays a plain clear).
    if (not override_protected) && jldctx_any_protected ac.ac_terms then None
    else Some ({ ac with ac_terms = []; ac_vocab = None; ac_language = None;
                 ac_base = ac.ac_original_base })
  | JString s ->
    // A remote context reference (JSON-LD 1.1 API §4.1's dereference
    // step). fuel = 0 or a repeat IRI (cycle) is an honest failure.
    if fuel = 0 then None
    else
      (match jldctx_resolve_context_iri ac s with
       | None -> None
       | Some resolved ->
         if List.Tot.mem resolved visited then None
         else
           (match jldctx_fetch_remote_context resolved with
            | None -> None
            | Some inner ->
              // The fetched document's content is read with ac_doc_url
              // updated to ITS OWN resolved URL (tc031's second hop: a
              // scoped context found INSIDE this document resolves
              // relative to it, not the original document) — then
              // RESTORED on the result so sibling context-array entries
              // / fields (processed after this one returns) keep
              // resolving against whatever document THEY were written
              // in.
              (match context_process ({ ac with ac_doc_url = Some resolved }) inner
                       override_protected (fuel - 1) (resolved :: visited) with
               | None -> None
               | Some ac' -> Some ({ ac' with ac_doc_url = ac.ac_doc_url }))))
  | JArray items -> context_process_array ac items override_protected fuel visited
  | JObject fields ->
    (match jldctx_extract_import fields with
     | (None, _) ->
       let ac_preview = jldctx_preview_prefixes ac fields in
       context_process_fields ac_preview fields (jldctx_scan_bool_key fields "@protected" false) override_protected fuel visited
     | (Some importref, restfields) ->
       // "@import" (JSON-LD 1.1 API §4.1 "Import"): fetch the imported
       // context, MERGE its fields with this object's own remaining
       // members (local replacing imported on key collision —
       // jldctx_merge_import), then process the merged set as ONE
       // context object — special keywords (@base/@vocab/@language/
       // @direction/@propagate/@version, wherever they came from) FIRST,
       // ordinary term definitions SECOND (jldctx_partition_special) —
       // toRdf/so08/so09/so10/so11's "the containing context is merged
       // into the source context" (so09: the imported "term" must
       // resolve against the CONTAINING context's own later "@vocab",
       // which a naive "process import fully, then fold local fields on
       // top" two-pass approach gets wrong, since the imported term
       // would already be resolved against the OLD vocab by the time the
       // local @vocab override is seen).
       // 1.1-only ("If context has an @import entry: if processing mode
       // is json-ld-1.0, an invalid context entry error has been
       // detected" — toRdf/tso01).
       if ac.ac_mode10 then None
       else if fuel = 0 then None
       else
         (match jldctx_resolve_context_iri ac importref with
          | None -> None
          | Some resolved ->
            if List.Tot.mem resolved visited then None
            else
              (match jldctx_fetch_remote_context resolved with
               | None -> None
               // "@import" (unlike an ordinary remote JString context)
               // MUST reference a document whose "@context" is a single
               // context OBJECT — not an array, not a further string
               // reference (JSON-LD 1.1 API §4.1: "If the top-level
               // element ... is not a valid remote context, an invalid
               // remote context has been detected" — the toRdf so13
               // "@import can only reference a single context" negative).
               | Some imported_ctx ->
                 (match imported_ctx with
                  | JObject imported_fields ->
                    let merged = jldctx_merge_import imported_fields restfields in
                    let ac_preview = jldctx_preview_prefixes ac merged in
                    let (special, ordinary) = jldctx_partition_special merged in
                    let default_protected = jldctx_scan_bool_key merged "@protected" false in
                    // fuel - 1 (not fuel) on both calls below: `special`/
                    // `ordinary` are freshly-built lists (via
                    // jldctx_merge_import / jldctx_partition_special),
                    // not direct pattern-matched subterms of `fields`, so
                    // the termination checker cannot see them as
                    // structurally smaller; the already-spent fetch's
                    // fuel decrement covers both calls too (this whole
                    // branch only runs once per JObject, so it costs
                    // only 1 extra unit of the generous 32-deep budget).
                    (match context_process_fields ac_preview special default_protected override_protected (fuel - 1) (resolved :: visited) with
                     | None -> None
                     | Some ac_special ->
                       context_process_fields ac_special ordinary default_protected override_protected (fuel - 1) (resolved :: visited))
                  | _ -> None))))
  | _ -> None

and context_process_array (ac:active_context) (items:list json_val) (override_protected:bool)
                           (fuel:nat) (visited:list string)
  : Tot (option active_context) (decreases %[fuel; items]) =
  match items with
  | [] -> Some ac
  | hd :: tl ->
    (match context_process ac hd override_protected fuel visited with
     | None -> None
     | Some ac1 -> context_process_array ac1 tl override_protected fuel visited)

// fuel/visited: threaded (unchanged) only to keep this function's
// decreases metric shape %[fuel; fields] comparable with context_process
// / context_process_array's within the shared mutual-recursion group —
// context_process_one_field's OWN remote fetches (the eager scoped-
// context validation, toRdf/tc033) use fuel - 1 / visited freshly at
// THAT call site, not decremented here — an ordinary field consumes none
// of ITS caller's remote-fetch depth budget merely by being visited.
and context_process_fields (ac:active_context) (fields:list (string & json_val))
                           (default_protected:bool) (override_protected:bool)
                           (fuel:nat) (visited:list string)
  : Tot (option active_context) (decreases %[fuel; fields]) =
  match fields with
  | [] -> Some ac
  | (key, value) :: rest ->
    (match context_process_one_field ac key value default_protected override_protected fuel visited with
     | None -> None
     | Some ac1 -> context_process_fields ac1 rest default_protected override_protected fuel visited)

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
// fuel/visited: threaded UNCHANGED from context_process_fields (processing
// one field consumes none of the remote-fetch depth budget by itself) —
// needed ONLY so the ordinary-term-definition tail below can eagerly
// VALIDATE a just-defined term's own scoped "@context" (toRdf/tc033 —
// see that branch's comment), which is why this function now lives in
// the SAME mutually-recursive group as context_process itself instead of
// being a plain leaf `let`.
and context_process_one_field (ac:active_context) (key:string) (value:json_val)
                               (default_protected:bool) (override_protected:bool)
                               (fuel:nat) (visited:list string)
  : Tot (option active_context) (decreases %[fuel; value]) =
  if key = "@base" then
    (match value with
     | JString s ->
       // toRdf/t0122-t0125 "IRI Resolution (2)-(5)": an ALREADY-ABSOLUTE
       // @base value is adopted VERBATIM, not merged against the
       // previous base via full RFC 3986 reference resolution — running
       // it through jldctx_resolve/resolve_iri would apply that
       // algorithm's remove_dot_segments step even though R (the new
       // @base string) already carries its own scheme, silently
       // stripping a deliberate "./" the fixtures keep (e.g. "@base":
       // "http://a/bb/ccc/./d;p?q" must stay exactly that, not collapse
       // to ".../ccc/d;p?q"). Only a genuinely RELATIVE @base value
       // (no scheme of its own) gets resolved against the previous base.
       let resolved = if is_iri s then s
                      else (match ac.ac_base with
                            | Some b -> jldctx_resolve b s
                            | None -> s) in
       Some ({ ac with ac_base = Some resolved })
     | JNull -> Some ({ ac with ac_base = None })
     | _ -> None)
  else if key = "@vocab" then
    (match value with
     | JString s ->
       // JSON-LD 1.1 API §4.1.2: the vocab mapping value is itself
       // IRI-expanded vocab-relative with document-relative fallback —
       // a term or compact IRI resolves through the ACTIVE context
       // (toRdf/e124 "ex:ns/", e125 "ex"), a relative reference with an
       // EXISTING vocab concatenates onto it (e111/e112 "./rel2#"), and
       // otherwise resolves against @base per RFC 3986 (e092 "" -> the
       // base itself; e110 "/relative").
       (match jldctx_expand_iri_ctx ac s true with
        | Some iri -> Some ({ ac with ac_vocab = Some iri })
        | None ->
          (match ac.ac_base with
           | Some b -> Some ({ ac with ac_vocab = Some (jldctx_resolve b s) })
           | None -> None))
     | JNull -> Some ({ ac with ac_vocab = None })
     | _ -> None)
  else if key = "@language" then
    (match value with
     | JString s -> Some ({ ac with ac_language = Some s })
     | JNull -> Some ({ ac with ac_language = None })
     | _ -> None)
  else if key = "@direction" then
    (match value with
     | JString s ->
       if s = "ltr" || s = "rtl" then Some ({ ac with ac_direction = Some s }) else None
     | JNull -> Some ({ ac with ac_direction = None })
     | _ -> None)
  else if key = "@version" then
    // JSON-LD 1.1 API §4.1.8: the @version member's value MUST be the
    // number 1.1 exactly (toRdf/ep03: "@version": 1.0 is an "invalid
    // @version value" error); AND, separately, "@version": 1.1 while
    // the processing mode is explicitly json-ld-1.0 is its own
    // "processing mode conflict" error (toRdf/tep02), distinct from the
    // invalid-value case above.
    (match value with
     | JNumber lex ->
       if lex <> "1.1" then None
       else if ac.ac_mode10 then None
       else Some ac
     | _ -> None)
  else if key = "@protected" then
    (match value with JBool _ -> Some ac | _ -> None)
  else if key = "@propagate" then
    // "@propagate" is 1.1-only (JSON-LD 1.1 API §4.1: "If context has an
    // @propagate entry: if processing mode is json-ld-1.0, an invalid
    // context entry error has been detected" — toRdf/tc029).
    if ac.ac_mode10 then None
    else (match value with JBool _ -> Some ac | _ -> None)
  else if key = "@type" then
    // JSON-LD 1.1 API Create Term Definition: redefining the KEYWORD
    // "@type" itself is illegal in 1.0 outright, and even in 1.1 the
    // value MUST be a map containing at least one of — and ONLY —
    // an "@container": "@set" entry and/or an "@protected" entry; an
    // EMPTY map has neither and is itself a keyword-redefinition error
    // (toRdf/ec02 "Term definition on @type with empty map"), and any
    // other shape is the same error (toRdf/ter42 "Keywords may not be
    // redefined in 1.0" once mode10 already catches it, and any
    // 1.1-mode shape violation). toRdf/tpr30 "Keywords may be
    // protected" is the positive case a valid shape must accept.
    //
    // The @type keyword's own container-@set-ness and protected-ness
    // ARE tracked — as an ordinary term_def stored under the literal
    // key "@type" in ac_terms — so a LATER redefinition of the
    // keyword is subject to the exact same protected-term-redefinition
    // rule as any other term (toRdf/tpr32 "Protected @type cannot be
    // overridden": a first context marks @type protected with
    // @container:@set, a second context (also protected, but WITHOUT
    // @container:@set) is a DIFFERENT, hence rejected, redefinition).
    // This is safe to store under an ordinary-term-shaped key: "@type"
    // can never be looked up via jldctx_find_term as an ordinary
    // term (expand_iri_gen returns Some value for any actual keyword
    // BEFORE ever consulting ac_terms), so this pseudo-entry is only
    // ever read back by this very branch.
    if ac.ac_mode10 then None
    else
      (match value with
       | JObject tfields ->
         let non_empty = (match tfields with | [] -> false | _ -> true) in
         let shape_ok =
           non_empty &&
           List.Tot.for_all
             (fun (kv:(string & json_val)) ->
                (fst kv = "@container" && (match snd kv with JString "@set" -> true | _ -> false)) ||
                (fst kv = "@protected" && JBool? (snd kv)))
             tfields in
         if not shape_ok then None
         else
           let has_set = List.Tot.existsb (fun (kv:(string & json_val)) -> fst kv = "@container") tfields in
           let protected = jldctx_scan_bool_key tfields "@protected" false in
           let td = { td_iri = "@type"; td_type_mapping = None;
                      td_container = (if has_set then CK_Type else CK_None);
                      td_reverse = false; td_language = None; td_direction = None;
                      td_index = None; td_scoped_context = None;
                      td_protected = protected; td_prefix = false } in
           (match jldctx_resolve_redefine ac "@type" td override_protected with
            | None -> None
            | Some final_td -> Some ({ ac with ac_terms = ("@type", final_td) :: ac.ac_terms }))
       | _ -> None)
  // A term NAME that is an actual keyword may not be redefined (keyword
  // collision, an error); one that merely LOOKS like a keyword
  // ("@ignoreMe") is ignored with a warning (toRdf/pr34/pr35/e119);
  // at-prefixed names WITHOUT keyword form ("@", "@foo.bar") are
  // ordinary terms and fall through (e119's "allowed" pair).
  else if jldctx_actual_keyword key then None
  else if jldctx_keyword_lookalike key then Some ac
  // JSON-LD 1.1 API Create Term Definition: "If term is the empty
  // string (""), an invalid term definition error has been detected"
  // (toRdf/er52 — a context defining "": {...} alongside an ordinary
  // term).
  else if key = "" then None
  else
    (match value with
     | JNull ->
       // "term": null DECOUPLES the term from @vocab (toRdf/e032): the
       // term is not merely removed (which would re-expose the @vocab
       // fallback at use sites) but pinned to the "@null" sentinel,
       // which JSONLD.Expand's key handling drops (it has keyword form
       // but is not an actual keyword — same drop path as "@ignoreMe").
       (match jldctx_find_term ac.ac_terms key with
        | Some existing ->
          if existing.td_protected && not override_protected then None
          else
            // JSON-LD 1.1 API Create Term Definition: "value is null"
            // still goes through "Create a new term definition,
            // definition, initializing ... protected to protected [the
            // ambient default_protected input]" — a null term is NOT
            // unconditionally unprotected (toRdf/pr28: a context-level
            // "@protected": true default must stick to a "term": null
            // entry too, so a LATER context's redefinition of that same
            // term is rejected as a protected-term redefinition).
            let td = { td_iri = "@null"; td_type_mapping = None; td_container = CK_None;
                       td_reverse = false; td_language = None; td_direction = None; td_index = None;
                       td_scoped_context = None; td_protected = default_protected; td_prefix = false } in
            Some ({ ac with ac_terms = (key, td) :: jldctx_remove_term ac.ac_terms key })
        | None ->
          let td = { td_iri = "@null"; td_type_mapping = None; td_container = CK_None;
                     td_reverse = false; td_language = None; td_direction = None; td_index = None;
                     td_scoped_context = None; td_protected = default_protected; td_prefix = false } in
          Some ({ ac with ac_terms = (key, td) :: ac.ac_terms }))
     | JString s ->
       // A simple-form definition whose VALUE looks like (but is not) a
       // keyword is ignored entirely — the term stays undefined, so its
       // uses fall back to @vocab or get dropped (toRdf/pr36/pr37).
       if jldctx_keyword_lookalike s then Some ac
       // Simple string form is spec sugar for {"@id": s} — the same
       // cyclic-IRI-mapping (jldctx_self_cyclic) and term-self-
       // consistency (jldctx_term_needs_self_check) checks that apply to
       // an explicit object-form "@id" apply here too.
       else if jldctx_self_cyclic ac key s then None
       else
       // JSON-LD 1.1 API Create Term Definition: the id-expansion
       // machinery ("if value contains the entry @id and its value does
       // NOT EQUAL term") is skipped entirely when the string value
       // equals the term's OWN name — "term": "term" falls straight to
       // the colon/slash/@type/vocab fallback, the SAME derivation the
       // (None, None) object-form case uses, and for the SAME reason:
       // it must not resolve through its own stale existing mapping
       // (toRdf/e072: a SECOND context's "term": "term" under a NEW
       // @vocab must re-resolve to vocab+"term", not to the value
       // "term" already carries from an earlier, about-to-be-replaced
       // context). Strip any existing `key` entry only in that
       // self-referencing case — an ordinary alias to a DIFFERENT
       // already-defined term (s <> key) still resolves through it.
       let ac_lookup = if s = key then { ac with ac_terms = jldctx_remove_term ac.ac_terms key } else ac in
       (match jldctx_expand_iri_ctx ac_lookup s true with
        | None -> None
        | Some iri ->
          // 1.1-only, same gating rationale as the object-form arm
          // above (toRdf/te026 is a 1.0-mode positive for the shape
          // this check would otherwise reject); key expanded with its
          // own entry stripped, same preview-pass rationale as there.
          if (not ac.ac_mode10) && jldctx_term_needs_self_check key &&
             jldctx_expand_iri_ctx ({ ac with ac_terms = jldctx_remove_term ac.ac_terms key }) key true <> Some iri then None
          else
          // Simple string form: prefix-capable iff the expanded IRI ends
          // in a gen-delim byte (td_prefix's doc comment).
          let td = { td_iri = iri; td_type_mapping = None; td_container = CK_None;
                     td_reverse = false; td_language = None; td_direction = None; td_index = None;
                     td_scoped_context = None; td_protected = default_protected;
                     td_prefix = jldctx_ends_gen_delim iri } in
          (match jldctx_resolve_redefine ac key td override_protected with
           | Some final_td -> Some ({ ac with ac_terms = (key, final_td) :: ac.ac_terms })
           | None -> None))
     | JObject termfields ->
       // A term definition whose "@reverse" member has keyword FORM
       // (actual keyword or lookalike) is ignored entirely — spec
       // Create Term Definition's @reverse step: warning + return
       // without creating the term (toRdf/pr38/pr39). Checked HERE
       // (before process_term_def_obj) because "ignore the whole
       // definition" and "malformed definition = error" need different
       // return paths.
       let rev_kw =
         List.Tot.existsb
           (fun (kv:(string & json_val)) ->
              fst kv = "@reverse" &&
              (match snd kv with JString rs -> jldctx_keyword_form rs | _ -> false))
           termfields in
       // {"@id": null} pins the term to the "@null" sentinel exactly
       // like "term": null above (toRdf/e032's "university").
       let id_null =
         List.Tot.existsb
           (fun (kv:(string & json_val)) -> fst kv = "@id" && JNull? (snd kv))
           termfields in
       if rev_kw then Some ac
       else if id_null then
         // Same protected-default rule as bare "term": null above
         // (toRdf/pr28's doc comment) — a null IRI mapping still carries
         // default_protected, not an unconditional false.
         (match jldctx_find_term ac.ac_terms key with
          | Some existing ->
            if existing.td_protected && not override_protected then None
            else
              let td = { td_iri = "@null"; td_type_mapping = None; td_container = CK_None;
                         td_reverse = false; td_language = None; td_direction = None; td_index = None;
                         td_scoped_context = None; td_protected = default_protected; td_prefix = false } in
              Some ({ ac with ac_terms = (key, td) :: jldctx_remove_term ac.ac_terms key })
          | None ->
            let td = { td_iri = "@null"; td_type_mapping = None; td_container = CK_None;
                       td_reverse = false; td_language = None; td_direction = None; td_index = None;
                       td_scoped_context = None; td_protected = default_protected; td_prefix = false } in
            Some ({ ac with ac_terms = (key, td) :: ac.ac_terms }))
       else
         // toRdf/tc033 "Unused context with an embedded context error":
         // JSON-LD 1.1 API Context Processing validates a term's OWN
         // scoped "@context" member EAGERLY, at term-definition time —
         // even when the term is never actually USED anywhere in the
         // document (so JSONLD.Expand's apply_property_scoped_context /
         // jldctx_apply_type_scoped never get a chance to run their OWN,
         // later, point-of-use context_process call, which is all that
         // used to validate it before this fix — tc032's twin fixture,
         // where the term IS used, already worked). The validation
         // RESULT is discarded either way (td_scoped_context still
         // stores the RAW value + its doc_url, re-processed fresh at
         // each point of use per propagate/override rules) — only a
         // FAILURE here is load-bearing. fuel = 0 here means "no depth
         // left to even ATTEMPT the validation fetch", an honest failure
         // (mirrors every other fuel=0 branch in this module) rather
         // than silently skipping the check.
         // override_protected = TRUE here (not false): this eager pass
         // exists to catch STRUCTURAL failures (an unresolvable term
         // mapping, a malformed remote reference — tc033's actual
         // failure mode), not to re-enforce protected-term rules ahead
         // of time. The REAL protected-term check already happens
         // correctly at each ACTUAL point of use with the RIGHT
         // override_protected for how the term ends up being used
         // (apply_property_scoped_context always passes true;
         // jldctx_apply_type_scoped always passes false) — using false
         // HERE would reject a scoped context that legitimately clears
         // protected terms via PROPERTY-scoped application (toRdf/pr06
         // "Clear active context of protected terms from a term",
         // pr08-pr16 and others: an unused term's scoped context whose
         // ONLY problem, under false, is touching a protected term the
         // way property-scoped application is EXPLICITLY allowed to)
         // before that term is ever actually applied.
         if fuel = 0 then None
         else
           (match process_term_def_obj ac key termfields default_protected override_protected with
            | None -> None
            | Some ac' ->
              (match jldctx_find_term ac'.ac_terms key with
               | Some td ->
                 (match td.td_scoped_context with
                  // A REMOTE (JString) scoped-context reference is
                  // skipped here — deliberately NOT run through the
                  // "actually chase it" eager check. toRdf/te126/te127/
                  // te128 ("a scoped context may include itself
                  // recursively [...] no exception is raised") each
                  // define a term whose scoped context is a JString
                  // pointing back at the SAME document it is defined in
                  // (directly, indirectly, or via a shared document with
                  // ANOTHER term). At the REAL point of use, this is
                  // harmless: apply_property_scoped_context /
                  // jldctx_apply_type_scoped re-derive the scoped
                  // context fresh only when the term is ACTUALLY used as
                  // a key/type value, so a self-reference only recurses
                  // as many times as the DOCUMENT itself actually nests
                  // that property — never infinitely. EAGERLY "running"
                  // the fetch to completion right here has no such
                  // natural bound: with an honest cycle guard (`visited`
                  // carrying this document forward) a legitimate self-
                  // reference is wrongly rejected as a cycle; with a
                  // FRESH `visited` per validation attempt (so the self-
                  // reference itself is never caught as a cycle) the
                  // eager recursion has NO way to terminate except by
                  // exhausting `fuel`, an honest but wrong failure. Since
                  // every remote-document TARGET of a JString scoped
                  // context is separately validated by ITS OWN
                  // term-definition sites when read (a genuinely invalid
                  // remote scoped context still surfaces as an "invalid
                  // scoped context" error the moment SOMETHING eagerly
                  // validatable inside it is itself checked, or the
                  // first time the term is actually applied), the
                  // narrower INLINE-only eager check below already
                  // covers tc033's actual failure mode (an inline
                  // object, never a remote reference).
                  | Some (JString _, _) -> Some ac'
                  | Some (raw, def_doc_url) ->
                    if Some? (context_process ({ ac' with ac_doc_url = def_doc_url }) raw
                                true (fuel - 1) visited)
                    then Some ac'
                    else None
                  | None -> Some ac')
               | None -> Some ac'))
     | _ -> None)


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
  match context_process ac ctxval override_protected jld_remote_context_fuel [] with
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

// ac0: FIXED snapshot of the active context as it stood before ANY
// type-scoped modification — the JSON-LD 1.1 API's "type-scoped context"
// (Expansion algorithm step "Initialize type-scoped context to active
// context" — this variable name is intentionally the SAME across every
// recursive call below, never the evolving accumulator). Every type
// NAME's own term definition (hence whether IT carries a scoped context)
// is looked up against this fixed ac0, never against ac_acc — otherwise
// an EARLIER type's scoped context can nullify or redefine the term
// entries that a LATER type's own name needs to resolve through (toRdf/
// c018: "Bar"'s scoped context is `[null, {"prop": ...}]` — the leading
// null wipes ac_terms; looking "Foo" up in that wiped accumulator instead
// of ac0 would silently skip Foo's scoped context entirely, which is
// exactly the bug this two-parameter shape prevents).
// ac_acc: the evolving accumulator ("active context" in the spec text)
// that each type's scoped context is folded ONTO, in ascending
// lexicographic order of the type names (toRdf/c011/c018: later-sorted
// types shadow earlier ones' term redefinitions in the final result).
let rec jldctx_apply_type_scoped (ac0:active_context) (ac_acc:active_context) (types:list string) (any_non_propagating:bool)
  : Tot (option (active_context & bool)) (decreases types) =
  match types with
  | [] -> Some (ac_acc, any_non_propagating)
  | t :: rest ->
    (match jldctx_find_term ac0.ac_terms t with
     | Some td ->
       (match td.td_scoped_context with
        | Some (scoped, def_doc_url) ->
          // override_protected is FALSE here (NOT true): the JSON-LD 1.1
          // API Expansion algorithm's @type-key loop invokes the Context
          // Processing algorithm passing only active context, the type's
          // local context, base URL, and false for propagate — override
          // protected is NOT mentioned at that call site, so it takes its
          // DEFAULT value, which the Context Processing algorithm
          // overview states is false. Only PROPERTY-scoped context
          // application (JSONLD.Expand.apply_property_scoped_context)
          // explicitly passes true for override protected — type-scoped
          // contexts get no blanket override right; a type-scoped context
          // may still redefine a protected term when the new definition
          // is IDENTICAL (term_defs_compatible, checked inside
          // jldctx_resolve_redefine regardless of
          // override_protected), but a DIFFERENT redefinition, or a null
          // reset that would drop protection, is now an honest failure
          // (toRdf/pr17, pr18, pr20, pr21 — all Negative "protected
          // terms must not be silently overridden by a type-scoped
          // context" fixtures that this blanket `true` used to pass
          // incorrectly).
          (match context_process ({ ac_acc with ac_doc_url = def_doc_url }) scoped false jld_remote_context_fuel [] with
           | None -> None
           | Some ac1 ->
             let propagate = jldctx_scan_propagate scoped false in
             jldctx_apply_type_scoped ac0 ac1 rest (any_non_propagating || not propagate))
        | None -> jldctx_apply_type_scoped ac0 ac_acc rest any_non_propagating)
     | None -> jldctx_apply_type_scoped ac0 ac_acc rest any_non_propagating)

// raw_types: the @type value's string entries AS WRITTEN (not yet
// IRI-expanded — term lookup for type-scoped contexts happens by term
// NAME against ac0, per spec). ac0: the active context BEFORE any
// type-scoped modification (after this node's own inline @context, if
// any, but before @type is consulted) — passed as BOTH arguments to
// jldctx_apply_type_scoped's initial call since the accumulator starts
// out equal to the fixed snapshot.
let apply_type_scoped_contexts (ac0:active_context) (raw_types:list string) : option active_context =
  match jldctx_apply_type_scoped ac0 ac0 (jldctx_sort_strings raw_types) false with
  | None -> None
  | Some (ac1, any_non_propagating) ->
    Some (if any_non_propagating then { ac1 with ac_previous = Some ac0 } else ac1)
