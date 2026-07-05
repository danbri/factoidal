module VC.Credential

// ============================================================================
// Verifiable Credentials (VC) Data Model 2.0 — structural conformance.
// Stage 1 of the VC program
// (docs/designissues/2026-07-05-vc-program-plan.md): a decoder + checker
// over an ALREADY-PARSED Parser.JSON tree (Parser.JSON.parse_json), the
// same "decode a json_val, no fuel needed beyond one level of embedding"
// idiom ShEx.Schema.fst uses for ShExJ — except this AST has no mutually
// recursive shapeExpr/tripleExpr group, so no fuel threading is needed at
// all: every check here is either non-recursive or structurally recursive
// over an ordinary `list json_val` (List.Tot's native decreases-metric).
//
// SCOPE (Stage 1 only — "required-property + type-membership checks",
// per the plan's stage table row 1): this module does NOT do general
// JSON-LD context processing (no term resolution, no @vocab expansion,
// no context-defined type redefinition). "@context handling" here means
// exactly the FIXED SENTINEL check the plan calls for: the base VC 2.0
// context IRI (`vc_base_context`) must be present and FIRST in the
// @context list — the same requirement VCDM 2.0 §4.1 states in prose
// ("The first value MUST be..."), decoded structurally rather than via
// JSON-LD context resolution.
//
// What IS checked (measured against the vendored `tests/input/*.json`
// fixtures — see bin/vc-runner/vc_runner.ml):
//   - @context: present; array (or bare string) shape; every entry is a
//     JString/JObject/JNull (rejects a bare JNumber/JBool entry, e.g.
//     `tests/input/credential-context-combo4-fail.json`) and every
//     JString entry "looks like an IRI" (contains ':', no raw space —
//     rejects the corpus's deliberately-mangled
//     "https ://not-a-url/..." entries, e.g. `credential-context-
//     combo3-fail.json`); the FIRST entry must equal `vc_base_context`
//     exactly (catches `credential-no-context-fail-or-inject.json`'s
//     sibling `presentation-missing-base-context-fail.json`, and
//     `presentation-context-order-fail.json`'s out-of-order base
//     context).
//   - type: present (array-of-string or bare string); must contain, as a
//     member (order-independent), "VerifiableCredential" or
//     "VerifiablePresentation" — the base-type membership check the
//     plan's Stage 1 row names directly.
//   - credentialSubject (documents whose type includes
//     "VerifiableCredential" only): present, and non-empty — a JObject
//     with >=1 field, or a JArray of such objects (every element
//     non-empty, not just one). Catches `credential-no-subject-fail`,
//     `credential-subject-no-claims-fail`, `credential-subject-
//     multiple-empty-fail`, and (empirically, per that fixture's actual
//     shape rather than its filename) `credential-no-issuer-fail`.
//   - verifiableCredential (documents whose type includes
//     "VerifiablePresentation" only, field optional): if present, must
//     be a JArray (or a lone JObject) of JObjects — a bare JString entry
//     fails immediately (`presentation-vc-as-string-fail.json`, a raw
//     JWT string in place of a credential object). Each JObject entry
//     is either an ENVELOPE (`type = "EnvelopedVerifiableCredential"`,
//     checked only for a present `id`) or a full embedded credential
//     (type contains "VerifiableCredential", recursively checked via
//     this same @context/type/credentialSubject rule set).
//
// EXPLICITLY DEFERRED to Stage 2 (do not silently guess at these —
// see the plan's stage table row 2 and the module plan's
// VC.Credential bullet):
//   - issuer presence/shape. Measured empirically against the corpus
//     (2026-07-05): a majority of `-ok`-suffixed `tests/input/*.json`
//     fixtures (including the baseline `credential-ok.json` itself)
//     omit `issuer` entirely — these fixtures test one narrow property
//     each and evidently rely on an issue/verify wrapping step this
//     offline runner does not have. Requiring issuer presence here
//     would produce ~30 systematic false FAILs; the issuer-shape
//     fixtures (`credential-issuer-no-url-fail.json` and siblings) are
//     left as a coherent Stage 2 unit instead of cherry-picked in.
//   - validFrom/validUntil ordering (reuses XSD.Datatypes per the plan).
//   - credentialStatus/credentialSchema/termsOfUse/evidence/
//     refreshService inner-shape checks (each has its own id/type
//     sub-requirements — a `-fail` fixture per missing sub-field).
//   - top-level `id` cardinality/format, and `holder` shape
//     (presentation-holder-*-fail/-ok) — both are optional-field
//     shape checks in the same family as issuer, deferred together.
//   - context-driven type redefinition/mapping (`credential-redef-
//     type*-fail`, `credential-type-mapped-*`, `credential-type-
//     unmapped-fail`) — needs real JSON-LD term resolution, which
//     Stage 1 explicitly does not implement; these fixtures score
//     PASS here (a known, documented Stage 1 miss, not a bug).
//
// Reference: VC Data Model 2.0, W3C Recommendation 2025-05-15
// (https://www.w3.org/TR/vc-data-model-2.0/). Corpus:
// third_party/testing/vc (w3c/vc-data-model-2.0-test-suite),
// tests/input/*.json (120 fixtures, `-ok`/`-fail` filename-suffixed;
// a handful of exceptions — `-fail-or-inject` and unsuffixed
// self-asserted-vc fixtures — are ambiguous verdicts the runner skips,
// see that file's header comment).
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.JSON

// ================================================================
// Small local string helpers (dependency-free of SPARQL11.Algebra —
// same "lightweight leaf module" discipline ShEx.Schema.fst documents
// for itself; this module only needs "does this string contain a
// given character", not general substring search).
// ================================================================

let rec vc_chars_contain (cs : list FStar.Char.char) (target : FStar.Char.char)
  : Tot bool (decreases cs) =
  match cs with
  | [] -> false
  | c :: tl -> c = target || vc_chars_contain tl target

let vc_string_contains_char (s : string) (target : FStar.Char.char) : bool =
  vc_chars_contain (String.list_of_string s) target

// A string "looks like an IRI reference" for this module's cheap
// well-formedness purposes: it contains a ':' (scheme/URN/DID
// delimiter) and no raw space. This is NOT RFC 3986 validation — it
// exists only to catch this corpus's deliberately-mangled fixtures
// (every "-not-a-url-fail"/"-nonurl-fail" fixture in the corpus uses
// the pattern "https ://not-a-url/..." — an embedded space — as its
// mangling device) without pulling in a full IRI parser for a Stage 1
// sentinel/shape check.
let vc_looks_like_iri (s : string) : bool =
  vc_string_contains_char s (FStar.Char.char_of_int 0x3A) (* ':' *) &&
  not (vc_string_contains_char s (FStar.Char.char_of_int 0x20)) (* ' ' *)

// ================================================================
// Verdict.
// ================================================================

type vc_verdict =
  | VC_Pass : vc_verdict
  | VC_Fail : string -> vc_verdict

// ================================================================
// @context: fixed base-context sentinel + entry-shape check.
// ================================================================

let vc_base_context : string = "https://www.w3.org/ns/credentials/v2"

// A single @context list entry: a JString must look like an IRI, a
// JObject (inline context definition) or JNull (per the JSON-LD
// grammar's own @context list-entry shape) is always acceptable at
// this structural level.
let vc_context_entry_ok (v : json_val) : bool =
  match v with
  | JString s -> vc_looks_like_iri s
  | JObject _ -> true
  | JNull -> true
  | _ -> false

let vc_check_context (v : json_val) : vc_verdict =
  match json_get_field "@context" v with
  | None -> VC_Fail "missing @context"
  | Some (JString s) ->
    if s = vc_base_context then VC_Pass
    else VC_Fail "bare-string @context must equal the base VC 2.0 context IRI"
  | Some (JArray items) ->
    (match items with
     | [] -> VC_Fail "@context is an empty array"
     | first :: _ ->
       if not (List.Tot.for_all vc_context_entry_ok items) then
         VC_Fail "an @context entry is neither a well-formed IRI string, an object, nor null"
       else
         (match first with
          | JString s ->
            if s = vc_base_context then VC_Pass
            else VC_Fail "the base VC 2.0 context IRI must be the FIRST @context entry"
          | _ -> VC_Fail "the first @context entry must be the base VC 2.0 context IRI string"))
  | Some _ -> VC_Fail "@context must be a string or an array"

// ================================================================
// type: base-type membership check.
// ================================================================

let rec vc_string_items (items : list json_val) : Tot (list string) (decreases items) =
  match items with
  | [] -> []
  | JString s :: tl -> s :: vc_string_items tl
  | _ :: tl -> vc_string_items tl

// Decodes the "type" field into a plain string list: a JArray keeps
// only its JString elements (a non-string element simply isn't a type
// name — it will not satisfy membership below, so a malformed element
// still surfaces as a failure via vc_check_type_membership rather than
// being silently accepted); a bare JString is a one-element list (the
// JSON-LD-coercion shape `"type": "VerifiableCredential"`, seen in the
// corpus at `credential-proof-missing-type-fail.json`); an absent or
// otherwise-shaped field decodes to the empty list, which fails the
// membership check below exactly like an explicit empty array does.
let vc_decode_type_list (v : json_val) : list string =
  match json_get_field "type" v with
  | Some (JArray items) -> vc_string_items items
  | Some (JString s) -> [s]
  | _ -> []

let vc_credential_type : string = "VerifiableCredential"
let vc_presentation_type : string = "VerifiablePresentation"
let vc_enveloped_credential_type : string = "EnvelopedVerifiableCredential"

let vc_check_type_membership (v : json_val) : vc_verdict =
  let types = vc_decode_type_list v in
  if List.Tot.mem vc_credential_type types || List.Tot.mem vc_presentation_type types
  then VC_Pass
  else VC_Fail "type array/string is missing the base VerifiableCredential/VerifiablePresentation type"

// ================================================================
// credentialSubject: required (credential-kind documents only) and
// non-empty.
// ================================================================

let vc_object_non_empty (v : json_val) : bool =
  match v with
  | JObject fields -> List.Tot.length fields > 0
  | _ -> false

let vc_check_credential_subject (v : json_val) : vc_verdict =
  match json_get_field "credentialSubject" v with
  | None -> VC_Fail "missing credentialSubject"
  | Some (JObject fields) ->
    if List.Tot.length fields > 0 then VC_Pass
    else VC_Fail "credentialSubject has no claims (empty object)"
  | Some (JArray []) -> VC_Fail "credentialSubject array is empty"
  | Some (JArray items) ->
    if List.Tot.for_all vc_object_non_empty items then VC_Pass
    else VC_Fail "credentialSubject array contains an empty-object entry"
  | Some _ -> VC_Fail "credentialSubject must be an object or an array of objects"

// ================================================================
// Top-level document check: @context + type, plus credentialSubject
// when the document is credential-shaped.
// ================================================================

// The three Stage-1 checks shared by a top-level document AND a fully
// embedded credential (a presentation's `verifiableCredential` entry
// that is NOT an envelope) — see vc_check_embedded_item below. Kept as
// one function so both call sites can never drift apart.
let vc_check_credential_shaped (v : json_val) : vc_verdict =
  match vc_check_context v with
  | VC_Fail r -> VC_Fail r
  | VC_Pass ->
    match vc_check_type_membership v with
    | VC_Fail r -> VC_Fail r
    | VC_Pass ->
      let types = vc_decode_type_list v in
      if List.Tot.mem vc_credential_type types
      then vc_check_credential_subject v
      else VC_Pass

// ================================================================
// verifiableCredential: presentation-kind documents only, field
// optional. Each entry is either an envelope (opaque signed data,
// checked only for a present `id`) or a full embedded credential
// (recursively checked via vc_check_credential_shaped).
// ================================================================

let vc_check_embedded_item (v : json_val) : vc_verdict =
  match v with
  | JObject _ ->
    let types = vc_decode_type_list v in
    if List.Tot.mem vc_enveloped_credential_type types then
      (match json_get_string "id" v with
       | Some _ -> VC_Pass
       | None -> VC_Fail "enveloped verifiableCredential entry is missing id")
    else if List.Tot.mem vc_credential_type types then
      vc_check_credential_shaped v
    else
      VC_Fail "verifiableCredential entry has neither VerifiableCredential nor EnvelopedVerifiableCredential type"
  | _ -> VC_Fail "verifiableCredential entry must be a JSON object"

let rec vc_check_embedded_list (items : list json_val) : Tot vc_verdict (decreases items) =
  match items with
  | [] -> VC_Pass
  | hd :: tl ->
    (match vc_check_embedded_item hd with
     | VC_Fail r -> VC_Fail r
     | VC_Pass -> vc_check_embedded_list tl)

let vc_check_embedded_credentials (v : json_val) : vc_verdict =
  match json_get_field "verifiableCredential" v with
  | None -> VC_Pass
  | Some field_val ->
    (match field_val with
     | JArray items -> vc_check_embedded_list items
     | JObject _ -> vc_check_embedded_item field_val
     | _ -> VC_Fail "verifiableCredential must be an object or an array of objects")

// ================================================================
// Top-level entry point.
// ================================================================

// Checks a fully decoded top-level VC/VP JSON document: @context
// sentinel + type membership always; credentialSubject when the
// document is credential-shaped; the embedded verifiableCredential
// list when the document is presentation-shaped (both may apply to
// the same document — the checks are independent, matching the
// corpus's own type-list-driven dispatch rather than an exclusive
// either/or).
let vc_check_document (v : json_val) : vc_verdict =
  match vc_check_credential_shaped v with
  | VC_Fail r -> VC_Fail r
  | VC_Pass ->
    let types = vc_decode_type_list v in
    if List.Tot.mem vc_presentation_type types
    then vc_check_embedded_credentials v
    else VC_Pass

// Convenience: parse raw JSON text and check it in one call. None on
// unparseable JSON or a non-object top level (a VC/VP document is
// always a JSON object per VCDM 2.0 §4.1) is folded into VC_Fail so
// callers get one verdict type rather than an option-of-verdict.
let vc_check_from_string (input : string) : vc_verdict =
  match parse_json input with
  | None -> VC_Fail "input is not well-formed JSON"
  | Some v ->
    (match v with
     | JObject _ -> vc_check_document v
     | _ -> VC_Fail "top-level JSON value must be an object")
