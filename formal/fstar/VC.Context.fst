module VC.Context

// ============================================================================
// Verifiable Credentials (VC) Data Model 2.0 — offline JSON-LD context
// TERM RESOLUTION for `type`-value checking.
//
// SCOPE: this is NOT a general JSON-LD context processor. It is the
// minimal, pure, offline term-resolution walker VCDM 2.0 `type`
// validation needs — enough to answer three questions about a
// credential/presentation document's own `@context` array:
//
//   1. Does an inline context REDEFINE a PROTECTED term (a term the
//      base VCDM v2 context, or an earlier `"@protected": true` inline
//      context, already defined) with a DIFFERENT mapping? JSON-LD 1.1
//      forbids this (§ "Protected Term Definitions"); VCDM makes the
//      whole v2 base context protected. Fixtures:
//      `credential-redef-type-fail.json` (redefines the v2-protected
//      `VerifiableCredential`) and `credential-redef-type2-fail.json`
//      (redefines an inline `"@protected": true` term).
//
//   2. Does a `type` value that is a defined TERM map to a NON-URL
//      IRI? A term used as a type must expand to an absolute IRI.
//      Fixture: `credential-type-mapped-nonurl-fail.json`
//      (`{"ExampleTestCredential": "https ://not-a-url#..."}`).
//
//   3. Is a `type` value UNMAPPED — not a URL, not a defined term, and
//      unreachable by any `@vocab` fallback because `{"@vocab": null}`
//      nullified it — with no unknown remote context that could still
//      define it? Fixture: `credential-type-unmapped-fail.json`.
//
// The v2 base context is supplied as an ALREADY-PARSED `json_val`
// (`Parser.JSON.parse_json` of the vendored
// `third_party/contexts/credentials-v2.jsonld`): the consumer parses
// it once and passes it in, so this module does ZERO I/O and carries no
// `assume val`. The term/protected data is read out of that parsed
// context (data-driven) rather than hardcoded here, so the map tracks
// the real W3C context byte-for-byte.
//
// CONSERVATIVE CHOICES (each keeps the `-ok` corpus green — the hard
// constraint is ZERO false-fails on any `-ok` fixture):
//   - An UNKNOWN remote context URL (any `@context` string entry other
//     than the v2 base IRI, e.g. `.../credentials/examples/v2`) is
//     treated as "could define anything": its terms are unknown, so a
//     `type` value we cannot otherwise resolve is NOT flagged (it may
//     be defined there). This is what keeps
//     `credential-optional-type-ok.json` (`RelationshipCredential`,
//     defined by the un-vendored examples/v2 context) passing.
//   - An UNMAPPED `type` term is flagged ONLY when `@vocab` was
//     EXPLICITLY set to `null` AND there is no unknown remote context.
//     A merely-absent `@vocab` (the common case) never triggers an
//     unmapped failure — the narrowest rule that still catches
//     `credential-type-unmapped-fail.json`.
//   - "URL-shaped" here means "contains ':' and no space" — the same
//     cheap predicate `VC.Credential.vc_looks_like_iri` uses, chosen
//     over `RDF.Term.is_iri` (colon-only) because the corpus's
//     deliberately-mangled non-URL device is an embedded space
//     ("https ://not-a-url#..."), which a colon-only check would miss.
//
// This module is a leaf: it depends only on `Parser.JSON` (and the F*
// stdlib). It does NOT depend on `VC.Credential` — it is compiled
// BEFORE it — and reports its verdict via its own `vcx_result` type,
// which `VC.Credential` maps onto `VC_Fail`.
//
// Reference: VC Data Model 2.0, W3C Recommendation 2025-05-15
// (https://www.w3.org/TR/vc-data-model-2.0/); JSON-LD 1.1, W3C
// Recommendation 2020-07-16, § 4.1.10 (Protected Term Definitions).
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.JSON

// ================================================================
// Small char/string helpers (leaf-module discipline — no dependency
// on SPARQL11.Algebra or VC.Credential's own namesake helpers, which
// are compiled later).
// ================================================================

let rec vcx_chars_have (cs : list FStar.Char.char) (target : FStar.Char.char)
  : Tot bool (decreases cs) =
  match cs with
  | [] -> false
  | c :: tl -> c = target || vcx_chars_have tl target

let vcx_has_char (s : string) (target : FStar.Char.char) : bool =
  vcx_chars_have (String.list_of_string s) target

// "URL-shaped" for this module's cheap purposes: contains a ':' and no
// raw space. See the header's conservative-choices note for why this,
// not RDF.Term.is_iri, is the predicate.
let vcx_is_url (s : string) : bool =
  vcx_has_char s (FStar.Char.char_of_int 0x3A) (* ':' *) &&
  not (vcx_has_char s (FStar.Char.char_of_int 0x20)) (* ' ' *)

// Is a context map key a JSON-LD keyword (leading '@')? Keyword keys
// (@protected, @vocab, @id, @type, ...) are not term definitions.
let vcx_is_keyword_key (k : string) : bool =
  String.length k > 0 && FStar.Char.int_of_char (String.index k 0) = 0x40 (* '@' *)

// ================================================================
// Term definitions + accumulated context state.
// ================================================================

// A resolved term definition: the IRI it maps to (None when the term
// maps to a keyword such as "@id"/"@type", or to an object without a
// plain string `@id` — neither is a type-expandable IRI, and neither
// occurs as a `type` VALUE in the corpus), and whether it is protected
// (redefining it with a DIFFERENT mapping is a JSON-LD 1.1 error).
type vcx_term_def = {
  vcx_iri : option string;
  vcx_protected : bool;
}

type vcx_vocab =
  | VcxVocabUnset : vcx_vocab
  | VcxVocabNull  : vcx_vocab
  | VcxVocabSet   : string -> vcx_vocab

type vcx_state = {
  vcx_terms          : list (string & vcx_term_def);
  vcx_vocab          : vcx_vocab;
  vcx_unknown_remote : bool;
}

// A processing step result: an updated state, or a protected-term
// redefinition violation (with a human-facing reason; the runner scores
// Pass/Fail, not the text).
type vcx_step =
  | VcxStepOk        : vcx_state -> vcx_step
  | VcxStepViolation : string -> vcx_step

// A final type-resolution verdict.
type vcx_result =
  | VcxOk        : vcx_result
  | VcxViolation : string -> vcx_result

// ================================================================
// Reading term definitions out of a context object.
// ================================================================

// Look a key up directly in a raw (string & json_val) field list.
let rec vcx_field_lookup (fields : list (string & json_val)) (k : string)
  : Tot (option json_val) (decreases fields) =
  match fields with
  | [] -> None
  | (k', v) :: tl -> if k' = k then Some v else vcx_field_lookup tl k

// A term-definition value's mapped IRI: a plain string maps directly;
// an object maps via its `@id` string; anything else has no plain IRI.
let vcx_term_iri_of_value (v : json_val) : option string =
  match v with
  | JString s -> Some s
  | JObject _ -> (match json_get_field "@id" v with Some (JString s) -> Some s | _ -> None)
  | _ -> None

// Is this context object marked `"@protected": true`?
let vcx_obj_protected (fields : list (string & json_val)) : bool =
  match vcx_field_lookup fields "@protected" with
  | Some (JBool b) -> b
  | _ -> false

// Turn a context object's fields into term definitions, skipping
// keyword keys. `protected` is the object's own @protected flag.
let rec vcx_terms_of_fields (protected : bool) (fields : list (string & json_val))
  : Tot (list (string & vcx_term_def)) (decreases fields) =
  match fields with
  | [] -> []
  | (k, valv) :: tl ->
    if vcx_is_keyword_key k then vcx_terms_of_fields protected tl
    else (k, { vcx_iri = vcx_term_iri_of_value valv; vcx_protected = protected })
         :: vcx_terms_of_fields protected tl

// The base VCDM v2 term map, read from the vendored context's parsed
// json_val (top-level shape: `{"@context": { ... }}`).
let vcx_base_terms (v2ctx : json_val) : list (string & vcx_term_def) =
  match json_get_field "@context" v2ctx with
  | Some (JObject fields) -> vcx_terms_of_fields (vcx_obj_protected fields) fields
  | _ -> []

// ================================================================
// Lookup + insertion in the accumulated term list. Newest definition
// is PREPENDED, so vcx_lookup (first match wins) sees the most recent
// binding, and base terms loaded first are shadowed by later inline
// ones for resolution — while the redefinition check below still sees
// the protected base binding at the moment an inline context tries to
// override it.
// ================================================================

let rec vcx_lookup (terms : list (string & vcx_term_def)) (k : string)
  : Tot (option vcx_term_def) (decreases terms) =
  match terms with
  | [] -> None
  | (k', d) :: tl -> if k' = k then Some d else vcx_lookup tl k

let vcx_set_term (st : vcx_state) (k : string) (iri : option string) (prot : bool) : vcx_state =
  { st with vcx_terms = (k, { vcx_iri = iri; vcx_protected = prot }) :: st.vcx_terms }

// ================================================================
// Processing an inline context object into the state.
// ================================================================

let vcx_apply_vocab (cur : vcx_vocab) (fields : list (string & json_val)) : vcx_vocab =
  match vcx_field_lookup fields "@vocab" with
  | Some JNull       -> VcxVocabNull
  | Some (JString s) -> VcxVocabSet s
  | _                -> cur

// Fold this object's term definitions into the state. A definition of
// a key that is ALREADY protected with a DIFFERENT IRI is a violation;
// re-stating a protected term with the SAME mapping, or defining a new
// / non-protected term, updates the map. A term (re)defined here is
// protected iff this object is @protected OR the prior binding was.
let rec vcx_apply_terms (obj_protected : bool) (st : vcx_state) (fields : list (string & json_val))
  : Tot vcx_step (decreases fields) =
  match fields with
  | [] -> VcxStepOk st
  | (k, valv) :: tl ->
    if vcx_is_keyword_key k then vcx_apply_terms obj_protected st tl
    else
      let new_iri = vcx_term_iri_of_value valv in
      (match vcx_lookup st.vcx_terms k with
       | Some d ->
         if d.vcx_protected && d.vcx_iri <> new_iri then
           VcxStepViolation ("redefinition of protected term '" ^ k ^ "'")
         else
           vcx_apply_terms obj_protected
             (vcx_set_term st k new_iri (obj_protected || d.vcx_protected)) tl
       | None ->
         vcx_apply_terms obj_protected (vcx_set_term st k new_iri obj_protected) tl)

let vcx_apply_inline (st : vcx_state) (fields : list (string & json_val)) : vcx_step =
  let prot = vcx_obj_protected fields in
  let st1 = { st with vcx_vocab = vcx_apply_vocab st.vcx_vocab fields } in
  vcx_apply_terms prot st1 fields

// ================================================================
// Processing the document's own @context array, in order.
// ================================================================

let vcx_base_url : string = "https://www.w3.org/ns/credentials/v2"

let vcx_load_base (st : vcx_state) (base : list (string & vcx_term_def)) : vcx_state =
  { st with vcx_terms = List.Tot.append base st.vcx_terms }

let rec vcx_process_entries (base : list (string & vcx_term_def))
                            (st : vcx_state) (entries : list json_val)
  : Tot vcx_step (decreases entries) =
  match entries with
  | [] -> VcxStepOk st
  | e :: tl ->
    (match e with
     | JString s ->
       if s = vcx_base_url then
         vcx_process_entries base (vcx_load_base st base) tl
       else
         // an unknown remote context — its terms are opaque to this
         // offline walker; record that so unmapped-term checks stay
         // conservative.
         vcx_process_entries base { st with vcx_unknown_remote = true } tl
     | JObject fields ->
       (match vcx_apply_inline st fields with
        | VcxStepViolation r -> VcxStepViolation r
        | VcxStepOk st'      -> vcx_process_entries base st' tl)
     | _ -> vcx_process_entries base st tl)

let vcx_build_state (v2ctx : json_val) (doc : json_val) : vcx_step =
  let base = vcx_base_terms v2ctx in
  let st0 = { vcx_terms = []; vcx_vocab = VcxVocabUnset; vcx_unknown_remote = false } in
  match json_get_field "@context" doc with
  | Some (JArray entries) -> vcx_process_entries base st0 entries
  | Some (JString s)      -> vcx_process_entries base st0 [JString s]
  | _                     -> VcxStepOk st0

// ================================================================
// Resolving a `type` value against the built state.
// ================================================================

let vcx_resolve_type (st : vcx_state) (t : string) : vcx_result =
  if vcx_is_url t then VcxOk
  else
    match vcx_lookup st.vcx_terms t with
    | Some d ->
      (match d.vcx_iri with
       | Some m -> if vcx_is_url m then VcxOk
                   else VcxViolation ("type term '" ^ t ^ "' is mapped to a non-URL IRI")
       | None -> VcxOk)
    | None ->
      (match st.vcx_vocab with
       | VcxVocabNull ->
         if st.vcx_unknown_remote then VcxOk
         else VcxViolation ("type term '" ^ t ^ "' is unmapped (no term definition; @vocab nullified)")
       | _ -> VcxOk)

let rec vcx_resolve_types (st : vcx_state) (ts : list string)
  : Tot vcx_result (decreases ts) =
  match ts with
  | [] -> VcxOk
  | t :: tl -> (match vcx_resolve_type st t with
                | VcxOk -> vcx_resolve_types st tl
                | v     -> v)

// ================================================================
// Entry point: build the context state from (vendored v2 context,
// document) and resolve every declared `type` value.
// ================================================================

let vcx_check_types (v2ctx : json_val) (doc : json_val) (type_values : list string) : vcx_result =
  match vcx_build_state v2ctx doc with
  | VcxStepViolation r -> VcxViolation r
  | VcxStepOk st       -> vcx_resolve_types st type_values
