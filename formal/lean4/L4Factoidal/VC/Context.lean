/-
L4Factoidal.VC.Context — the JSON-LD contexts a Verifiable Credential
and its Data Integrity proof resolve against, and the loader that
serves them OFFLINE.

This is NOT a port of `formal/fstar/VC.Context.fst`. That module is a
purpose-built term-resolution walker for VCDM 2.0 `type`-value checking
(protected-term redefinition, non-URL type mappings, `@vocab: null`)
feeding the structural validator `VC.Credential.fst` — a stage this
port does not include (see PORT_NOTES, "VC Data Integrity stage",
"Not ported"). The Lean tree has a full JSON-LD 1.1 processor
(`JSONLD/`), so the contexts are consumed by the real algorithm instead;
what this module supplies is the DATA the F* tree keeps in
`bin/vc-api-shim/server.mjs` and `bin/vc-runner/vc_runner.ml`:

  * which vendored context file answers which context IRI
    (`third_party/contexts/`, provenance and licence in its
    `PROVENANCE.md`; the W3C `did/v1`, `multikey/v1`, `ed25519-2020/v1`
    contexts come from `third_party/jsonld-context-cache/`, see the
    `jsonld-context-cache` skill);
  * the proof-options context rule of the shim's `proofContextFor`: a
    proof's canonical form needs the Data Integrity vocabulary
    (`DataIntegrityProof`, `cryptosuite`, `verificationMethod`,
    `proofPurpose`, `created`, `proofValue`). VCDM 2.0's base context
    defines it (scoped under `VerifiableCredential`/`proof`); the VCDM
    1.1 base context does not, and JSON-LD DROPS undefined terms
    silently, which would produce a truncated, non-interoperable
    signature input. So the proof options get
    `https://w3id.org/security/data-integrity/v2` appended unless the
    document's context already carries VCDM 2.0 or that context
    (appending it ON TOP of VCDM 2.0 redefines protected terms and the
    processor rightly rejects the document).

The loader is a PARAMETER, as throughout the JSON-LD port: this module
only maps IRIs to file names and builds a `Loader` from bodies that the
executable read in `IO` (`Harness/VcProbe.lean`). No file system access
here; no empty-context fallback anywhere (a theorem of the JSON-LD
stage, `contextProcess_string_none_loader`).
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JSONLD.Loader

namespace L4Factoidal.VC.Context

open L4Factoidal.JSON
open L4Factoidal.JSONLD

/-- VCDM 2.0 base context IRI. -/
def vcV2ContextIri : String := "https://www.w3.org/ns/credentials/v2"

/-- Data Integrity v2 context IRI. -/
def dataIntegrityV2ContextIri : String := "https://w3id.org/security/data-integrity/v2"

/-- Context IRI → file name under `third_party/contexts/` (the mapping
recorded in that directory's `PROVENANCE.md`). -/
def vendoredContextFiles : List (String × String) := [
  (vcV2ContextIri, "credentials-v2.jsonld"),
  ("https://www.w3.org/ns/credentials/examples/v2", "credentials-examples-v2.jsonld"),
  (dataIntegrityV2ContextIri, "security-data-integrity-v2.jsonld"),
  ("https://w3id.org/security/multikey/v1", "security-multikey-v1.jsonld"),
  ("https://www.w3.org/2018/credentials/v1", "credentials-v1.jsonld") ]

/-- A loader over an `(IRI, body)` table the caller has read from disk —
`vendoredContextFiles` resolved, plus whatever the context cache holds. -/
def vcLoader (bodies : List (String × String)) : Loader := tableLoader bodies

/-- Does a `@context` value (string or array) name this IRI? -/
def contextIncludes (ctx : Json) (iri : String) : Bool :=
  match ctx with
  | .string s => s == iri
  | .array items => items.any (fun i => match i with | .string s => s == iri | _ => false)
  | _ => false

/-- The `@context` a proof-options document is canonicalised under
(module header): the securing document's own context, with the Data
Integrity v2 context appended unless VCDM 2.0 or that context is
already listed. Always an array. -/
def proofContextFor (docContext : Option Json) : Json :=
  let base : List Json := match docContext with
    | some (.array items) => items
    | some (.null) => []
    | some j => [j]
    | none => []
  let ctx := Json.array base
  if contextIncludes ctx vcV2ContextIri || contextIncludes ctx dataIntegrityV2ContextIri then ctx
  else Json.array (base ++ [Json.string dataIntegrityV2ContextIri])

end L4Factoidal.VC.Context
