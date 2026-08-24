# Proof, logic, and evidence architecture

Status: analysis note, 2026-08-23. No implementation changes.

Question: can Factoidal integrate the notions of proof and formal logic
from the RDF/RDFS/OWL layers with the proof methods used to create and
verify the software, including signed data, transformations, and
regulated-industry uses?

Conclusion: yes, but only if the system treats "proof" as a typed
stack rather than a single word. The RDF/RDFS/OWL layer supplies
object-logic claims about graphs: satisfaction, entailment,
consistency, closure, and semantic-extension boundaries. F* and Lean 4
supply meta-logic claims about the software: totality, termination,
representation invariants, parser/serializer round trips, executable
closure soundness, algorithm equivalence, and extraction/FFI
boundaries. VC Data Integrity and RDFC-1.0 add a third kind of claim:
cryptographic evidence that a concrete byte-level document is the one
whose graph semantics and software-processing claims are being relied
on.

The integration target is therefore not "make RDF proofs and F*/Lean
proofs the same thing." It is:

1. Parse and canonicalize bytes into graph/dataset values.
2. Prove or test that this transformation preserves the intended RDF
   identity relation.
3. Prove that semantic operations over those graph values preserve
   truth under the relevant W3C interpretation class.
4. Sign the canonicalized representation and the proof/processing
   metadata that identify the operation, theorem family, software
   version, and policy profile.
5. Publish the result as an RDF evidence graph that machines can query
   and auditors can inspect.

## Methodology correction history

This note is also a guard against a pattern that has repeated in the
project.

First, the earliest F* work was pulled toward OCaml. Agents reached for
the extracted or hand-written implementation layer because it was the
fastest way to make behavior appear. That made progress hard to trust:
logic that should have lived in F* or Lean sat below the proof boundary.

Second, after that OCaml pull was controlled, another gap became
visible. Some F* code was still "verified" only in the narrow sense
that it was total, typed, and executable. A `Tot` implementation can be
well behaved as a program and still fail to state the RDF Model Theory,
RDFS semantic conditions, OWL RDF-Based interpretation conditions, or
SPARQL entailment-regime semantics it is intended to implement.

Third, the recent RDF/RDFS/OWL proof work is the needed repair:
separate interfaces/specifications from implementations, introduce
independent model-theoretic or rule-specification layers, and connect
optimized execution to those layers with explicit bridge theorems.
This is the difference between "the closure function terminates" and
"the closure function emits only triples true in every interpretation
satisfying the input graph under the stated conditions."

Fourth, the Lean 4 port has acted as an independent instrument. It has
found F* defects, forced hidden scoping choices into the open, and made
claim labels matter: licensing lemmas, truth preservation,
completeness, conformance-score evidence, extern assumptions, and
runtime differential checks are different claims. The correct response
is not to blur them under one "verified" label, but to make the labels
stable enough that both trees and the evidence graph can use them.

The durable rule is: no proof claim stands alone. It must name its
logic level, fragment, implementation path, byte identity path, and
remaining trust boundary.

## Source context

The W3C RDF 1.1 Semantics Recommendation defines a model-theoretic
semantics for RDF graphs and RDFS vocabularies, including entailment
regimes and truth preservation for transformations or operations that
derive RDF content from other RDF:

- https://www.w3.org/TR/rdf11-mt/
- especially sections 1, 3, 5, 8, and 9.

The OWL 2 RDF-Based Semantics Recommendation is RDF-compatible model
theory. It defines OWL 2 RDF-Based interpretations as D-interpretations
that also satisfy the OWL semantic conditions, and defines
satisfaction, consistency, and entailment over RDF graphs:

- https://www.w3.org/TR/owl2-rdf-based-semantics/
- especially definitions 4.2 through 4.5.

RDFC-1.0 defines canonicalization of RDF datasets: datasets with the
same information are transformed into the same serialized canonical
form, with deterministic blank-node identifiers:

- https://www.w3.org/TR/rdf-canon/
- especially section 4.

VC Data Integrity defines a tamper-evidence processing model:
document/context selection, cryptosuite selection, proof creation, and
verification through transformation, hashing, and proof verification:

- https://www.w3.org/TR/vc-data-integrity/
- especially sections 4.1 through 4.5.

These specifications compose naturally, but only if each layer keeps
its own claim boundary explicit.

## Current Factoidal evidence

F* already carries the most mature model-theoretic RDF/RDFS work:

- `formal/fstar/RDF.Entailment.Simple.*`
- `formal/fstar/RDF.Entailment.RDF.Spec.fst`
- `formal/fstar/RDF.Entailment.RDFS.*`
- `formal/fstar/OWL.Semantics.*`
- `formal/fstar/OWL.RL.*`
- `formal/fstar/RDF.Canonical.fst`
- `formal/fstar/VC.DataIntegrity.fst`

The current RDF/RDFS coverage survey says simple entailment is strong,
RDF/RDFS soundness has substantial landed proof coverage, and
rho-df completeness has a corrected bounded theorem. It also records
the remaining hard gaps: index completeness (#347), fixed-point and
dedup faithfulness, literal value spaces, datatype interpretation, and
some completeness hypotheses.

Lean 4 now supplies a second, independently useful proof style:

- `formal/lean4/L4Factoidal/RDF/*Theorems.lean`
- `formal/lean4/L4Factoidal/RDFS/*Theorems.lean`
- `formal/lean4/L4Factoidal/OWL/*Theorems.lean`
- `formal/lean4/L4Factoidal/RDF/Canonical.lean`
- `formal/lean4/L4Factoidal/VC/DataIntegrity.lean`
- `formal/lean4/Harness/*`

Issue #466 shows the Lean port is not a toy mirror. It has real W3C
manifest execution, differential checks against the F* tree, theorem
modules, property probes, and a labelled HACL* Ed25519 extern family.
It has also found F* defects. That makes Lean a useful independent
evidence generator, not only an alternate implementation.

Signed-data support is no longer only a plan. The F* side has
`VC.DataIntegrity.fst` for the transform -> hash -> proof pipeline over
canonical inputs and datasets. The Lean side has a document-level
`VC/DataIntegrity.lean` that models proof blocks, proof options,
JSON-LD-to-RDF canonicalization, did:key resolution boundaries, proof
sets, and refusal modes. The crypto policy correctly separates public
hashes, byte encodings, and secret-bearing signatures.

## The integration model

Use four artifact classes.

### 1. Semantic claim

An RDF/RDFS/OWL claim is a statement in the object logic. Examples:

- graph G simply entails graph H;
- RDFS closure step S is truth-preserving under `rdfs_conditions`;
- an OWL RL rule is licensed by a specific semantic condition;
- an entailment regime applies only under a named fragment predicate.

This belongs in F*/Lean theorem statements and in an RDF evidence graph
as a queryable claim. It must not be confused with "the code type
checks."

### 2. Software-correctness claim

A software claim is a theorem or measured gate about an implementation
path. Examples:

- parser round trip;
- canonical serializer sortedness;
- closure implementation equals reference closure;
- indexed closure equals naive closure;
- evaluator invariant;
- F* extraction boundary or Lean extern audit.

This can support a semantic claim only through a named bridge theorem.
For example, a rule function returning a well-formed graph is useful
but not enough; the required theorem is that every emitted triple is
true in every interpretation satisfying the input graph under the
selected semantic conditions.

### 3. Byte and identity claim

A byte claim ties the abstract graph/dataset to a concrete document.
Examples:

- parse bytes -> dataset;
- dataset -> canonical N-Quads;
- canonical N-Quads hash;
- graph/dataset isomorphism;
- context validation;
- Data Integrity proof configuration canonicalization.

This is the bridge between regulated records and formal semantics.
Without it, a theorem proves something about an abstract value, while
the regulator or counterparty sees a file.

### 4. Cryptographic claim

A cryptographic claim says a key holder endorsed a canonical byte
sequence under a named suite and purpose. It does not prove the RDF
content is true. It proves binding, integrity, and non-repudiation
properties relative to the cryptographic assumptions and key policy.

This layer should point at semantic and software-correctness claims,
not replace them.

## Evidence graph shape

Factoidal should define a small RDF vocabulary for evidence packages,
or reuse PROV-O where possible and add only project-specific terms.
The minimal shape:

```turtle
@prefix fxev: <https://factoidal.dev/ns/evidence#> .
@prefix prov: <http://www.w3.org/ns/prov#> .

<#run> a fxev:VerifiedRun ;
  fxev:inputDataset <sha256:...> ;
  fxev:canonicalDataset <sha256:...> ;
  fxev:operation fxev:RdfsClosure ;
  fxev:regime fxev:RDFS ;
  fxev:fragment fxev:Rdf11NoTripleTerms ;
  fxev:implementation <git:...> ;
  fxev:theorem <urn:factoidal:theorem:RDFS.Closure.Soundness.rdfs_closure_entails> ;
  fxev:testReport <docs/test-results/latest.json> ;
  fxev:proofProfile fxev:SoundnessNotCompleteness ;
  prov:generatedAtTime "2026-08-23T00:00:00Z"^^xsd:dateTime .
```

This makes the important audit question machine-readable:

> Which theorem, over which interpretation class and fragment, justifies
> which transformation of which signed dataset, using which executable
> and which test evidence?

## Evidence profile v0.1

The first profile should be intentionally small. It should be rich
enough to describe one RDFS closure run and one VC Data Integrity
verification, but not so broad that it tries to become a general proof
ontology.

Namespace:

```turtle
@prefix fxev: <https://factoidal.dev/ns/evidence#> .
```

Core classes:

| Term | Kind | Meaning |
|---|---|---|
| `fxev:EvidencePackage` | class | A named bundle of claims about one processing event. |
| `fxev:VerifiedRun` | class | A run whose evidence includes at least one theorem-backed claim. |
| `fxev:SemanticClaim` | class | A claim in an RDF/RDFS/OWL/SPARQL object logic. |
| `fxev:SoftwareClaim` | class | A theorem, invariant, or measured gate about implementation behavior. |
| `fxev:ByteIdentityClaim` | class | A claim connecting files, parsed graphs, datasets, canonical bytes, and hashes. |
| `fxev:CryptographicClaim` | class | A signature, hash, key, or proof-verification result. |
| `fxev:PolicyProfile` | class | A reusable bundle of permitted regimes, cryptosuites, theorem floors, and test floors. |
| `fxev:Refusal` | class | A typed refusal to make a stronger claim. |

Core predicates:

| Term | Range shape | Meaning |
|---|---|---|
| `fxev:claim` | claim node | Adds a typed claim to an evidence package. |
| `fxev:claimKind` | IRI | One of semantic, software, byte identity, cryptographic. |
| `fxev:sourceArtifact` | IRI/literal | The input file, document, dataset, or graph identifier. |
| `fxev:resultArtifact` | IRI/literal | The output file, document, dataset, or graph identifier. |
| `fxev:canonicalArtifact` | IRI/literal | The canonical byte representation used for hashing or comparison. |
| `fxev:digest` | literal | Hash of a source, result, canonical artifact, or report. |
| `fxev:algorithm` | IRI/literal | Canonicalization, hash, signing, parser, closure, or validation algorithm. |
| `fxev:regime` | IRI/literal | RDF, RDFS, D-entailment, OWL-RL, OWL-RDF-Based, OWL-Direct, SHACL, etc. |
| `fxev:fragment` | IRI/literal | The explicit fragment restriction under which a theorem is valid. |
| `fxev:theorem` | IRI | Stable theorem URI. |
| `fxev:theoremStatus` | IRI/literal | Proved, assumed, carried hypothesis, measured, refused, unsupported. |
| `fxev:proofProfile` | IRI/literal | The strength of a proof claim, such as soundness-not-completeness or licensing-not-truth. |
| `fxev:testReport` | IRI | Machine-readable report or dashboard artifact. |
| `fxev:implementation` | IRI/literal | Git commit, binary, wasm bundle, Lean executable, F* runner, or extracted path. |
| `fxev:trustBoundary` | IRI/literal | Extraction, FFI, HACL*, host clock, network, context loader, or storage boundary. |
| `fxev:verifiedBy` | IRI/literal | F*, Lean 4, W3C suite, differential harness, signature verifier, or human audit. |
| `fxev:verificationMethod` | IRI/literal | A VC Data Integrity verification method, key identifier, or equivalent signing authority reference. |
| `fxev:policyProfile` | `fxev:PolicyProfile` | The policy bundle this evidence package claims to satisfy. |
| `fxev:refusesClaim` | `fxev:Refusal` | A stronger claim this package explicitly does not make. |
| `fxev:reason` | literal | Human-readable reason for a refusal, unsupported case, or scoped claim boundary. |

Named controlled values should be IRIs, not free text, once the profile
stabilizes. During the first documentation pass, short literal names
are acceptable if the page states their intended URI.

Recommended first controlled values:

| Value | Meaning |
|---|---|
| `fxev:Semantic` | Object-logic graph claim. |
| `fxev:SoftwareCorrectness` | Program theorem or implementation gate. |
| `fxev:ByteIdentity` | Bytes-to-graph or graph-to-bytes claim. |
| `fxev:Cryptographic` | Signature/hash/key claim. |
| `fxev:Proved` | Machine-checked theorem, no carried hypothesis beyond stated imports/logic base. |
| `fxev:Measured` | Empirical test, benchmark, or conformance score. |
| `fxev:CarriedHypothesis` | The theorem exists but depends on a named hypothesis. |
| `fxev:Unsupported` | The implementation refuses the case explicitly. |
| `fxev:SoundnessNotCompleteness` | Truth preservation is claimed; completeness is not. |
| `fxev:LicensingNotTruth` | A rule is structurally licensed, but model-theoretic truth preservation is not claimed. |

## Live Factoidal evidence runner

The panel below is an exploratory executable sketch, not a stable
emitter/checker. It uses the same-origin `@factoidal/core` browser
package mirrored under this docs site:

- core-RDFS fragment and closure calls use `coreRdfsCheck` and
  `coreRdfsClosure`;
- the derived-fact query tries the WASM query engine first and falls
  back to the JS engine if this browser does not support that path;
- VC Data Integrity uses Factoidal's `eddsa-rdfc-2022` wrappers over
  HACL* WebAssembly crypto;
- the generated Turtle is still demo evidence, not a normative report
  format.

<section id="fxev-live-runner" class="fxev-live-runner" aria-labelledby="fxev-live-title">
  <style>
    .fxev-live-runner {
      margin: 1.5rem 0;
      border: 1px solid #cfd8d3;
      border-radius: 8px;
      background: #f7fbf8;
      color: #202a24;
      overflow: hidden;
    }
    .fxev-live-runner * { box-sizing: border-box; }
    .fxev-runner-head {
      display: flex;
      gap: 1rem;
      align-items: center;
      justify-content: space-between;
      padding: 1rem;
      border-bottom: 1px solid #dce5df;
      background: #eef6f1;
    }
    .fxev-runner-head h3 {
      margin: 0;
      font-size: 1.1rem;
      line-height: 1.25;
    }
    .fxev-actions {
      display: flex;
      flex-wrap: wrap;
      gap: .5rem;
    }
    .fxev-actions button {
      border: 1px solid #2d6a4f;
      background: #2d6a4f;
      color: #fff;
      border-radius: 6px;
      padding: .45rem .7rem;
      font: inherit;
      cursor: pointer;
    }
    .fxev-actions button.secondary {
      background: transparent;
      color: #2d6a4f;
    }
    .fxev-actions button:disabled {
      opacity: .55;
      cursor: progress;
    }
    .fxev-grid {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(260px, 1fr));
      gap: 1px;
      background: #dce5df;
    }
    .fxev-pane {
      min-width: 0;
      padding: 1rem;
      background: #fff;
    }
    .fxev-pane h4 {
      margin: 0 0 .5rem;
      font-size: .95rem;
    }
    .fxev-pane label {
      display: block;
      margin: .65rem 0 .25rem;
      color: #43514a;
      font-size: .78rem;
      font-weight: 700;
      text-transform: uppercase;
    }
    .fxev-pane textarea,
    .fxev-pane pre {
      width: 100%;
      min-height: 9rem;
      margin: 0;
      border: 1px solid #d7dfda;
      border-radius: 6px;
      background: #fbfdfb;
      color: #1d2520;
      font: 12px/1.45 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      overflow: auto;
    }
    .fxev-pane textarea {
      resize: vertical;
      padding: .75rem;
    }
    .fxev-pane pre {
      padding: .75rem;
      white-space: pre-wrap;
      overflow-wrap: anywhere;
    }
    .fxev-status {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(160px, 1fr));
      gap: .5rem;
      padding: .75rem 1rem;
      border-top: 1px solid #dce5df;
      background: #f2f7f4;
      font-size: .82rem;
    }
    .fxev-status span {
      display: inline-flex;
      min-height: 2rem;
      align-items: center;
      border: 1px solid #d7dfda;
      border-radius: 999px;
      padding: .2rem .7rem;
      background: #fff;
      color: #33433a;
    }
    @media (prefers-color-scheme: dark) {
      .fxev-live-runner {
        border-color: #33433a;
        background: #141a17;
        color: #d6dbe1;
      }
      .fxev-runner-head {
        border-bottom-color: #33433a;
        background: #18211c;
      }
      .fxev-actions button.secondary { color: #7fd0a7; }
      .fxev-grid { background: #33433a; }
      .fxev-pane { background: #121417; }
      .fxev-pane label { color: #aab8b0; }
      .fxev-pane textarea,
      .fxev-pane pre {
        border-color: #33433a;
        background: #1a1f1c;
        color: #d6dbe1;
      }
      .fxev-status {
        border-top-color: #33433a;
        background: #171d1a;
      }
      .fxev-status span {
        border-color: #33433a;
        background: #121417;
        color: #d6dbe1;
      }
    }
  </style>
  <div class="fxev-runner-head">
    <h3 id="fxev-live-title">Run the evidence profile</h3>
    <div class="fxev-actions">
      <button type="button" data-fxev-run="all">Run both</button>
      <button type="button" class="secondary" data-fxev-run="rdfs">RDFS only</button>
      <button type="button" class="secondary" data-fxev-run="vc">VC only</button>
    </div>
  </div>
  <div class="fxev-grid">
    <div class="fxev-pane">
      <h4>RDFS closure input</h4>
      <label for="fxev-rdfs-input">Editable Turtle</label>
      <textarea id="fxev-rdfs-input" spellcheck="false"></textarea>
      <label for="fxev-rdfs-output">Generated evidence graph</label>
      <pre id="fxev-rdfs-output">Press "Run both" or "RDFS only".</pre>
    </div>
    <div class="fxev-pane">
      <h4>VC Data Integrity input</h4>
      <label for="fxev-vc-doc">Canonical document N-Quads</label>
      <textarea id="fxev-vc-doc" spellcheck="false"></textarea>
      <label for="fxev-vc-config">Canonical proof config N-Quads</label>
      <textarea id="fxev-vc-config" spellcheck="false"></textarea>
      <label for="fxev-vc-output">Generated evidence graph</label>
      <pre id="fxev-vc-output">Press "Run both" or "VC only".</pre>
    </div>
  </div>
  <div class="fxev-status" aria-live="polite">
    <span id="fxev-package-status">package: not loaded</span>
    <span id="fxev-wasm-status">query engine: pending</span>
    <span id="fxev-crypto-status">crypto: pending</span>
  </div>
  <script type="module" src="{{ '/designissues/proof-evidence-runner.js' | url }}"></script>
</section>

## Worked example: RDFS closure run

This is the smallest useful semantic evidence package. It claims that
a closure output is sound, not that it is complete for all RDFS
entailment.

```turtle
@prefix fxev: <https://factoidal.dev/ns/evidence#> .
@prefix prov: <http://www.w3.org/ns/prov#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

<#rdfs-run-001> a fxev:EvidencePackage, fxev:VerifiedRun ;
  fxev:policyProfile fxev:RegulatedRdfsSoundnessProfile ;
  fxev:claim <#input-byte-identity>,
             <#rdfs-soundness>,
             <#implementation-gate>,
             <#known-nonclaim> ;
  prov:generatedAtTime "2026-08-23T00:00:00Z"^^xsd:dateTime .

<#input-byte-identity> a fxev:ByteIdentityClaim ;
  fxev:claimKind fxev:ByteIdentity ;
  fxev:sourceArtifact <sha256:INPUT_DATASET_HASH> ;
  fxev:canonicalArtifact <sha256:INPUT_CANONICAL_NQUADS_HASH> ;
  fxev:algorithm "RDFC-1.0 canonical N-Quads" ;
  fxev:verifiedBy "Factoidal RDF.Canonical / W3C rdf-canon suite" ;
  fxev:testReport <https://danbri.github.io/factoidal/test-results/latest.json> .

<#rdfs-soundness> a fxev:SemanticClaim ;
  fxev:claimKind fxev:Semantic ;
  fxev:sourceArtifact <sha256:INPUT_DATASET_HASH> ;
  fxev:resultArtifact <sha256:RDFS_CLOSURE_DATASET_HASH> ;
  fxev:regime "RDFS" ;
  fxev:fragment "RDF 1.1 graph fragment named by the theorem" ;
  fxev:theorem <urn:factoidal:theorem:RDF.Entailment.RDFS:rdfs_closure_entails> ;
  fxev:theoremStatus fxev:CarriedHypothesis ;
  fxev:proofProfile fxev:SoundnessNotCompleteness ;
  fxev:trustBoundary "index completeness, dedup/string-key faithfulness where still carried" .

<#implementation-gate> a fxev:SoftwareClaim ;
  fxev:claimKind fxev:SoftwareCorrectness ;
  fxev:implementation <git:COMMIT> ;
  fxev:algorithm "formal/fstar RDFS closure, extracted runtime path" ;
  fxev:verifiedBy "F* verification plus W3C rdf-mt/rdfs-regime tests" ;
  fxev:testReport <https://danbri.github.io/factoidal/test-results/latest.json> .

<#known-nonclaim> a fxev:Refusal ;
  fxev:refusesClaim "complete RDFS entailment for unrestricted RDF graphs" ;
  fxev:reason "The current proof surface records soundness and fragment-bounded completeness only; unrestricted completeness is not claimed." .
```

Important details:

- The semantic claim names soundness separately from byte identity.
- The theorem status carries hypotheses when the current F* theorem
  does.
- The package refuses unrestricted completeness explicitly instead of
  letting readers infer it from the word "verified".
- A later implementation can mechanically fill the hashes, commit, and
  theorem URI once those identifiers are stable.

## Worked example: VC Data Integrity verification

This package verifies a signed JSON-LD credential and records what that
verification does and does not say.

```turtle
@prefix fxev: <https://factoidal.dev/ns/evidence#> .
@prefix prov: <http://www.w3.org/ns/prov#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

<#vc-run-001> a fxev:EvidencePackage, fxev:VerifiedRun ;
  fxev:policyProfile fxev:RegulatedCredentialProfile ;
  fxev:claim <#vc-document-identity>,
             <#vc-context-shape>,
             <#vc-proof-verification>,
             <#vc-semantic-nonclaim> ;
  prov:generatedAtTime "2026-08-23T00:00:00Z"^^xsd:dateTime .

<#vc-document-identity> a fxev:ByteIdentityClaim ;
  fxev:claimKind fxev:ByteIdentity ;
  fxev:sourceArtifact <sha256:SIGNED_VC_JSONLD_HASH> ;
  fxev:canonicalArtifact <sha256:VC_RDFC_CANONICAL_HASH> ;
  fxev:algorithm "JSON-LD toRdf + RDFC-1.0 canonicalization" ;
  fxev:trustBoundary "JSON-LD context loading and context cache policy" .

<#vc-context-shape> a fxev:SoftwareClaim ;
  fxev:claimKind fxev:SoftwareCorrectness ;
  fxev:algorithm "VC structural validation and proof-options construction" ;
  fxev:verifiedBy "Factoidal VC.DataIntegrity / VC tests" ;
  fxev:theoremStatus fxev:Measured .

<#vc-proof-verification> a fxev:CryptographicClaim ;
  fxev:claimKind fxev:Cryptographic ;
  fxev:algorithm "eddsa-rdfc-2022" ;
  fxev:digest "sha256(proofConfigCanonical) || sha256(documentCanonical)" ;
  fxev:verificationMethod "did:key:..." ;
  fxev:trustBoundary "HACL* Ed25519 extern family; key-control policy external to Factoidal" ;
  fxev:verifiedBy "VC Data Integrity verifier" ;
  fxev:theoremStatus fxev:Measured .

<#vc-semantic-nonclaim> a fxev:Refusal ;
  fxev:refusesClaim "the credential subject assertion is true" ;
  fxev:reason "A valid Data Integrity proof establishes document integrity and signer binding, not real-world truth or authorization." .
```

Important details:

- Signature verification is a cryptographic claim, not a semantic
  claim.
- JSON-LD context handling is a trust boundary and must be visible.
- A valid credential can still fail a policy profile, SHACL shape,
  authorization rule, or real-world truth check.
- The same evidence package can later include semantic claims if the
  credential is processed through RDFS/OWL/SHACL rules.

## Worked example: transformation evidence

Transformations are where regulated deployments will most often lose
auditability. A mapping or enrichment step should produce its own
evidence package, even if the input and output are later signed.

```turtle
<#transform-run-001> a fxev:EvidencePackage, fxev:VerifiedRun ;
  fxev:claim <#mapping-byte-identity>,
             <#mapping-software-claim>,
             <#mapping-semantic-claim> .

<#mapping-byte-identity> a fxev:ByteIdentityClaim ;
  fxev:sourceArtifact <sha256:SOURCE_TABLE_HASH> ;
  fxev:resultArtifact <sha256:OUTPUT_RDF_HASH> ;
  fxev:algorithm "CSVW/RML transform profile" .

<#mapping-software-claim> a fxev:SoftwareClaim ;
  fxev:implementation <git:COMMIT> ;
  fxev:verifiedBy "F*/Lean transform tests or theorem, as available" ;
  fxev:theoremStatus fxev:Measured .

<#mapping-semantic-claim> a fxev:SemanticClaim ;
  fxev:regime "RDF" ;
  fxev:proofProfile "construction claim, not entailment" ;
  fxev:refusesClaim "semantic entailment from the source table alone" .
```

This separates construction from entailment. A CSVW or RML mapping can
be deterministic and verified as a transformation without implying that
the source table logically entails the generated RDF under RDF Model
Theory.

## Regulated policy bundles

The profile should support named bundles. These are not code forks.
They are declarative requirements that a run can satisfy or refuse.

### `fxev:RegulatedRdfsSoundnessProfile`

Minimum requirements:

- RDF 1.1 or RDF 1.2 syntax mode stated.
- Canonicalization algorithm and hash algorithm stated.
- RDFS regime and fragment stated.
- Soundness theorem URI stated.
- Completeness status stated as one of complete, fragment-complete,
  carried hypothesis, or not claimed.
- W3C test-report URI attached.
- Implementation commit attached.
- All trust boundaries listed.

Intended uses: controlled vocabulary normalization, regulated
classification pipelines, life-sciences metadata enrichment, and
financial product taxonomy expansion.

### `fxev:RegulatedCredentialProfile`

Minimum requirements:

- VC Data Model version stated.
- JSON-LD context policy stated.
- RDFC/JCS canonicalization path stated.
- Cryptosuite stated.
- Verification method stated.
- HACL*/crypto boundary stated.
- Structural validation result stated.
- Signature result stated.
- Policy authorization result stated separately from signature result.

Intended uses: public-sector credentials, verifiable professional
licences, clinical-trial attestations, and supply-chain claims.

### `fxev:TransformationAuditProfile`

Minimum requirements:

- Source artifact hash.
- Mapping artifact hash.
- Output artifact hash.
- Transformation language and version.
- Determinism or non-determinism policy.
- Semantic claim kind: construction, entailment, validation, or
  enrichment.
- Test or theorem evidence.
- Refusal of stronger claims that are not established.

Intended uses: CSVW/RML table-to-RDF conversion, JSON-LD framing,
XSLT/XML transformations, evidence extraction, and reporting pipelines.

## Theorem URI scheme

The theorem registry should mint stable URIs before emitters are
implemented. A simple first scheme:

```text
urn:factoidal:theorem:<tree>:<module>:<name>
```

Examples:

```text
urn:factoidal:theorem:fstar:RDF.Entailment.RDFS:rdfs_closure_entails
urn:factoidal:theorem:fstar:RDF.Canonical:canonicalize_to_nquads_sorted
urn:factoidal:theorem:lean:RDF.Canonical:issuer_injective
urn:factoidal:theorem:lean:RDFS.FullClosure:fullClosure_saturated_complete
```

The URI is not the proof. It is a stable handle for a proof inventory
row that records:

- source tree: F* or Lean;
- module and theorem name;
- commit where the theorem was checked;
- exact statement;
- assumptions and imported trust base;
- proof status;
- related W3C section;
- related test suite;
- whether it is semantic, software-correctness, byte-identity, or
  cryptographic evidence.

The first emitter should refuse to cite a theorem URI unless that URI
exists in a generated registry.

## F* and Lean roles

Use F* as the shipping proof/extraction spine for the product runtime.
Its proof obligations are closest to the extracted OCaml/JS/wasm/C
surface and the current production story.

Use Lean 4 as an independent proof and conformance workbench:

- interactive theorem development for calculus-shaped logic;
- independent W3C harness execution;
- differential F* vs Lean checks;
- specification experiments where F* SMT automation would be brittle;
- certificate checkers that consume traces from the F* engine.

The most valuable shared artifact is not duplicated code. It is a
shared theorem/certificate vocabulary: names for semantic regimes,
fragments, transformations, algorithms, proof obligations, and refusal
reasons that both trees can emit and consume.

## Regulated-industry fit

The best near-term use cases are those where a signed RDF dataset must
survive audit, replay, and policy checks.

### Life sciences and clinical data

Use signed JSON-LD/RDF bundles for trial metadata, sample provenance,
lab assay facts, consent assertions, or safety signals. Factoidal can
add value by proving that normalization, closure, shape validation, and
selected inference steps preserve the relevant graph meaning. The
evidence package can record the exact theorem set and test suite state
used for a submission or internal audit.

### Finance and risk

Use RDF/OWL vocabularies for product classifications, counterparty
identifiers, regulatory obligations, and risk-control rules. The
valuable property is explainable monotonic derivation: a downstream
classification or obligation should be traceable to a signed source
dataset, a named entailment regime, and a checked closure/evaluation
path.

### Public sector identity and credentials

VC Data Integrity, did:key, RDFC-1.0, JSON-LD context validation, and
RDF entailment compose directly. The required caution is that a valid
signature is not a valid credential policy result. The evidence graph
must separately record structural validation, context validation,
cryptographic verification, semantic entailment, and application
authorization decisions.

### Supply chain and ESG reporting

Signed RDF graphs can carry product, location, batch, process, and
claim metadata. RDFS/OWL closure can normalize vocabulary variants and
derive reporting categories. RDFC and Data Integrity can make the
record tamper-evident. The weak point is transformation provenance:
every mapping, enrichment, and inference step needs an evidence node,
not only the final signed output.

## Issue #563 task breakdown

This page is the build-out surface for issue #563. The immediate work
should stay documentation-first until the claim vocabulary and example
graphs are stable.

1. **Define the minimal `fxev:` evidence vocabulary.**
   The v0.1 vocabulary above is the first draft. It should be reviewed
   against RDF/RDFS/OWL semantic claims, F*/Lean theorem rows, byte
   identity claims, and VC Data Integrity verification before any
   emitter depends on it.
2. **Link theorem-registry rows to stable theorem URIs.**
   The URI scheme above is a draft. The next documentation step is to
   extend the generated theorem registry with stable IDs, exact theorem
   statements, source tree, commit, assumptions, W3C section, and claim
   kind.
3. **Draft one concrete evidence graph example for an RDFS closure
   run.**
   The `#rdfs-run-001` example above is the first draft. It should be
   tightened with one real W3C or local fixture, real input/output
   hashes, and real theorem-registry URIs.
4. **Draft one concrete evidence graph example for VC Data Integrity
   verification.**
   The `#vc-run-001` example above is the first draft. It should be
   tightened with one real fixture, the actual verification method,
   canonical document hash, proof-config hash, signature result, and
   context-cache policy.
5. **Turn the examples into acceptance criteria or subtasks on #563.**
   The tracker should carry these six items as subtasks so progress is
   visible without reading the whole design note.
6. **Implement emitters/checkers only after the vocabulary is stable.**
   No runtime code should be written until at least the vocabulary, one
   RDFS example, one VC example, and theorem URI policy have survived a
   review pass. The first implementation should be a narrow emitter for
   one fixture, not a generalized framework.

Definition of done for the documentation phase:

- `fxev:` has a minimal term table with class/predicate meanings.
- The theorem URI scheme is tied to generated theorem-registry rows.
- One RDFS closure evidence graph uses real hashes and theorem IDs.
- One VC Data Integrity evidence graph uses real hashes, method IDs,
  context policy, and signature result.
- The page explicitly labels semantic, software-correctness,
  byte-identity, and cryptographic claims.
- #563 has matching subtasks or acceptance criteria.
- No emitters/checkers are started before the profile stabilizes.

## Gaps to track

1. Define the evidence vocabulary and a JSON/RDF report format for
   theorem-backed runs. This should sit beside the assurance inventory,
   not replace it.
2. Connect theorem registry rows to stable URIs. The current markdown
   registry is human-readable; evidence graphs need stable machine
   names.
3. Add an explicit bridge from RDFC canonical bytes to graph/dataset
   identity claims. Issue #451 is adjacent: duplicate renderers and
   canonicalization paths are a risk until one path is authoritative.
4. Extend semantic proof coverage for signed-data transformations:
   JSON-LD toRdf, context validation, proof-option canonicalization,
   and proof-set/chain semantics need clear theorems or refusal
   boundaries.
5. Keep OWL proof labels precise. Lean issue #466 records OWL RL
   licensing/completeness work, but some `_sound` names are licensing
   lemmas rather than model-theoretic truth preservation. The evidence
   vocabulary should distinguish those.
6. Close or explicitly carry F* RDFS blockers: #347, #335, and the
   dedup/string-key/canonicalization faithfulness family.
7. Define regulated profiles as policy bundles, not code forks:
   allowed regimes, allowed cryptosuites, allowed contexts, required
   theorem families, required test-suite floors, hash agility policy,
   and retention/audit metadata.
8. Decide where proof-carrying traces live. A small checker in Lean
   that consumes F* engine traces would let the production engine emit
   compact certificates while Lean verifies them independently.

## Proposed next issue

Open a tracker titled:

> Evidence graph profile: connect RDF/RDFS/OWL semantic theorems,
> F*/Lean software proofs, RDFC canonicalization, and VC Data Integrity.

Acceptance criteria:

- A minimal `fxev:` vocabulary is documented.
- One RDFS closure run can emit an evidence graph naming input hash,
  output hash, regime, fragment, implementation commit, theorem URI,
  and test-report URI.
- One VC Data Integrity verification can emit an evidence graph naming
  cryptosuite, verification method, context validation result,
  canonicalization algorithm, and signature result.
- F* and Lean can both emit the same evidence-shape fields for at least
  one shared W3C fixture.
- The profile states which claims are semantic, which are software
  correctness, which are byte identity, and which are cryptographic.
- The profile includes at least one regulated-industry policy bundle
  example.

This is the missing integration layer between the existing theorem
work and practical deployment. It is documentation and evidence
plumbing first; implementation should wait until the vocabulary and
claim boundaries are stable.
