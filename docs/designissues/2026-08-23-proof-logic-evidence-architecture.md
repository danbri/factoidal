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
