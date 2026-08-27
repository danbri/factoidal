# FPP0 adopted: heterogeneous proof chains

Status: ADOPTED as the design direction, superseding the single-regime
parts of
[`2026-08-26-proof-certificate-v1.md`](2026-08-26-proof-certificate-v1.md).
Written 2026-08-26 on receipt of the owner-supplied handoff note
"Factoidal heterogeneous proof chains — IKL as proof interchange, Lean 4
checker, Why3 lessons, and a dataflow/proof DSL" (dated 2026-08-26,
reviewing snapshot `a7a33d6337ae95fa2fe208819967e4f2fbe55067`).

Its repo claims were checked before adoption: the four design documents
it cites all exist, and `FnDataset` / `cell` / `derive` are present in
`npm/factoidal/fn.js` and `fn.d.ts`. The five CL/IKL ABI ops it names
are the five that exist.

## What it changes

### 1. Four evidence strengths, never one green tick

The largest correction. The v1 design carried a single `assurance.tier`
per step and reported the chain's weakest link. That is too coarse. The
handoff separates:

| level | meaning |
|---|---|
| F — foundational | a small kernel checks a derivation in a fixed calculus |
| V — verified replay | a verified evaluator reruns a deterministic operation and establishes the result for the declared semantics |
| R — reproducible replay | deterministic and re-runnable with pinned inputs/tool/version; the evaluator is not in the trusted kernel |
| A — attestation | a named agent states that an operation was performed or a source observed |

A result must report the mix, not collapse it. The handoff's own
formulation of what a checker should be able to say:

> "the final IKL conclusion follows formally, conditional on two
> externally supplied transformation facts; three intermediate graph
> operations were independently replayed by verified evaluators."

### 2. FPP0 — restricted control, expressive claims

Do not make arbitrary IKL the proof-CONTROL language; that recreates
the original expressiveness problem inside the checker. Fix a small
versioned profile whose control structures are finite and
syntax-directed, while the objects being proved may be full IKL
proposition terms. Grammar: artifact, claim, step, premise, rule,
adapterEvidence, assumption, conclusion, semantics/profile.

**Banned by name:** a rule `semanticConsequence` that asks whether the
premises entail the conclusion. That hides theorem proving inside
"checking". Every foundational rule application must be locally
decidable and total.

### 3. The theorem target carries the assumption frontier

    checkBundle b = .ok r  ->  Derives r.assumptions r.conclusion

Not "the bundle is true". External and replay stages appear as NAMED
ASSUMPTIONS rather than being accidentally promoted to truth, which
makes the assurance frontier mathematically explicit. Adapter-specific
theorems later discharge individual assumptions without changing the
bundle structure.

What landed today (`cb9092d146f`) is the assumption-free special case:

    checkDerivation_sound : checkDerivation ax g d = true ->
                            DerivesFull ax g (d[i]!).conclusion

Every step in an RDFS-only chain is F-level, so `assumptions = empty`
and the general form reduces to it. The landed theorem composes into
FPP0 rather than being superseded by it.

### 4. Identity is syntactic; equivalence is a proof step

    alphaNorm(P) bytes = alphaNorm(Q)   -> cheap identity, may join
    P and Q provably equivalent          -> an explicit proof step
    P and Q true in one shared model     -> NOT identity

Join proof fragments on canonical syntactic identity — alpha-normalised
CLIF plus a digest. Never by deciding whether two arbitrary IKL
sentences are logically equivalent. `clAlphaNorm` already exists and is
the building block.

### 5. One node DAG, three projections

Not "dataflow plus a separate proof log". One immutable operation DAG
viewed as computation (values, operations, cache keys), proof (claims,
premises, evidence) and provenance (hashes, versions, signatures).

Consequence: **no second DSL and no second wasm payload.** The proof
checker becomes another operation group in the existing Lean module,
reached through the existing `l4_call` dispatch; `factoidal/proof` is a
thin wrapper over the already-loaded instance. Content addressing serves
both the cache and the proof references, which is a rare case where one
mechanism improves runtime performance and auditability together.

### 6. Adapters declare what their evidence establishes

Per technology, with staged strength rather than a blanket claim.
Schematron starts at R (pin input digest, schema digest, phase, XPath
version, processor version, SVRL digest) and rises to V only when a
verified XPath subset exists. RML pins module/profile set, mapping graph
digest, source digests, base IRI and function catalogue; **every
FnML/ad-hoc function becomes a visible subnode with its own evidence**
and must not disappear inside "RML succeeded". SPARQL is the early
V candidate. OWL evidence always names profile and semantics. IKLbase is
the reference adapter for a fully foundational multi-step proof.

### 7. Why3 is precedent, not kernel

Borrow the driver/adapter split, explicit transformations, replayable
sessions and multiple backends under one task model. Do not put Why3 in
the trusted computing base. A Why3 adapter may return a foundational
certificate from a backend that produces one, an R-level replay
certificate, or a proof term translated into FPP0 and checked by Lean.

## Two objections to the handoff

Recorded because adopting a design without stating where it is risky is
how the risk gets inherited silently.

### 8a. The degenerate bundle

If a bundle may declare assumptions, then
`Derives r.assumptions r.conclusion` is trivially satisfiable by
declaring the conclusion itself as an assumption. The handoff's
invariant "every external assumption remains visible in the final
checker result" covers disclosure but not this shape.

Required addition: a bundle whose conclusion is an assumption, or is
derivable from the assumptions alone with zero foundational steps, MUST
be reported as such and never as a proof. `foundational steps: 0` is a
verdict, not a footnote.

### 8b. V-level is easier to claim than to earn

The handoff's table gives "SPARQL evaluation using a verified Lean/F\*
evaluator" as a typical V example. Our SPARQL assurance today is
measured by W3C suite scores (631 pass, 0 fail out of 631 in the Lean
runner), NOT established by a refinement theorem over the whole algebra.
Suite conformance is evidence about tested inputs; V claims a property
of the operation.

Rule adopted here: **a V-level claim must cite a named theorem, by
fully-qualified name and module, whose statement covers the operation
performed.** Absent that, the level is R, however green the suite is. On
today's assurance inventory — 121 of 221 modules `merely-tot`, 11 at
`w3c-refinement` — most of our surface is R, and a design that lets us
write V by default would misreport exactly the thing this system exists
to report accurately.

This is the same failure the v1 design already guards against for the
`assurance` field, applied one level up.

## Milestones (from the handoff, adopted)

**M0 and M1 LANDED 2026-08-26** (`7fc183a7c19`:
`L4Factoidal/Proof/Syntax.lean`, `Proof/Checker.lean`,
`Proof/Tests.lean`): the `Bundle` vocabulary, the four evidence levels
in `CheckResult`, a total `checkBundle` with `checkBundle_sound` proved
unconditionally, and 57 `#guard`s of which 20 are rejections with no
defect accepted. Section 8a is implemented as REPORT, not rejection: a
degenerate bundle is valid and carries `conclusionIsAssumption = true`
beside `foundational steps: 0` counted over the SUPPORT of its
conclusion.

The ABI half landed the same day: `Wasm/Ops/Proof.lean` adds
`proofCheck(bundleJson)` and `proofInspect(bundleJson)` to
`Wasm/Dispatch.lean`'s op table. The op decodes, calls `checkBundle`,
and encodes; it checks nothing itself. The decoder rejects rather than
defaults — a missing or unrecognised `level`, `kind`, rule row or
`profile` is an error naming the field, and `decodeLevelName_inj`,
`decodeKindName_inj` and `decodeRowName_inj` prove that nothing but a
member's own name decodes to it. A decode failure is `{"ok":false}`
and is pinned apart from the kernel's `{"ok":true,"valid":false}`. 54
`#guard`s: the three fixture bundles both against literal values and
against the kernel's own `checkBundle` answer, plus ten rejections.
The whole-bundle round trip is pinned, not proved — the general
N-Triples round trip it would rest on
(`Syntax.SyntaxTheorems.graph_roundtrip`) is stated and unproved in
this tree. ⚠️ The committed wasm artifact does not serve the two ops
until `Wasm/build-wasm.sh` runs again; the npm wrapper is a separate
landing.

- **M0** freeze the model: FPP0 JSON/IKL vocabulary; F/V/R/A as part of
  checker output; canonical proposition identity via the existing CLIF
  parser and alpha normalization; DAG acyclicity, unique ids, digest
  references, versioning.
- **M1** minimal Lean kernel: total decoding + structural validation;
  small foundational calculus for IKLbase; soundness for accepted
  foundational steps; `Wasm/Ops/Proof.lean` with `proofCheck` dispatch;
  negative tests for cycles, missing artifact, wrong digest, unknown
  rule, malformed proposition, adapter precondition failure.
- **M2** existing verified operations as adapters (CL/IKL, SPARQL, OWL).
- **M3** heterogeneous demonstration: Schematron → RML → SPARQL → OWL →
  IKLbase, with the final check showing which assumptions remain
  external, rendered as both a dataflow graph and a proof graph over the
  same node ids.
- **M4** Why3 experiment, kept outside the TCB.

Already done, ahead of M1 and reusable in it: an RDFS witness emitter
(`4feb7d9a4cc`) and a total Lean checker proved sound and proved to
accept the emitter (`cb9092d146f`), 46 guards, 19 of them rejections
with no defect accepted.

## Non-negotiable invariants (from the handoff, adopted verbatim in force)

- Every accepted foundational rule application is locally decidable and
  total.
- Every semantics-changing translation is a first-class node with a
  named profile/version.
- Every external assumption remains visible in the final checker result.
- No successful tool exit code is automatically promoted to a theorem.
- No proposition is merged with another because a reasoner says they are
  equivalent; equivalence is evidence.
- Wasm-facing operations report proof hypotheses and preconditions
  instead of assuming them, following the existing CL/IKL op discipline.
