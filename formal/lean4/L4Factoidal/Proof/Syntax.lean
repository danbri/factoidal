/-
L4Factoidal.Proof.Syntax — FPP0, the Factoidal Proof Profile, version
0: the bundle vocabulary a heterogeneous proof chain is written in,
and `Derives`, the relation a checked bundle establishes.

Design: `docs/designissues/2026-08-26-proof-profile-fpp0-adoption.md`
sections 1 (four evidence levels), 2 (restricted control), 3 (the
theorem target carries the assumption frontier), 4 (identity is
syntactic), 8a (the degenerate bundle) and 8b (V must cite a
theorem); and
`docs/designissues/2026-08-26-proof-certificate-v1.md` sections 2
(trust model), 3 (RDFC-1.0 graph identity) and 5 (rejection table).

Milestone M0 of the adoption doc: freeze the model.

## What a bundle is

An `Artifact` names a value by its digest. An `Assumption` is an
external fact ENTERING the chain, at an evidence level that is never
foundational. A `BundleStep` is one node of the operation DAG: a
foundational rule application, or an adapter's evidence at V, R or A.
A `Bundle` is the four tables plus the claim it ends at.

## The foundational rule family

FPP0's only foundational rules are the RDF 1.1 Semantics section 8.1
and section 9.2 rows, and they are checked by the RDFS derivation
checker that already landed
(`L4Factoidal.RDFS.DerivationCheck`, commit cb9092d146f). This module
does not restate a single row: `Derives.rdfsRow` carries an
`RDFS.DerivesFull` term, and `Proof/Checker.lean` obtains that term
from `RDFS.stepOk_sound`.

Section 2 of the adoption doc bans a `semanticConsequence` rule. No
constructor below asks whether premises entail a conclusion. Every
foundational check is a finite membership or list test.

## Identity is syntactic (adoption doc section 4)

`Claim` has `DecidableEq`, and that decision is the join. A
`clif` claim carries ALPHA-NORMALISED CLIF text (`CL.Alpha.alphaCanon`
produces it) and joins by string equality; an `rdfDerivable` claim
joins on two RDFC-1.0 digests plus the triple. Nothing here decides
logical equivalence, and no reasoner is consulted to merge two
claims.

DEVIATION from the brief's sketch, recorded because it is visible in
every signature: the sketch spelled claims as `String`. They are a
structured `Claim` here. A bare string would force the kernel either
to PARSE a claim back into a triple before it could check an RDFS
row, or to carry the same content twice and hope the two agree. It
would also put an unproved obligation on the critical path — that the
string rendering is injective — because a non-injective rendering
lets a step derived for one claim be read as a proof of another.
`Claim.render` exists for display and is not the identity.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDFS.DerivationCheck
import L4Factoidal.RDF.Canonical

namespace L4Factoidal.FPP0

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-! ## Profile version

Adoption doc section 2: the control structures are a FIXED, VERSIONED
profile. A step naming another profile is rejected rather than read
under this one's rules (certificate v1 section 5, last row). -/

/-- The one profile string this kernel understands. -/
def fpp0Profile : String := "fpp0/1"

/-! ## Evidence levels (adoption doc section 1) -/

/-- The four evidence strengths. A result reports the MIX; it never
collapses them to one green tick.

* `foundational` — this kernel checked the step in a fixed calculus.
* `verifiedReplay` — a verified evaluator established the result for
  the declared semantics. Section 8b: such a step MUST cite a named
  theorem, by fully-qualified name and module.
* `replay` — deterministic and re-runnable with pinned inputs, tool
  and version; the evaluator is not in the trusted kernel.
* `attestation` — a named agent states that an operation was
  performed or a source observed. -/
inductive EvidenceLevel where
  | foundational
  | verifiedReplay
  | replay
  | attestation
  deriving DecidableEq, Repr, Inhabited

/-- What kind of value an artifact names. -/
inductive ArtifactKind where
  /-- An RDF graph, identified by its RDFC-1.0 canonical hash
  (certificate v1 section 3). -/
  | graph
  /-- An opaque byte sequence, identified by SHA-256 of the bytes. -/
  | bytes
  /-- A proposition. -/
  | claim
  /-- A SPARQL solution sequence. -/
  | solutions
  deriving DecidableEq, Repr, Inhabited

/-- The RDFC-1.0 canonical hash of a graph, read as the default graph
of a dataset — certificate v1 section 3. This is the digest an
`ArtifactKind.graph` artifact carries, and the only digest this
module computes. -/
def graphDigest (g : Graph) : String :=
  Dataset.canonicalHash { default := g, named := [] }

/-- A content-addressed value the bundle refers to.

`body` is the OPTIONAL inline graph of certificate v1 section 4
("inline artifact bodies may be omitted when the checker already
holds them; hashes may not"). When it is present the kernel checks
that its RDFC-1.0 digest is the declared one, so an inline body can
never disagree with the identity it is filed under. When it is absent
the digest is a REFERENCE the kernel does not resolve, and any leaf
fact about that graph has to enter as an assumption instead. -/
structure Artifact where
  id : String
  kind : ArtifactKind
  /-- RDFC-1.0 canonical hash for a graph; SHA-256 of the bytes
  otherwise. -/
  digest : String
  /-- Inline graph body, when the producer chose to include one. -/
  body : Option Graph := none
  deriving DecidableEq, Repr, Inhabited

/-- A named Lean statement. DATA: the kernel does NOT check that the
theorem exists or that it says what the name suggests — the same
discipline `checkDerivation_ignores_tags` states for the RDFS
checker's `assurance` field. What the kernel DOES enforce is
adoption-doc section 8b: a step at `verifiedReplay` with no citation
is REJECTED, not quietly re-levelled. -/
structure Citation where
  theoremName : String
  module : String
  deriving DecidableEq, Repr, Inhabited

/-- What a step or an assumption asserts.

Two shapes, and identity is structural equality on them.

* `rdfDerivable graph axioms t` — the triple `t` is derivable by the
  RDF 1.1 Semantics section 8.1 / section 9.2 rows from the graph
  whose RDFC-1.0 digest is `graph`, under the axiom set whose
  RDFC-1.0 digest is `axioms`. BOTH digests are part of the claim:
  derivability is relative to a regime, so a claim that named only
  the graph would be true under one axiom set and false under
  another, and two such claims must not join.
* `clif p` — a proposition, carried as ALPHA-NORMALISED CLIF text
  (adoption doc section 4). Two `clif` claims join exactly when their
  normalised text is equal. -/
inductive Claim where
  | rdfDerivable (graph : String) (axioms : String) (t : Triple)
  | clif (proposition : String)
  deriving DecidableEq, Repr

/-- A canonical default claim, so `Array` indexing with `[i]!` works
in tests and in a wasm ABI wrapper. Never reaches a reader: every use
is guarded by an in-range test. -/
instance : Inhabited Claim := ⟨.clif ""⟩

/-- Display text for a claim. PRESENTATION ONLY — `DecidableEq` on
`Claim` is the identity the kernel joins on, never this string. -/
def Claim.render : Claim → String
  | .rdfDerivable g a t =>
      "(rdf-derivable " ++ g ++ " " ++ a ++ " "
        ++ Canonical.canonQuad (none, t) ++ ")"
  | .clif p => p

/-- An external fact ENTERING the chain (adoption doc section 3).

`level` is never `foundational` — a fact this kernel checked is a
step, not an assumption. The rule is enforced by the CHECKER
(`Checker.lean`, `assumptionEnv`), not by the type, so that a bundle
declaring a foundational assumption is a REJECTION a test can pin.
Encoding it in the type would make the defect unrepresentable and
therefore untestable. -/
structure Assumption where
  id : String
  /-- What the assumption asserts. -/
  subject : Claim
  level : EvidenceLevel
  deriving DecidableEq, Repr

instance : Inhabited Assumption := ⟨{ id := "", subject := default, level := .attestation }⟩

/-- The claim text of an assumption, for a reader. Presentation only,
as `Claim.render` is. -/
def Assumption.claim (a : Assumption) : String := a.subject.render

/-- What licenses a step.

Adoption doc section 2's grammar has `rule` and `adapterEvidence`,
and nothing else. There is deliberately no rule whose check is "do
the premises entail this".

* `rule r graphArtifact axiomArtifact` — one RDF 1.1 Semantics row,
  read over the graph and axiom set those two artifacts name. Always
  foundational.
* `adapterEvidence adapter detail` — an adapter states its result.
  Never foundational: its conclusion enters the reported frontier as
  a named assumption. -/
inductive Justification where
  | rule (row : RuleId) (graphArtifact : String) (axiomArtifact : String)
  | adapterEvidence (adapter : String) (detail : String)
  deriving DecidableEq, Repr, Inhabited

/-- One node of the operation DAG.

`premises` are step or assumption IDS. The checker resolves each
against the prefix it has already accepted, so a premise can only
ever name something STRICTLY EARLIER — which is what makes a cycle,
a forward reference and a self-justification the same rejection. -/
structure BundleStep where
  id : String
  justification : Justification
  /-- Ids of earlier steps, or of declared assumptions. -/
  premises : List String
  conclusion : Claim
  level : EvidenceLevel
  /-- The profile the step is written in. Must be `fpp0Profile`. -/
  profile : String
  /-- Required at `verifiedReplay` (adoption doc section 8b). -/
  citation : Option Citation := none
  deriving DecidableEq, Repr

instance : Inhabited BundleStep :=
  ⟨{ id := "", justification := default, premises := [], conclusion := default,
     level := .attestation, profile := fpp0Profile, citation := none }⟩

/-- A proof bundle: the artifact table, the declared assumptions, the
steps in topological order, and the claim the bundle ends at. -/
structure Bundle where
  artifacts : Array Artifact
  assumptions : Array Assumption
  steps : Array BundleStep
  conclusion : Claim
  deriving DecidableEq, Repr

/-! ## `Derives` — what a checked bundle establishes

The FPP0 analogue of `RDFS.DerivesFull`, and the right-hand side of
`checkBundle_sound`. Adoption doc section 3: the theorem target is
`Derives assumptions conclusion`, NOT "the bundle is true".

Three of the four constructors are the RDFS family, and they carry
`DerivesFull` terms rather than restating any row.

⚠️ Adoption doc section 8a: this relation is TRIVIALLY satisfiable by
declaring the conclusion as an assumption — the `assumption`
constructor alone proves it. That is why `CheckResult` reports the
frontier, the per-level counts and `foundationalOnly`, and why a
reader must read those and not `valid` alone. -/
inductive Derives (Γ : List Assumption) : Claim → Prop where
  /-- An external fact, visible in the frontier. -/
  | assumption {a : Assumption} (h : a ∈ Γ) : Derives Γ a.subject
  /-- A triple of the graph the digest names — RDFS `base`. The
  digest link is part of the constructor, so the claim is about the
  graph the artifact is filed under and not about some other graph
  that happened to be exhibited. -/
  | rdfsBase {gd ad : String} {g : Graph} {t : Triple}
      (hdig : graphDigest g = gd) (hmem : t ∈ g) :
      Derives Γ (Claim.rdfDerivable gd ad t)
  /-- An axiomatic triple of the axiom set the digest names — RDFS
  `axiomatic`. -/
  | rdfsAxiom {gd ad : String} {ax : Graph} {t : Triple}
      (hdig : graphDigest ax = ad) (hmem : t ∈ ax) :
      Derives Γ (Claim.rdfDerivable gd ad t)
  /-- One RDF 1.1 Semantics inference row, over premises already
  derived about the SAME graph and the SAME axiom set. `hd` is the
  landed RDFS relation: `t` follows from the premise triples alone,
  with no axioms, so the row is context-free and composes by
  `DerivesFull.cut`. -/
  | rdfsRow {gd ad : String} {prem : List Triple} {t : Triple}
      (hp : ∀ u ∈ prem, Derives Γ (Claim.rdfDerivable gd ad u))
      (hd : DerivesFull [] prem t) :
      Derives Γ (Claim.rdfDerivable gd ad t)

/-- Weakening: more assumptions never lose a derivation. Used
nowhere in the soundness proof; stated because a reader checking that
`Derives` is a sensible consequence relation looks for it. -/
theorem Derives.weaken {Γ Δ : List Assumption} (hsub : ∀ a ∈ Γ, a ∈ Δ)
    {c : Claim} (h : Derives Γ c) : Derives Δ c := by
  induction h with
  | assumption ha => exact Derives.assumption (hsub _ ha)
  | rdfsBase hdig hmem => exact Derives.rdfsBase hdig hmem
  | rdfsAxiom hdig hmem => exact Derives.rdfsAxiom hdig hmem
  | rdfsRow _ hd ih => exact Derives.rdfsRow ih hd

/-! ## Collapsing an RDFS-only chain back to `DerivesFull`

An FPP0 chain over one graph and one axiom set is an RDF 1.1
Semantics derivation, and the theorem below turns it back into one.

⚠️ The two collision hypotheses are the cryptographic assumption,
written down instead of assumed silently: a claim names a graph by
its RDFC-1.0 digest, so recovering THE graph from a claim needs the
digest to name at most one graph. Lean cannot discharge that, and
this file does not pretend it can. No machine-checked instance of
`hcol` exists, for the same reason `closure_chain_wf` has none
(`skills/measuring-inference` section 4); `Proof/Tests.lean` carries
a concrete inhabitant of `Derives` instead, which is the part that
CAN be checked. -/

/-- Monotone in the axiom set. Every constructor but `axiomatic` is
insensitive to it, and `axiomatic` needs only the inclusion. -/
theorem derivesFull_axMono {ax ax' g : Graph} (hsub : ∀ u ∈ ax, u ∈ ax')
    {t : Triple} (h : DerivesFull ax g t) : DerivesFull ax' g t := by
  induction h with
  | base hm => exact DerivesFull.base hm
  | axiomatic hm => exact DerivesFull.axiomatic (hsub _ hm)
  | rdfD2 _ ih => exact DerivesFull.rdfD2 ih
  | rdfs2 _ _ ih1 ih2 => exact DerivesFull.rdfs2 ih1 ih2
  | rdfs3 _ _ hs ih1 ih2 => exact DerivesFull.rdfs3 ih1 ih2 hs
  | rdfs4a _ ih => exact DerivesFull.rdfs4a ih
  | rdfs4b _ hs ih => exact DerivesFull.rdfs4b ih hs
  | rdfs5 _ hs _ ih1 ih2 => exact DerivesFull.rdfs5 ih1 hs ih2
  | rdfs6 _ ih => exact DerivesFull.rdfs6 ih
  | rdfs7 _ _ ih1 ih2 => exact DerivesFull.rdfs7 ih1 ih2
  | rdfs8 _ ih => exact DerivesFull.rdfs8 ih
  | rdfs9 _ _ ih1 ih2 => exact DerivesFull.rdfs9 ih1 ih2
  | rdfs10 _ ih => exact DerivesFull.rdfs10 ih
  | rdfs11 _ hs _ ih1 ih2 => exact DerivesFull.rdfs11 ih1 hs ih2
  | rdfs12 _ ih => exact DerivesFull.rdfs12 ih
  | rdfs13 _ ih => exact DerivesFull.rdfs13 ih

/-- **An FPP0 chain about one graph IS an RDF 1.1 Semantics
derivation**, given that the two digests name those graphs and no
others, and that every assumption about them is itself derivable. -/
theorem Derives.toDerivesFull {Γ : List Assumption} {g ax : Graph}
    (hcolG : ∀ g' : Graph, graphDigest g' = graphDigest g → g' = g)
    (hcolA : ∀ a' : Graph, graphDigest a' = graphDigest ax → a' = ax)
    (hΓ : ∀ a ∈ Γ, ∀ u : Triple,
        a.subject = Claim.rdfDerivable (graphDigest g) (graphDigest ax) u →
        DerivesFull ax g u) :
    ∀ {c : Claim}, Derives Γ c → ∀ t : Triple,
      c = Claim.rdfDerivable (graphDigest g) (graphDigest ax) t →
      DerivesFull ax g t := by
  intro c h
  induction h with
  | @assumption a ha => intro t heq; exact hΓ a ha t heq
  | @rdfsBase gd ad g' t' hdig hmem =>
      intro t heq
      cases heq
      cases hcolG g' hdig
      exact DerivesFull.base hmem
  | @rdfsAxiom gd ad ax' t' hdig hmem =>
      intro t heq
      cases heq
      cases hcolA ax' hdig
      exact DerivesFull.axiomatic hmem
  | @rdfsRow gd ad prem t' _ hd ih =>
      intro t heq
      cases heq
      refine DerivesFull.cut (fun u hu => ih u hu u rfl) ?_
      exact derivesFull_axMono (by intro u hu; cases hu) hd

/-! ## Level counts and the check result -/

/-- The mix of evidence levels a result reports. Four numbers, never
one tick (adoption doc section 1). -/
structure LevelCounts where
  foundational : Nat
  verifiedReplay : Nat
  replay : Nat
  attestation : Nat
  deriving DecidableEq, Repr, Inhabited

def LevelCounts.zero : LevelCounts := ⟨0, 0, 0, 0⟩

def LevelCounts.bump (c : LevelCounts) : EvidenceLevel → LevelCounts
  | .foundational => { c with foundational := c.foundational + 1 }
  | .verifiedReplay => { c with verifiedReplay := c.verifiedReplay + 1 }
  | .replay => { c with replay := c.replay + 1 }
  | .attestation => { c with attestation := c.attestation + 1 }

/-- What a caller gets back.

`valid` alone is NOT a verdict that something was proved — adoption
doc section 8a. The fields a reader must combine with it:

* `assumptions` — the frontier, always reported.
* `counts` — the level mix over the steps the conclusion actually
  depends on.
* `foundationalOnly` — true only when the frontier is empty.
* `conclusionIsAssumption` — the degenerate shape, named. -/
structure CheckResult where
  valid : Bool
  conclusion : Claim
  /-- The assumption frontier. Every declared assumption, and every
  non-foundational step promoted to one. -/
  assumptions : Array Assumption
  /-- Level counts over the SUPPORT of the conclusion. -/
  counts : LevelCounts
  /-- The frontier is empty and the bundle is valid. -/
  foundationalOnly : Bool
  /-- The conclusion is itself a declared assumption. -/
  conclusionIsAssumption : Bool
  deriving DecidableEq, Repr

end L4Factoidal.FPP0
