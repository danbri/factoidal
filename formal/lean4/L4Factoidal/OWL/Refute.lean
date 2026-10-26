/-
L4Factoidal.OWL.Refute — the OWL DL REFUTATION calculus, wave 1.

Port of `formal/fstar/Tableau.Refute.fst` — step 3 of
https://github.com/danbri/factoidal/issues/548 . Where
`L4Factoidal/OWL/Materialise.lean` is positive-sound only (it writes
entailed memberships and never detects unsatisfiability), this module
runs a bounded clash search over an executable RDF state.

## The verdicts (three-valued since 2026-08-25, issue 586)

`tableauConsistent` answers `Option Bool` with three public outcomes:

* `some false` — REFUTED by an executable clash on every explored
  branch, or by a graph-level check. OWL 2 Direct Semantics
  unsatisfiability is the intended contract, but a general theorem
  connecting this search to `Refuted` does not yet exist. This is the
  only verdict wired into suite scoring.
* `some true` — the represented deterministic rules reached
  quiescence, one branch remained open, and no represented branch,
  merge, nominal, or witness obligation remained. This is not a
  candidate-model certificate and does not prove satisfiability.
* `none` — the visit budget ran out or bounded witness construction
  left an unresolved obligation. Indeterminate, never collapsed into
  either Boolean.

`refute` is the refutation-only VIEW of the same search (defined
through `tableauConsistent`; one search path, no duplicate
dispatch): `some false` = refuted, `none` = not refuted; quiescence,
visit exhaustion, and withheld obligations are deliberately
indistinguishable. The harness's
inconsistency judges consume this view.

## Relation to the declarative calculus (`OWL/Tableau.lean`)

`OWL/Tableau.lean` is the PROOF HOME: the `Derives`/`Refuted` clash
calculus over the OWL 2 Direct Semantics fragment of names, Boolean
connectives, value restrictions and (qualified) cardinality, with
soundness proofs in `TableauTheorems.lean`. This module is the
EXECUTABLE engine over RDF graphs. On the shared fragment each
procedural clash source corresponds to a `Refuted` constructor:

* `clashForLabel` complement arm ↔ `Refuted.clash`;
* `owl:Nothing` label arm ↔ `Refuted.botClash`;
* min/max label pairs (`existsMaxLt`/`existsMaxQualLt`) ↔
  `Refuted.minMaxClash` / `.minMaxClashQ` / `.minQMaxClash`;
* counted provably-distinct successors over a `≤ k` label ↔
  `Refuted.maxClash` / `.maxClashQ`;
* `search`'s union branching ↔ `Refuted.disjSplit`;
* the ≤-rule witness merge (`pendingMerge`/`mergeInto`) ↔
  `Refuted.leqMerge`;
* `ensureWitnesses` ↔ `Refuted.exWitness`.

The procedural fragment includes nominal rules, datatype value-space
clashes C5/C6, graph-level checks G1–G9, TBox unfolding through
`collectAxioms`, and inverse roles. Its witness depth and per-pass
generation are bounded, and its rule set does not cover all OWL 2 DL.
Unfinished lower-bound witness obligations are reported as
indeterminate instead of open. `RefuteTests.lean` keeps an
instance-level paired witness: one input refuted here by `#guard`
and refuted in the calculus by an explicit `Refuted` derivation. The
general linkage — an abstraction from a clash trace to a serialisable
`Refuted` derivation, `refute g b = some false → Refuted R A` on the
shared fragment — is the certificate-checker rung
`OWL/Tableau.lean`'s header names; tracked as follow-up 6 on
https://github.com/danbri/factoidal/issues/586 .

## What is NOT here, named

The F* module carries several more waves. Missing executable coverage
normally withholds a refutation. That observation is not a general
soundness proof for the rules that are present:

* the counting oracle and the analytic min-sum counting clash
  (`OWL/CountingOracle.lean` exists, with a proved Farkas validator,
  but is not yet consulted from this search);
* blocking for cyclic or deeper existential expansions;
* generated pairwise-distinct witnesses for minimum cardinality;
* DPLL-style branch-ordering heuristics.

(The ≤-rule itself and the datatype facet/cardinality clashes were
on this list until 2026-08-23; they are ported — see the ≤-rule and
"Datatype value spaces" sections below.)

## Every label is in negation normal form

After `nnf`, `complement` wraps only a named class, a `hasValue`, a
`oneOf` or a `dataRestriction` — so the complement clash reduces to
structural matching rather than a search. `nnfNeg` of an unreadable
expression is `unknown`, which DROPS the constraint: dropping one can
only lose clashes, never invent them.
-/
import L4Factoidal.OWL.ClassExpr
import L4Factoidal.OWL.DatatypePattern
import L4Factoidal.XSD.Facets

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.XSD

/-! ## Vocabulary this module needs and `OWL/Vocabulary.lean` does not
carry -/

def owlAllDifferent : WfIri := ⟨"http://www.w3.org/2002/07/owl#AllDifferent", rfl⟩
def owlDistinctMembers : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#distinctMembers", rfl⟩
def owlHasSelf : WfIri := ⟨"http://www.w3.org/2002/07/owl#hasSelf", rfl⟩
def owlAllDisjointProperties : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#AllDisjointProperties", rfl⟩
def owlBottomObjectProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#bottomObjectProperty", rfl⟩
def owlBottomDataProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#bottomDataProperty", rfl⟩
def owlTopObjectProperty : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#topObjectProperty", rfl⟩
def owlDisjointUnionOf : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#disjointUnionOf", rfl⟩

/-- `EXT(owl:bottomObjectProperty) = EXT(owl:bottomDataProperty) = ∅`
    in every model, so any obligation to HAVE a successor on one is
    unsatisfiable and any asserted triple over one is false. -/
def isBottomProp (p : WfIri) : Bool :=
  p == owlBottomObjectProperty || p == owlBottomDataProperty

/-! ## Negation normal form

Each rewrite is the corresponding Direct Semantics identity:
`¬⊤ = ⊥`, `¬¬C = C`, `¬(C ⊓ D) = ¬C ⊔ ¬D`, `¬∃p.C = ∀p.¬C`,
`¬(≥ k p) = (≤ k-1 p)` for `k ≥ 1` and `⊥` for `k = 0`,
`¬(≤ k p) = (≥ k+1 p)`, and `= k p` is `(≥ k p) ⊓ (≤ k p)`. -/

mutual

partial def nnf : ClassExpr → ClassExpr
  | .complement d      => nnfNeg d
  | .intersection cs   => .intersection (cs.map nnf)
  | .union cs          => .union (cs.map nnf)
  | .someOf p d        => .someOf p (nnf d)
  | .allOf p d         => .allOf p (nnf d)
  | .minQualCard k p d => .minQualCard k p (nnf d)
  | .maxQualCard k p d => .maxQualCard k p (nnf d)
  -- `= 0 p` is `≤ 0 p` EXACTLY: `≥ 0 p` holds of every individual in
  -- every model, so keeping it as a conjunct puts a tautology into
  -- the label set. That is not cosmetic — an axiom's left-hand side
  -- is matched by structural equality, so a node that derives
  -- `≤ 0 p` could never match an axiom written `⊓[≥ 0 p, ≤ 0 p]`.
  | .exactCard k p     =>
      if k == 0 then .maxCard 0 p
      else .intersection [.minCard k p, .maxCard k p]
  | .exactQualCard k p d =>
      let d' := nnf d
      if k == 0 then .maxQualCard 0 p d'
      else .intersection [.minQualCard k p d', .maxQualCard k p d']
  | c => c

partial def nnfNeg : ClassExpr → ClassExpr
  | .named x =>
      if x == owlThing then .named owlNothing
      else if x == owlNothing then .named owlThing
      else .complement (.named x)
  | .complement d      => nnf d
  | .intersection cs   => .union (cs.map nnfNeg)
  | .union cs          => .intersection (cs.map nnfNeg)
  | .someOf p d        => .allOf p (nnfNeg d)
  | .allOf p d         => .someOf p (nnfNeg d)
  | .hasValue p v      => .complement (.hasValue p v)
  | .minCard k p       => if k == 0 then .named owlNothing else .maxCard (k - 1) p
  | .maxCard k p       => .minCard (k + 1) p
  | .exactCard k p     =>
      if k == 0 then .minCard 1 p
      else .union [.maxCard (k - 1) p, .minCard (k + 1) p]
  | .minQualCard k p d =>
      if k == 0 then .named owlNothing else .maxQualCard (k - 1) p (nnf d)
  | .maxQualCard k p d => .minQualCard (k + 1) p (nnf d)
  | .exactQualCard k p d =>
      let d' := nnf d
      if k == 0 then .minQualCard 1 p d'
      else .union [.maxQualCard (k - 1) p d', .minQualCard (k + 1) p d']
  -- A nominal and a facet-restricted datatype have no closed-form
  -- negation in this AST, so they are WRAPPED and treated as atomic.
  -- Nothing is dropped.
  | .oneOf ms          => .complement (.oneOf ms)
  | .dataRestriction dt fs => .complement (.dataRestriction dt fs)
  -- An unreadable expression's negation DROPS the constraint. Fewer
  -- constraints means fewer clashes, never a wrong one.
  | .unknown           => .unknown

end

/-! ## Structural equality, and why `unknown` is not equal to itself

`ClassExpr.beq` says two `unknown`s match, which is the right answer
for a syntactic comparison. It is the wrong one HERE: two
unparseable expressions are no evidence of denoting the same class,
and a refuter that treated them as one could close a branch on a
coincidence of failure. `ceEq` is `beq` with that one case removed,
and it is what every clash and axiom match uses. -/

mutual

partial def ceDefinite : ClassExpr → Bool
  | .unknown            => false
  | .someOf _ d         => ceDefinite d
  | .allOf _ d          => ceDefinite d
  | .complement d       => ceDefinite d
  | .minQualCard _ _ d  => ceDefinite d
  | .maxQualCard _ _ d  => ceDefinite d
  | .exactQualCard _ _ d => ceDefinite d
  | .intersection ds    => ceListDefinite ds
  | .union ds           => ceListDefinite ds
  | _                   => true

partial def ceListDefinite : List ClassExpr → Bool
  | []      => true
  | c :: tl => ceDefinite c && ceListDefinite tl

end

def ceEq (a b : ClassExpr) : Bool := ceDefinite a && ClassExpr.beq a b

/-! ## The tableau state -/

structure RNode where
  id     : Subject
  /-- Invariant: every label is in negation normal form. -/
  labels : List ClassExpr

/-- An edge the expansion created. `counts` separates a
    `hasValue`-derived edge, which holds in EVERY model and may
    therefore be counted against a cardinality bound, from an
    existential witness, which may coincide with an existing
    successor in some model and is used only to carry `∀`
    propagation. Counting a witness would fabricate cardinality
    clashes. -/
structure REdge where
  s      : Subject
  p      : WfIri
  o      : Term
  counts : Bool

structure RState where
  nodes      : List RNode := []
  extra      : List REdge := []
  fresh      : Nat := 0
  /-- Witness depth per minted blank node. An ABox individual is at
      depth 0. The cap is what stops a cyclic TBox (`X ⊑ ∃p.X`) from
      growing an infinite `∃`-chain. An obligation withheld at this
      cap makes the final verdict indeterminate. -/
  wdepth     : List (BNodeId × Nat) := []
  inv        : List (WfIri × WfIri) := []
  subprop    : List (WfIri × WfIri) := []
  transProps : List WfIri := []
  funcProps  : List WfIri := []
  /-- Declared `rdfs:range` pairs. A range confines a property's
      fillers to a datatype, which is what lets the value-space rules
      bound them. -/
  ranges     : List (WfIri × WfIri) := []
  /-- Anonymous datatype ranges, parsed once at initialisation. Named
      datatype ranges stay in `ranges`; incomplete parses are stored
      as `unknown` and remain inert. -/
  anonymousRanges : List (WfIri × ClassExpr) := []
  /-- `p ↦ {q | q ⊑* p}` and `p ↦ {q | p ⊑* q}`, computed ONCE at
      `initState` for every property the subproperty table mentions.
      Both closures are fixpoints over that table, and the clash rules
      ask for them once per property per node per ROUND — recomputing
      them there put `type-inconsistency` from 6 seconds to 79. A
      property in no subproperty pair is absent from the table and
      falls back to `[p]`, which is what the fixpoint returns for
      it. -/
  subClosure : List (WfIri × List WfIri) := []
  supClosure : List (WfIri × List WfIri) := []
  /-- The INDEXED view of the input graph, built once. The successor
      lookups and the `owl:differentFrom` test run per label per node
      per round, and a list scan of the whole graph at each of them
      is what made `type-inconsistency` take 78 seconds. -/
  store      : Store := Store.ofGraph []
  /-- Terms this branch HYPOTHESISES to denote one domain element,
      as (absorbed, representative) pairs. The ≤-rule writes them;
      `labelsOf` and `successorsOf` read them.

      Identification is done at READ TIME, not by rewriting edges.
      An edge asserted in the input graph cannot be rewritten at all,
      and the materialisation pass puts its own existential witnesses
      INTO the graph — so an edge-rewriting merge silently missed
      every successor that came from there, which is most of them on
      the real path. Pooling at read time covers both. -/
  ident      : List (Term × Term) := []
  /-- The TBox `collectAxioms` read, as (antecedent, consequent)
      pairs. `search` carries it as an argument; the clash rules need
      it too, and a clash rule cannot take one more argument without
      threading it through `clashNodes`, so it is carried here as
      well. Written once, by `tableauConsistent`. -/
  tbox       : List (ClassExpr × ClassExpr) := []

def maxWitnessDepth : Nat := 3
def maxGeneratedWitnesses : Nat := 6

/-! ## Label bookkeeping -/

def memCe (c : ClassExpr) (ls : List ClassExpr) : Bool :=
  ls.any (fun l => ceEq c l)

/-- Is a union choice contradicted by an explicit complementary label?
    This is exactly the complement relation used by the clash rule.
    ceEq rejects unknown against unknown, so parse failure cannot
    eliminate a live choice. -/
def unionChoiceContradicted (c : ClassExpr) (ls : List ClassExpr) : Bool :=
  ls.any (fun l =>
    match c, l with
    | .complement a, b => ceEq a b
    | a, .complement b => ceEq a b
    | _, _ => false)

/-- Union choices not already contradicted, preserving source order. -/
def liveUnionChoices (cs ls : List ClassExpr) : List ClassExpr :=
  cs.filter (fun c => !(unionChoiceContradicted c ls))

/-- The representative of a term under this branch's
    identifications. -/
partial def repOf (st : RState) (t : Term) : Term :=
  match st.ident.find? (fun q => q.1 == t) with
  | some (_, r) => if r == t then t else repOf st r
  | none        => t

def identifiedWith (st : RState) (t : Term) : List Term :=
  if st.ident.isEmpty then [t]
  else
    let r := repOf st t
    (t :: r :: (st.ident.filterMap (fun q =>
      if repOf st q.1 == r then some q.1 else none))).eraseDups

/-- `addLabel` keeps ONE entry per subject, so the unidentified case
    is a LOOKUP and not a gather. The `filter`-then-`flatMap` version
    this replaces scanned the whole node list to the end every time,
    and `clashNodes` calls it once per node — quadratic in the node
    count, per round.

    With identifications present the read is POOLED across the group:
    once two terms are identified, a clash entailed by the UNION of
    their labels has to be visible from either one. -/
def labelsOf (st : RState) (i : Subject) : List ClassExpr :=
  if st.ident.isEmpty then
    match st.nodes.find? (fun n => n.id == i) with
    | some n => n.labels
    | none   => []
  else
    ((identifiedWith st i.toTerm).filterMap termAsSubject).flatMap (fun j =>
      match st.nodes.find? (fun n => n.id == j) with
      | some n => n.labels
      | none   => [])

/-- Add one label. `unknown` is never stored: it constrains nothing
    and would only make the label sets longer. The Boolean says
    whether the state changed, which is what the expansion loop's
    stopping rule reads. -/
def addLabel (st : RState) (i : Subject) (c : ClassExpr) : RState × Bool :=
  match c with
  | .unknown => (st, false)
  | _ =>
    if memCe c (labelsOf st i) then (st, false)
    else if st.nodes.any (fun n => n.id == i) then
      ({ st with nodes := st.nodes.map (fun n =>
           if n.id == i then { n with labels := n.labels ++ [c] } else n) }, true)
    else
      ({ st with nodes := st.nodes ++ [{ id := i, labels := [c] }] }, true)

/-! ## The role box

A declared `owl:inverseOf` or `rdfs:subPropertyOf` pair is schema
level: collected once and read-only for the rest of the run. The RL
closure already applies them to the triples the document asserts;
these tables are what makes the edges the EXPANSION creates
role-aware, which the closure never sees. -/

def collectPairs (g : Graph) (pred : WfIri) : List (WfIri × WfIri) :=
  g.filterMap (fun t =>
    if t.p == pred then
      match t.s, t.o with
      | .iri a, .iri b => some (a, b)
      | _, _           => none
    else none)

def collectTypedIris (g : Graph) (cls : WfIri) : List WfIri :=
  g.filterMap (fun t =>
    if t.p == rdfType && t.o == Term.iri cls then
      match t.s with
      | .iri a   => some a
      | .bnode _ => none
    else none)

def inversesOf (inv : List (WfIri × WfIri)) (p : WfIri) : List WfIri :=
  inv.filterMap (fun (a, b) =>
    if a == p then some b else if b == p then some a else none)

/-- The reflexive-transitive closure of `rdfs:subPropertyOf` BELOW
    `p`: every `q` with `EXT(q) ⊆ EXT(p)` in every model, so a
    `q`-edge counts wherever a `p`-successor is asked for. -/
partial def subpropertiesOfRaw (sp : List (WfIri × WfIri)) (p : WfIri) : List WfIri :=
  let rec go (acc : List WfIri) (fuel : Nat) : List WfIri :=
    match fuel with
    | 0     => acc
    | n + 1 =>
      let more := sp.filterMap (fun (a, b) =>
        if acc.contains b && !(acc.contains a) then some a else none)
      if more.isEmpty then acc else go (acc ++ more.eraseDups) n
  go [p] (sp.length + 1)

/-- The reflexive-transitive closure of `rdfs:subPropertyOf` ABOVE
    `p`: every `q` with `EXT(p) ⊆ EXT(q)`, so a `∀q.D` binds every
    `p`-filler too. -/
partial def superpropertiesOfRaw (sp : List (WfIri × WfIri)) (p : WfIri) : List WfIri :=
  let rec go (acc : List WfIri) (fuel : Nat) : List WfIri :=
    match fuel with
    | 0     => acc
    | n + 1 =>
      let more := sp.filterMap (fun (a, b) =>
        if acc.contains a && !(acc.contains b) then some b else none)
      if more.isEmpty then acc else go (acc ++ more.eraseDups) n
  go [p] (sp.length + 1)

/-- The memoised lookups. A property absent from the table is in no
    subproperty pair, and the fixpoint returns `[p]` for it. -/
def subsOf (st : RState) (p : WfIri) : List WfIri :=
  match st.subClosure.find? (fun q => q.1 == p) with
  | some (_, xs) => xs
  | none         => [p]

def supsOf (st : RState) (p : WfIri) : List WfIri :=
  match st.supClosure.find? (fun q => q.1 == p) with
  | some (_, xs) => xs
  | none         => [p]

/-- The `p`-successors of `i`: the graph's `q`-edges for every
    `q ⊑* p`, the inverse direction of each, and the expansion's own
    edges. `counted` restricts the result to successors licensed for
    positive cardinality and distinctness reasoning. A maximum of zero
    instead asks for every required successor: one is already too many,
    without any distinctness premise. -/
def successorsOf (_g : Graph) (st : RState) (i : Subject) (p : WfIri)
    (counted : Bool) : List Term :=
  let roles := subsOf st p
  let selves := (identifiedWith st i.toTerm).filterMap termAsSubject
  let fromGraph := selves.flatMap (fun j =>
    roles.flatMap (fun r => (st.store.withSubjPred j r).map (·.o)))
  let viaInverse := selves.flatMap (fun j =>
    roles.flatMap (fun r =>
      (inversesOf st.inv r).flatMap (fun r' =>
        (st.store.withPredObj r' j.toTerm).map (·.s.toTerm))))
  let fromExtra := st.extra.filterMap (fun e =>
    if selves.contains e.s && roles.contains e.p && (!counted || e.counts)
    then some e.o else none)
  -- The inverse direction of an EXPANSION edge. `viaInverse` above
  -- reads it off the input graph only, so a witness minted on `invR`
  -- was invisible when the witness's own `r`-successors were asked
  -- for. That is the shape of the OilEd inverse-role fixtures:
  -- `x invR y` mints `y`, and `y`'s `r`-successors must include `x`.
  -- `Inv(r') = r` holds in every model, so the edge `(a, r', b)`
  -- entails `(b, r, a)` and reading it back is sound.
  let inverseRoles := roles.flatMap (fun r => inversesOf st.inv r)
  let fromExtraInverse := st.extra.filterMap (fun e =>
    if inverseRoles.contains e.p && selves.any (fun j => e.o == j.toTerm)
       && (!counted || e.counts)
    then some e.s.toTerm else none)
  let raw := (fromGraph ++ viaInverse ++ fromExtra ++ fromExtraInverse).eraseDups
  -- Identified successors collapse to ONE term, which is what makes a
  -- merge REDUCE the count a `≤ k` bound is measured against.
  if st.ident.isEmpty then raw else (raw.map (repOf st)).eraseDups

/-- `Trans(r)` holds for `r` and for its inverse alike. -/
def roleIsTransitive (st : RState) (r : WfIri) : Bool :=
  st.transProps.contains r || (inversesOf st.inv r).any (st.transProps.contains ·)

/-! ## Provable distinctness

No unique-name assumption: two different IRIs may denote one
individual. Distinctness must be PROVED, and there are two ways to
prove it here — an `owl:differentFrom` assertion, and two literals
whose lexical forms differ under the same datatype. -/

def differentFromAsserted (g : Graph) (a b : Term) : Bool :=
  g.any (fun t =>
    t.p == owlDifferentFrom &&
    ((t.s.toTerm == a && t.o == b) || (t.s.toTerm == b && t.o == a)))


/-- Datatypes whose LEXICAL MAPPING is injective: distinct literals
    in the lexical space map to distinct members of the value space,
    so lexical inequality entails value inequality.

    XSD Datatypes §2.1 to §2.3 give each datatype a lexical space, a
    value space, and a lexical mapping from the first to the second.
    That mapping is many-to-one for most datatypes. `"1"` and `"01"`
    are distinct literals in the lexical space of `xsd:integer` and
    map to one value; `"1.0"` and `"1.00"` likewise for
    `xsd:decimal`; two `rdf:XMLLiteral` literals differing only in
    insignificant whitespace map to one value after exclusive XML
    canonicalization.

    The lexical mapping of `xsd:string` is injective, so `"colour"`
    and `"color"` are distinct values there. That is why the test is
    per-datatype and not general.

    The first version of this predicate returned `true` for every
    datatype. `WebOnt-miscellaneous-202` asserts a CONSISTENT premise
    with a functional datatype property whose two asserted values are
    the same `rdf:XMLLiteral` written with different whitespace. The
    predicate reported them distinct, the cardinality clash fired,
    and the refuter reported no model for a premise that has one.

    Kept for the record of that incident. `literalValuesDistinct`
    below is what `provablyDistinct` now calls; this predicate decides
    a LEXICAL question and could never see the value-level cases. -/
def lexicalMappingIsInjective (dt : WfIri) : Bool := dt == xsdString

/-! ### Literal distinctness decided on VALUES, not on lexical forms

`lexicalMappingIsInjective` answers a lexical question, and only for
`xsd:string`. It cannot see that `"18"^^xsd:integer` and
`"19"^^xsd:integer` denote different integers, which is what
`functionality-clash` needs, and it cannot see that two
`rdf:XMLLiteral` literals with DIFFERENT canonical forms denote
different values, which is what `WebOnt-miscellaneous-203` and
`-204` need.

The predicates below decide the same question one level lower, on the
data value. Each arm returns `true` only where the OWL 2 datatype map
fixes the two values as different, and `false` — WITHHOLD — everywhere
it cannot decide. Withholding costs refutations; a wrong `true` costs
soundness, and `WebOnt-miscellaneous-202` is the standing witness for
that direction. -/

/-- The part of the `xsd:float` / `xsd:double` value space this module
    decides exactly.

    XSD Datatypes §3.2.4 (float) and §3.2.5 (double) give the value
    space as the IEEE single/double grid together with
    `positiveZero`, `negativeZero`, `positiveInfinity`,
    `negativeInfinity` and `NaN`, and state that positive zero and
    negative zero are two DISTINCT values. OWL 2 Syntax §4.3 adopts
    those value spaces unchanged.

    The lexical-to-value map of the finite non-zero part ROUNDS to the
    nearest grid point, so two different decimal lexical forms can
    denote one value. This classifier therefore names only the values
    it can read off the lexical form with no rounding: the two
    infinities, `NaN`, and the two zeroes. Everything else is `none`
    and the caller withholds. -/
inductive FpExact where
  | posZero | negZero | posInf | negInf | nan
  deriving DecidableEq, Repr

def fpExactValue (lex : String) : Option FpExact :=
  if lex == "NaN" then some .nan
  else if lex == "INF" || lex == "+INF" then some .posInf
  else if lex == "-INF" then some .negInf
  else match parseDecimalRat lex with
    | some r =>
        if r.num == 0 then
          some (if lex.startsWith "-" then .negZero else .posZero)
        else none
    | none => none

/-- The exact rational a literal on the `owl:real` line denotes.
    `xsd:float` and `xsd:double` are absent for the reason
    `XSD.termExactRat` states: their value is the ROUNDED grid point,
    in a different value space. `owl:real` itself has no lexical
    space in OWL 2 Syntax §4.1, so it is absent too. -/
def literalExactRat (l : Literal) : Option XSD.Rat :=
  if isIntegerFamilyDatatype l.datatype then
    (parseFacetInt l.lexicalForm).map (fun v => { num := v, den := 1 })
  else if l.datatype == xsdDecimal then parseDecimalRat l.lexicalForm
  else if l.datatype == owlRational then parseRationalLex l.lexicalForm
  else none

def literalBoolValue (l : Literal) : Option Bool :=
  if l.datatype == xsdBoolean then
    if l.lexicalForm == "true" || l.lexicalForm == "1" then some true
    else if l.lexicalForm == "false" || l.lexicalForm == "0" then some false
    else none
  else none

/-- Provable data-value equality for negative data-property assertions.
    Exact term equality and the built-in OWL datatype map are delegated
    to `termProvablyEqual`; RDF XML literals additionally compare their
    exclusive canonical forms. `owl:sameAs` between datatype IRIs is
    deliberately irrelevant under Direct Semantics, where individual
    and datatype interpretations are separate. -/
def literalTermsProvablyEqualInStore (_st : Store) (a b : Term) : Bool :=
  termProvablyEqual a b ||
  match a, b with
  | .literal la, .literal lb =>
      la.val.datatype == rdfXMLLiteral &&
      lb.val.datatype == rdfXMLLiteral &&
      XmlCanon.xmlCanonEq la.val.lexicalForm lb.val.lexicalForm
  | _, _ => false

/-- Do these two literals denote DIFFERENT data values?

    `rdf:XMLLiteral` first: RDF 1.1 Concepts §5.1 maps a well-formed
    lexical form to its exclusive canonical XML form, and that map is
    injective on canonical forms — so two XMLLiterals denote different
    values exactly when their canonical forms differ. This arm keeps
    `WebOnt-miscellaneous-202` (same canonical form, no clash) apart
    from `-203` and `-204` (different canonical forms, clash), which a
    lexical comparison cannot do in either direction.

    Otherwise the two datatypes are placed in the value-space families
    of `XSD.classifyFamily`, whose members OWL 2 Syntax §4 fixes as
    PAIRWISE DISJOINT. Two literals in different families therefore
    denote different values. Inside one family the value is computed
    and compared: exact rationals on the `owl:real` line, the Boolean
    pair, `xsd:string` (whose lexical map is the identity), and the
    exactly-readable part of the floating-point grid. A datatype
    outside every family, or a lexical form the arm cannot read,
    withholds. -/
def literalValuesDistinct (a b : Literal) : Bool :=
  if a.datatype == rdfXMLLiteral && b.datatype == rdfXMLLiteral then
    !XmlCanon.xmlCanonEq a.lexicalForm b.lexicalForm
  else
    match classifyFamily a.datatype, classifyFamily b.datatype with
    | some fa, some fb =>
        if fa != fb then true
        else match fa with
          | .string  => a.lexicalForm != b.lexicalForm
          | .boolean =>
              match literalBoolValue a, literalBoolValue b with
              | some x, some y => x != y
              | _,      _      => false
          | .numeric =>
              match literalExactRat a, literalExactRat b with
              | some x, some y => !ratEq x y
              | _,      _      => false
          | .float | .double =>
              match fpExactValue a.lexicalForm, fpExactValue b.lexicalForm with
              | some x, some y => x != y
              | _,      _      => false
    | _, _ => false

def provablyDistinct (g : Graph) (a b : Term) : Bool :=
  if a == b then false
  else match a, b with
    | .literal x, .literal y =>
        literalValuesDistinct x.val y.val || differentFromAsserted g a b
    | _, _ => differentFromAsserted g a b

/-- Distinctness between identification groups. If any names pooled
    into the two groups are graph-asserted different, the groups cannot
    be identified. This is the no-unique-name counterpart of looking
    through `labelsOf`: every assertion carried by an alias remains
    visible after later merges. -/
def provablyDistinctGrouped (g : Graph) (st : RState) (a b : Term) : Bool :=
  (identifiedWith st a).any (fun x =>
    (identifiedWith st b).any (fun y => provablyDistinct g x y))

/-- Is there a subset of `ts` of size `n` whose members are PAIRWISE
    provably distinct? Branch on the first element: taking it filters
    the rest against it, so every chosen pair passed a filter and
    pairwise distinctness of the whole chosen set follows. -/
partial def existsDistinctSubset (g : Graph) (ts : List Term) (n : Nat) : Bool :=
  if n == 0 then true
  else match ts with
    | []      => false
    | t :: tl =>
        existsDistinctSubset g (tl.filter (provablyDistinct g t ·)) (n - 1)
        || existsDistinctSubset g tl n

/-! ## Clash rules

Each returns `true` only when the label set it is given cannot be
satisfied in ANY model. -/

def existsMaxLt (k : Nat) (p : WfIri) (ls : List ClassExpr) : Bool :=
  ls.any (fun l => match l with
                   | .maxCard k' p' => p' == p && k' < k
                   | _              => false)

def existsMaxQualLt (k : Nat) (p : WfIri) (c : ClassExpr) (ls : List ClassExpr)
    : Bool :=
  ls.any (fun l => match l with
                   | .maxQualCard k' p' c' => p' == p && k' < k && ceEq c c'
                   | _                     => false)

/-- Successors PROVABLY in the filler: the successor's own node
    carries the filler as a label. Labels are entailed memberships, so
    this under-counts, which is the direction that keeps a `≤ k`
    clash sound. -/
def successorsInFiller (st : RState) (c : ClassExpr) (ts : List Term) : List Term :=
  ts.filter (fun t =>
    match termAsSubject t with
    | some j => memCe c (labelsOf st j)
    | none   => false)

/-- One label's clash against the whole label set of its node. -/
def clashForLabel (g : Graph) (st : RState) (i : Subject)
    (lsAll : List ClassExpr) (l : ClassExpr) : Bool :=
  match l with
  -- `owl:Nothing` is empty in every model.
  | .named x => x == owlNothing
  -- `¬C` beside `C`, or `¬⊤`.
  | .complement c =>
      memCe c lsAll || (match c with
                        | .named x => x == owlThing
                        | _        => false)
  -- An obligation to HAVE a successor on the bottom property cannot
  -- be met: `EXT(owl:bottomObjectProperty)` is empty in every model.
  | .minCard k p        => k ≥ 1 && (isBottomProp p || existsMaxLt k p lsAll)
  | .someOf p c         =>
      isBottomProp p || existsMaxLt 1 p lsAll || existsMaxQualLt 1 p c lsAll
  | .hasValue p _       => isBottomProp p || existsMaxLt 1 p lsAll
  | .minQualCard k p c  =>
      k ≥ 1 &&
      (isBottomProp p || existsMaxLt k p lsAll || existsMaxQualLt k p c lsAll ||
       -- A nominal `{a₁ … aₘ}` denotes at most `m` individuals in
       -- every model — that is the whole content of `owl:oneOf`. So
       -- `≥ k p.{a₁ … aₘ}` with `k > m` demands more pairwise-
       -- distinct fillers than the set can hold, with no
       -- `owl:differentFrom` needed.
       (match c with
        | .oneOf ms => k > ms.length
        | _         => false))
  -- `i : {a₁ … aₘ}` forces `i` to BE one of the members. If `i` is
  -- provably distinct from every member, no member can be `i`.
  | .oneOf ms =>
      ms.all (provablyDistinctGrouped g st i.toTerm ·)
  -- A union clashes when no disjunct is already present and every
  -- choice has an explicit complementary label. The empty union is
  -- the zero-choice instance.
  | .union cs =>
      !(cs.any (fun c => memCe c lsAll)) &&
      (liveUnionChoices cs lsAll).isEmpty
  | .maxCard k p =>
      let succs := successorsOf g st i p (!(k == 0))
      if k == 0 then !succs.isEmpty else existsDistinctSubset g succs (k + 1)
  | .maxQualCard k p c =>
      let succs := successorsInFiller st c (successorsOf g st i p (!(k == 0)))
      if k == 0 then !succs.isEmpty else existsDistinctSubset g succs (k + 1)
  | _ => false

/-- A zero maximum clashes on any required successor, including an
uncounted fresh expansion edge. No pairwise-distinctness premise is
needed when the permitted cardinality is zero. -/
theorem clashForLabel_maxCard_zero (g : Graph) (st : RState) (i : Subject)
    (ls : List ClassExpr) (p : WfIri) :
    clashForLabel g st i ls (.maxCard 0 p) =
      !(successorsOf g st i p false).isEmpty := by
  rfl

theorem clashForLabel_maxQualCard_zero (g : Graph) (st : RState) (i : Subject)
    (ls : List ClassExpr) (p : WfIri) (c : ClassExpr) :
    clashForLabel g st i ls (.maxQualCard 0 p c) =
      !(successorsInFiller st c (successorsOf g st i p false)).isEmpty := by
  rfl

/-! ## Datatype value spaces

Two rules over the concrete domain, both reading
`L4Factoidal/XSD/Facets.lean`.

**C6, the range clash.** Every `∀p.D` label on a node constrains ALL
its `p`-fillers, and several of them combine by INTERSECTION — "all
fillers in D₁" and "all fillers in D₂" together mean "all fillers in
D₁ ∩ D₂". A `hasValue p v` or a `∃p.D₀` label each separately FORCE
a filler to exist, and that filler must also lie in the intersected
`∀`-constraint. If it cannot, no filler can exist: clash.

Soundness-critical: two DIFFERENT existence obligations on one
property are NEVER combined WITH EACH OTHER — only each one against
the shared `∀`-intersection. Combining two `∃p.Dᵢ` would assume they
share one filler, which is false for a non-functional property.

**C5, the cardinality clash.** A `≥ k p` (k ≥ 1) demands `k` pairwise
distinct fillers. When `p`'s fillers are confined to a value space of
provable size `M < k`, that is impossible. `valueSetMaxSize` is an
OVER-approximation, so `k > M` implies `k` exceeds the true size and
never the reverse: an over-count only withholds a clash. A dense
range answers `none` and makes the rule inert there, which is right —
a min-cardinality on `xsd:decimal` is satisfiable.
-/

/-- Fold one class expression into the value space its fillers must
    lie in. Every shape the datatype layer does not recognise leaves
    the accumulator untouched, so this rule is inert on the ordinary
    class-expression corpus by construction. -/
partial def foldDatatypeConstraint (acc : ValueSet) : ClassExpr → ValueSet
  | .dataRestriction dt facets =>
      if isIntegerFamilyDatatype dt then
        valueSetIntersect acc (.interval (facetsToInterval dt facets fullInterval))
      else if isDateTimeDatatype dt then
        valueSetIntersect acc (.dateInterval (dateTimeFacetsToInterval facets fullInterval))
      -- A restriction over `xsd:float` is DISCRETE: an open interval
      -- whose endpoints are adjacent representable floats is EMPTY
      -- though the same real interval is not.
      else if isFloatDatatype dt then
        (if floatRestrictionProvablyEmpty dt facets then .empty else acc)
      -- A DENSE base folds to a rational-endpoint interval on the
      -- owl:real line, where adjacency never empties anything.
      else if isDenseNumericDatatype dt then
        valueSetIntersect acc (.dense (denseFacetsToQInterval facets fullQInterval))
      else acc
  | .oneOf members =>
      if !members.isEmpty && members.all (fun t => match t with
                                                   | .literal _ => true
                                                   | _          => false)
      then valueSetIntersect acc (.enum members) else acc
  | .named dt =>
      if isDateTimeDatatype dt then valueSetIntersect acc (.dateInterval fullInterval)
      else if isDenseNumericDatatype dt then
        valueSetIntersect acc (.dense fullQInterval)
      else
        (match classifyFamily dt with
         | some .numeric => valueSetIntersect acc (.interval (baseIntervalFor dt))
         -- WITHHELD deliberately for the two floating-point families.
         -- The RDFS closure derives `xsd:byte rdfs:subClassOf
         -- xsd:double`, and range propagation turns one asserted
         -- `p rdfs:range xsd:byte` into a DERIVED `p rdfs:range
         -- xsd:double`. Reading that derived range as a disjointness
         -- constraint would empty the value space of a CONSISTENT
         -- premise. The float/real disjointness is still used where
         -- it is read off an asserted literal's OWN datatype, never
         -- off a derived range triple.
         | some .float  => acc
         | some .double => acc
         | some f       => valueSetIntersect acc (.family f)
         | none         => acc)
  | .complement inner =>
      valueSetSubtract acc (foldDatatypeConstraint .unconstrained inner)
  | _ => acc

/-- The intersection of every `∀q.D` label whose `q` constrains `p`'s
    fillers — `p ⊑* q`, so every `p`-filler is a `q`-filler. -/
def universalForProperty (st : RState) (p : WfIri)
    (ls : List ClassExpr) (acc : ValueSet) : ValueSet :=
  let sups := supsOf st p
  ls.foldl (fun a l => match l with
    | .allOf q d => if sups.contains q then foldDatatypeConstraint a d else a
    | _          => a) acc

/-- `q rdfs:range d` constrains `p`'s fillers when `p ⊑* q`. -/
def rangeValueSet (st : RState) (ranges : List (WfIri × WfIri))
    (p : WfIri) (acc : ValueSet) : ValueSet :=
  let sups := supsOf st p
  ranges.foldl (fun a (q, d) =>
    if sups.contains q then foldDatatypeConstraint a (.named d) else a) acc

/-- Anonymous `rdfs:range` expressions constrain sub-properties in
    the same direction as named ranges. They are cached in `RState`
    so this per-node rule does no graph parsing. -/
def anonymousRangeValueSet (st : RState) (p : WfIri) (acc : ValueSet) : ValueSet :=
  let sups := supsOf st p
  st.anonymousRanges.foldl (fun a (q, d) =>
    if sups.contains q then foldDatatypeConstraint a d else a) acc

/-- Properties declared disjoint from `p`, including declarations on
    super-properties.  If `p ⊑* p'`, `q ⊑* q'`, and `p'` is disjoint
    from `q'`, then `EXT(p)` and `EXT(q)` are disjoint as well. -/
def disjointPropertiesFor (st : RState) (p : WfIri) : List WfIri :=
  let pSups := supsOf st p
  (st.store.withPred owlPropertyDisjointWith).flatMap (fun t =>
    match t.s, t.o with
    | .iri a, .iri b =>
        (if pSups.contains a then subsOf st b else []) ++
        (if pSups.contains b then subsOf st a else [])
    | _, _ => []) |>.eraseDups

/-- Values asserted for this node through a property whose extension
    is disjoint from `p`.  The graph is the closure passed to the
    refuter, so entailed sub-property assertions already present there
    are usable evidence.  Identified subjects are pooled in the same
    way as `labelsOf` and `successorsOf`. -/
def disjointPropertyExclusions (st : RState) (i : Subject) (p : WfIri) : List Term :=
  let subjects := (identifiedWith st i.toTerm).filterMap termAsSubject
  (disjointPropertiesFor st p).flatMap (fun q =>
    subjects.flatMap (fun s => (st.store.withSubjPred s q).map (·.o))) |>.eraseDups

def owlNegativePropertyAssertion : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#NegativePropertyAssertion", rfl⟩

/-- Literal targets of explicit negative data-property assertions on
    `i` which also forbid a `p` edge.  A negative assertion on `q`
    forbids `p` when `p ⊑* q`; the reverse implication is invalid.
    Only complete OWL 2 Mapping to RDF Graphs reifications are read. -/
def negativePropertyExclusions (st : RState) (i : Subject) (p : WfIri) : List Term :=
  let subjects := identifiedWith st i.toTerm
  let pSups := supsOf st p
  (st.store.withPredObj rdfType (Term.iri owlNegativePropertyAssertion)).filterMap
    (fun typeTriple =>
      match firstObject st.store typeTriple.s owlSourceIndividual,
            firstObject st.store typeTriple.s owlAssertionProperty,
            firstObject st.store typeTriple.s owlTargetValue with
      | some source, some (.iri q), some target =>
          if subjects.contains source && pSups.contains q then
            match target with
            | .literal _ => some target
            | _          => none
          else none
      | _, _, _ => none) |>.eraseDups

/-- Values which this node's `p`-filler cannot denote: explicit
    negative assertions and asserted values on disjoint properties.
    The two sources are independent and are combined only as a set of
    exclusions for one existence obligation. -/
def forbiddenDataValues (st : RState) (i : Subject) (p : WfIri) : List Term :=
  (negativePropertyExclusions st i p ++
   disjointPropertyExclusions st i p).eraseDups

def collectDtProperties (ls : List ClassExpr) : List WfIri :=
  ls.filterMap (fun l => match l with
    | .someOf p _   => some p
    | .allOf p _    => some p
    | .hasValue p _ => some p
    | .minCard k p   => if k ≥ 1 then some p else none
    | .exactCard k p => if k ≥ 1 then some p else none
    | _             => none)

/-- Is some existence obligation on `p` unsatisfiable against the
    shared `∀`-intersection? Each obligation is checked ALONE against
    that intersection, never against another obligation. -/
def existsUnsatisfiableWitness (p : WfIri) (ls : List ClassExpr)
    (universal : ValueSet) (excluded : List Term) : Bool :=
  ls.any (fun l => match l with
    | .someOf q d =>
        q == p && (valueSetIsEmptyAfterExcluding
                     (foldDatatypeConstraint universal d) excluded
                   || stringPatternExcluded d excluded)
    | .hasValue q v =>
        q == p && (match v with
                   | .literal _ => valueSetIsEmptyAfterExcluding
                                     (valueSetIntersect universal (.enum [v])) excluded
                   | _          => false)
    | .minCard k q | .exactCard k q =>
        q == p && k ≥ 1 && valueSetIsEmptyAfterExcluding universal excluded
    | _ => false)

/-- The value space every `p`-filler must lie in: the `∀`-intersection
    of the node's own labels, MET with the asserted `rdfs:range` of `p`
    and of every super-property of `p`.

    The range half was missing until 2026-09-04, and only from this
    rule: `datatypeCardinalityClash` below already read `st.ranges`.
    OWL 2 Syntax §9.2.5 `DataPropertyRange( DPE DR )` is satisfied only
    when every filler of `DPE` is in the data range, so the range
    constrains a filler exactly as a `∀` label does, and the two
    combine by intersection. `string-integer-clash` is the shape it
    could not see: `DataPropertyRange(:hasAge xsd:integer)` with an
    asserted `xsd:string` filler.

    A range triple can be DERIVED, never invented: the RL rows widen a
    range to a superclass (scm-rng1) or carry it down to a
    sub-property (scm-rng2), and both readings are sound here. The
    float and double families stay withheld inside
    `foldDatatypeConstraint` for the reason recorded there. -/
def fillerValueSet (st : RState) (p : WfIri) (ls : List ClassExpr) : ValueSet :=
  valueSetIntersect (universalForProperty st p ls .unconstrained)
    (anonymousRangeValueSet st p
      (rangeValueSet st st.ranges p .unconstrained))

def datatypeRangeClash (st : RState) (i : Subject) (ls : List ClassExpr) : Bool :=
  (collectDtProperties ls).any (fun p =>
    existsUnsatisfiableWitness p ls (fillerValueSet st p ls)
      (forbiddenDataValues st i p))

def collectCardProps (ls : List ClassExpr) : List (Nat × WfIri) :=
  ls.filterMap (fun l => match l with
    | .minCard k p   => some (k, p)
    | .exactCard k p => some (k, p)
    | _              => none)

def datatypeCardinalityClash (st : RState) (ls : List ClassExpr) : Bool :=
  (collectCardProps ls).any (fun (k, p) =>
    k ≥ 1 &&
    (match valueSetMaxSize (fillerValueSet st p ls) with
     | some m => k > m
     | none   => false))

/-! ## The counting clash: pairwise-disjoint existentials against `≤ k`

The ≤-rule below closes a `≤ k p` by MERGING successors and asking
every merge to clash. That search is a partition enumeration —
`WebOnt-description-logic-019` records 301 partitions for its
unsatisfiable case and `-022` records 42,525 for its satisfiable one —
so on the OilEd fixtures it does not finish inside any budget worth
giving it.

The rule here decides the same clash analytically, and it is the
standard ≥/≤ counting argument of the `SHIQ` calculus (Horrocks,
Sattler and Tobies, "Practical Reasoning for Very Expressive
Description Logics", LJ IGPL 8(3), 2000, §3, the `≥`/`≤` clash
condition; the same argument the `choose`-free counting optimisation
of FaCT and RACER uses).

    If `x` carries `∃p.C₁ … ∃p.Cₘ` with the `Cᵢ` PAIRWISE DISJOINT,
    then in every model `x` has `m` p-successors that are pairwise
    distinct, because a shared successor would lie in two disjoint
    classes. A `≤ k p` on `x` with `k < m` therefore has no model.

Under OWL 2 Direct Semantics §2.2 that reads
`ObjectSomeValuesFrom(p Cᵢ) ⊆ {x | ∃y. ⟨x,y⟩ ∈ p ∧ y ∈ Cᵢ}` and
`ObjectMaxCardinality(k p) ⊆ {x | #{y | ⟨x,y⟩ ∈ p} ≤ k}`, so the
argument is a counting one over `p`'s extension at `x` and needs no
choice of witnesses.

Both directions of approximation withhold the clash rather than
invent one: `ceDisjoint` proves disjointness structurally and answers
`false` where it cannot, and `disjointClique` takes a GREEDY
pairwise-disjoint subset, which is a lower bound on the largest one. -/

/-- `ls` with `news` appended, skipping what is already there. -/
def addCes (ls : List ClassExpr) (news : List ClassExpr) : List ClassExpr :=
  news.foldl (fun acc c => if memCe c acc then acc else acc ++ [c]) ls

/-- The labels a node must carry if it carries every member of `ls`:
    the conjuncts of each intersection, and the consequent of each
    TBox axiom whose antecedent is present, to a fixpoint under
    `fuel`. Running out of fuel DROPS labels, which can only lose a
    clash. -/
def ceLabelClosure (tb : List (ClassExpr × ClassExpr))
    : Nat → List ClassExpr → List ClassExpr
  | 0,     ls => ls
  | n + 1, ls =>
    let ls' := addCes ls
      ((ls.flatMap (fun l => match l with
                             | .intersection cs => cs
                             | _                => [])) ++
       tb.filterMap (fun q => if memCe q.1 ls then some q.2 else none))
    if ls'.length == ls.length then ls else ceLabelClosure tb n ls'

/-- A label set that no node can carry: a complement pair, or
    `owl:Nothing`. The structural core of `clashForLabel`, without the
    parts that read the graph. -/
def cesClash (ls : List ClassExpr) : Bool :=
  ls.any (fun l => match l with
                   | .complement c => memCe c ls
                   | .named x      => x == owlNothing
                   | _             => false)

/-- Are `a` and `b` disjoint — is `a ⊓ b` unsatisfiable? Proved by
    closing the pair's label set under the TBox and finding a
    structural clash in it. `false` where no proof is found. -/
def ceDisjoint (tb : List (ClassExpr × ClassExpr)) (a b : ClassExpr) : Bool :=
  ceDefinite a && ceDefinite b &&
  cesClash (ceLabelClosure tb 8 (addCes [a] [b]))

/-- The fillers of the existential obligations on `p`. A
    `minQualCard k p C` with `k ≥ 1` obliges one filler in `C` the
    same way `∃p.C` does; the extra `k - 1` are not used here. -/
def existentialFillersOn (p : WfIri) (ls : List ClassExpr) : List ClassExpr :=
  ls.filterMap (fun l => match l with
    | .someOf q c        => if q == p then some c else none
    | .minQualCard k q c => if q == p && k ≥ 1 then some c else none
    | _                  => none)

/-- A pairwise-disjoint subset of `cs`, taken greedily in list order.
    Any pairwise-disjoint subset is a valid lower bound on the number
    of successors the obligations force apart, so a greedy one is
    sound; a maximum one would only find more clashes. -/
def disjointClique (tb : List (ClassExpr × ClassExpr)) (cs : List ClassExpr)
    : List ClassExpr :=
  cs.foldl (fun acc c =>
    if acc.all (fun d => ceDisjoint tb c d) then acc ++ [c] else acc) []

/-- `≤ k p` (or `= k p`) against the existential obligations on `p`.
    The cheap length test runs first: with `m ≤ k` obligations no
    clique can exceed `k`, so no disjointness is computed at all. -/
def countingClash (st : RState) (ls : List ClassExpr) : Bool :=
  ls.any (fun l =>
    match l with
    | .maxCard k p | .exactCard k p =>
        let cs := existentialFillersOn p ls
        cs.length > k && (disjointClique st.tbox cs).length > k
    | _ => false)

/-- A branch may acquire an asserted `differentFrom` conflict only
    after several identifications. Checking complete groups prevents
    an indirect merge `a = b = c` from hiding `a differentFrom c`. -/
def identificationClash (g : Graph) (st : RState) : Bool :=
  st.ident.any (fun p => provablyDistinctGrouped g st p.1 p.2)

/-- A complete negative data-property assertion contradicts a positive
    assertion whose literal denotes the same data value. RDF term
    identity is sufficient but not required: numeric lexical aliases,
    and canonical XML literals are compared by
    `literalTermsProvablyEqualInStore`. -/
def negativeDataPropertyAssertionClash (st : RState) : Bool :=
  (st.store.withPredObj rdfType (Term.iri owlNegativePropertyAssertion)).any
    (fun typeTriple =>
      match firstObject st.store typeTriple.s owlSourceIndividual,
            firstObject st.store typeTriple.s owlAssertionProperty,
            firstObject st.store typeTriple.s owlTargetValue with
      | some source, some (.iri p), some target =>
          match termAsSubject source, target with
          | some s, .literal _ =>
              (st.store.withSubjPred s p).any (fun edge =>
                literalTermsProvablyEqualInStore st.store edge.o target)
          | _, _ => false
      | _, _, _ => false)

def clashNodes (g : Graph) (st : RState) : Bool :=
  identificationClash g st ||
  negativeDataPropertyAssertionClash st ||
  st.nodes.any (fun n =>
    let ls := labelsOf st n.id
    ls.any (clashForLabel g st n.id ls)
    || datatypeRangeClash st n.id ls
    || datatypeCardinalityClash st ls
    || countingClash st ls)

/-! ## Graph-level violations

Five shapes that make a graph unsatisfiable without any expansion at
all. Each is checked once, before the tableau starts. -/

def sameAsLinked (g : Graph) (a b : Term) : Bool :=
  g.any (fun t =>
    t.p == owlSameAs &&
    ((t.s.toTerm == a && t.o == b) || (t.s.toTerm == b && t.o == a)))

/-- G1: `owl:AllDifferent` members must be pairwise distinct, so a
    member listed twice, or two members linked by `owl:sameAs`, has no
    model. Positions `i < j` only — every term is `owl:sameAs` itself
    by reflexivity, and that must not fire. -/
partial def allDiffPairViolation (g : Graph) : List Term → Bool
  | []      => false
  | h :: tl => tl.any (fun o => h == o || sameAsLinked g h o)
               || allDiffPairViolation g tl

def allDifferentViolation (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == rdfType && t.o == Term.iri owlAllDifferent &&
    (((firstObject (Store.ofGraph g) t.s owlMembers).map
        (fun h => allDiffPairViolation g (walkRdfList (Store.ofGraph g) h 64))
        |>.getD false) ||
     ((firstObject (Store.ofGraph g) t.s owlDistinctMembers).map
        (fun h => allDiffPairViolation g (walkRdfList (Store.ofGraph g) h 64))
        |>.getD false)))

/-- G3: `p owl:propertyDisjointWith p` makes `EXT(p)` disjoint from
    itself, so empty. Any triple using `p` is then false in every
    model. The RL marker misses this because it wants two DIFFERENT
    predicates. -/
def selfDisjointPropertyInUse (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlPropertyDisjointWith && t.s.toTerm == t.o &&
    (match t.s with
     | .iri p   => g.any (fun u => u.p == p)
     | .bnode _ => false))

/-- G4: `rdf:nil` is the empty list and has no `rdf:first` or
    `rdf:rest` of its own, under both OWL 2 semantics. -/
def nilStructureViolation (g : Graph) : Bool :=
  g.any (fun t =>
    (t.p == rdfFirst || t.p == rdfRest) &&
    (match t.s with
     | .iri i   => i == rdfNil
     | .bnode _ => false))

/-- G5: a named class disjoint from `ObjectHasSelf(p)`, with an
    individual in that class carrying the reflexive edge `x p x`. The
    class-expression AST has no `hasSelf` constructor, so this narrow
    shape is checked at graph level. -/
def hasSelfRestriction (g : Graph) (r : Subject) : Option WfIri :=
  match firstObject (Store.ofGraph g) r owlOnProperty with
  | some (.iri p) =>
      (match firstObject (Store.ofGraph g) r owlHasSelf with
       | some (.literal l) =>
           if l.val.lexicalForm == "true" || l.val.lexicalForm == "1" then some p
           else none
       | _ => none)
  | _ => none

def hasSelfDisjointFor (g : Graph) (c : WfIri) (r : Subject) : Bool :=
  match hasSelfRestriction g r with
  | none   => false
  | some p =>
      g.any (fun t =>
        t.p == rdfType && t.o == Term.iri c &&
        g.any (fun u => u.p == p && u.s == t.s && u.o == t.s.toTerm))

def hasSelfDisjointViolation (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlDisjointWith &&
    (match t.s, t.o with
     | .iri c, .bnode b => hasSelfDisjointFor g c (.bnode b)
     | .bnode b, .iri c => hasSelfDisjointFor g c (.bnode b)
     | .iri c, .iri r   => hasSelfDisjointFor g c (.iri r)
     | _, _             => false))

/-- G2: `EXT(owl:bottomObjectProperty)` is empty in every model, so
    any triple asserted over it is false in every model. -/
def bottomPropertyAssertion (g : Graph) : Bool :=
  g.any (fun t => isBottomProp t.p)

/-- G6: `owl:Thing owl:equivalentClass owl:Nothing`, in either
    direction. OWL 2 Direct Semantics requires a NON-EMPTY domain and
    interprets `owl:Thing` as the whole of it, so equating it with the
    empty class has no model. -/
def thingIsNothing (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlEquivalentClass &&
    ((t.s == Subject.iri owlThing && t.o == Term.iri owlNothing) ||
     (t.s == Subject.iri owlNothing && t.o == Term.iri owlThing)))

/-- G7: two DIFFERENT properties declared `owl:propertyDisjointWith`
    with a shared subject-object pair. `EXT(p) ∩ EXT(q) = ∅`, and the
    pair is in both. -/
def disjointPropertiesShareAPair (g : Graph) : Bool :=
  g.any (fun t =>
    t.p == owlPropertyDisjointWith &&
    (match t.s, t.o with
     | .iri p, .iri q =>
         p != q &&
         g.any (fun u => u.p == p &&
           g.any (fun v => v.p == q && v.s == u.s && v.o == u.o))
     | _, _ => false))

/-- The members of every `owl:AllDisjointProperties` list. -/
def allDisjointPropertyGroups (g : Graph) : List (List WfIri) :=
  let st := Store.ofGraph g
  g.filterMap (fun t =>
    if t.p == rdfType && t.o == Term.iri owlAllDisjointProperties then
      match firstObject st t.s owlMembers with
      | some head => some ((walkRdfList st head 64).filterMap (fun x =>
          match x with
          | .iri i => some i
          | _      => none))
      | none      => none
    else none)

/-- G8: two members of one `owl:AllDisjointProperties` sharing a
    pair. The group asserts the extensions are PAIRWISE disjoint, so
    one shared pair has no model. -/
partial def groupPairViolation (g : Graph) : List WfIri → Bool
  | []      => false
  | p :: tl =>
      tl.any (fun q =>
        g.any (fun u => u.p == p &&
          g.any (fun v => v.p == q && v.s == u.s && v.o == u.o)))
      || groupPairViolation g tl

def allDisjointPropertiesViolation (g : Graph) : Bool :=
  (allDisjointPropertyGroups g).any (groupPairViolation g)

/-- G9: an `owl:AsymmetricProperty` with both `x p y` and `y p x`, or
    an `owl:IrreflexiveProperty` with `x p x`. Asymmetry says
    `(x,y) ∈ EXT(p)` implies `(y,x) ∉ EXT(p)`; irreflexivity says no
    pair `(x,x)` is in it. -/
def asymmetryViolation (g : Graph) : Bool :=
  (collectTypedIris g owlAsymmetricProperty).any (fun p =>
    g.any (fun u => u.p == p &&
      g.any (fun v => v.p == p && v.s.toTerm == u.o && v.o == u.s.toTerm)))

def irreflexivityViolation (g : Graph) : Bool :=
  (collectTypedIris g owlIrreflexiveProperty).any (fun p =>
    g.any (fun u => u.p == p && u.o == u.s.toTerm))

/-- G10: an `owl:hasKey` violation.

    OWL 2 Direct Semantics §2.3.5 gives
    `HasKey(CE (p1 … pm) (d1 … dn))` the condition: if `x` and `y` are
    both in `CE`, and for every key property `pi` there is a value `v`
    with `⟨x,v⟩` and `⟨y,v⟩` in `pi`, then `x = y`. Two individuals
    the graph forces apart therefore contradict the key.

    OWL 2 Syntax §9.5 restricts the condition to NAMED individuals —
    "the key is applied only to individuals that are explicitly named
    in the ontology" — which is why only IRI subjects are paired here.
    That restriction is also what makes a graph-level test the right
    shape: no witness needs to be built.

    `owl:Thing` as the class expression is every individual, so the
    membership test is skipped for it. For any other named class the
    membership must be IN THE GRAPH, which after the RL closure is
    where an entailed `rdf:type` is. A membership the closure did not
    derive withholds the violation. -/
def hasKeyViolation (g : Graph) : Bool :=
  let st := Store.ofGraph g
  g.any (fun t =>
    t.p == owlHasKey &&
    (match t.s with
     | .bnode _ => false
     | .iri c =>
       let keys := (walkRdfList st t.o 64).filterMap (fun u =>
         match u with
         | .iri k => some k
         | _      => none)
       if keys.isEmpty then false
       else
         -- Only individuals that carry EVERY key property can share a
         -- value on every one of them, so the pair loop runs over
         -- those alone.
         let named : List Term :=
           (g.filterMap (fun u =>
             match u.s with
             | .iri a => if keys.contains u.p then some (Term.iri a) else none
             | _      => none)).eraseDups
         let cands := named.filter (fun a =>
           (c == owlThing ||
            g.any (fun u => u.p == rdfType && u.o == Term.iri c &&
                            u.s.toTerm == a)) &&
           keys.all (fun k => g.any (fun u => u.p == k && u.s.toTerm == a)))
         cands.any (fun a => cands.any (fun b =>
           provablyDistinct g a b &&
           keys.all (fun k =>
             g.any (fun u => u.p == k && u.s.toTerm == a &&
               g.any (fun v => v.p == k && v.s.toTerm == b && v.o == u.o))))))) 

def immediateInconsistency (g : Graph) : Bool :=
  allDifferentViolation g || bottomPropertyAssertion g ||
  selfDisjointPropertyInUse g ||
  nilStructureViolation g || hasSelfDisjointViolation g ||
  thingIsNothing g || disjointPropertiesShareAPair g ||
  allDisjointPropertiesViolation g ||
  asymmetryViolation g || irreflexivityViolation g ||
  hasKeyViolation g

/-! ## The TBox

Axioms are `(lhs, rhs)` pairs of NNF class expressions. A node whose
label matches `lhs` structurally gains `rhs`. Each pair satisfies
`CEXT(lhs) ⊆ CEXT(rhs)` in every model of the graph:

* `A rdfs:subClassOf B` gives `A ⊑ B`;
* `A owl:equivalentClass B` gives `A ⊑ B` and `B ⊑ A`, and — since
  it is a genuine iff — both contrapositives `¬B ⊑ ¬A` and
  `¬A ⊑ ¬B`. The contrapositives are what let a definition fire
  through a negated name, which plain unfolding never does;
* `A owl:disjointWith B` gives `A ⊑ ¬B` and `B ⊑ ¬A`;
* `A owl:complementOf B` gives the same pair.

The contrapositive is NOT taken for `rdfs:subClassOf`: `¬B ⊑ ¬A`
does not follow from `A ⊑ B` as an unfolding rule the way it does
from an equivalence, because the tableau applies these left to right
on labels a node actually carries. -/

/-! ### Provably empty named classes become `owl:Nothing`

A named class whose superclass restrictions put BOTH a `≥ k p` and a
`≤ j p` on the same property with `j < k` has an empty extension in
every model: a member would need at least `k` and at most `j`
successors at once. Replacing such a class with `owl:Nothing` swaps
one class for another of IDENTICAL extension, so it is sound in
either polarity.

The payoff is syntactic. Axiom left-hand sides are matched
STRUCTURALLY, so a fixture that defines its own bottom class makes
`∀q.first:Nothing` and `∀q.owl:Nothing` — the same extension — two
expressions that never match each other. Normalising makes them one.

Detection is deliberately narrow: only the direct min/max pair, and
only for classes that appear as an `owl:allValuesFrom` filler, which
is where the normalisation pays. MISSING an empty class is sound
(nothing is normalised); claiming one falsely is not, and cannot
happen — the pair is entailed of the class, and `k > j` has no
model. -/

def superclassCes (st : Store) (c : WfIri) : List ClassExpr :=
  st.graph.filterMap (fun t =>
    if (t.p == rdfsSubClassOf || t.p == owlEquivalentClass) && t.s == Subject.iri c
    then some (parseClassExpr st t.o 8) else none)

def cesMinMaxClash (ces : List ClassExpr) : Bool :=
  ces.any (fun ce => match ce with
    | .minCard k p =>
        k ≥ 1 && ces.any (fun d => match d with
                                   | .maxCard j q => q == p && j < k
                                   | _            => false)
    | _ => false)

/-- Store-parameterised: the graph it reads is `st.graph`. -/
def unsatNamedClassesS (st : Store) : List WfIri :=
  let fillers := (st.graph.filterMap (fun t =>
    if t.p == owlAllValuesFrom then
      match t.o with
      | .iri c => some c
      | _      => none
    else none)).eraseDups
  fillers.filter (fun c => cesMinMaxClash (superclassCes st c))

def unsatNamedClasses (g : Graph) : List WfIri :=
  unsatNamedClassesS (Store.ofGraph g)

/-- Indexed implementation of `unsatNamedClasses`. The public list
    definition remains the proof-facing specification. -/
def unsatNamedClassesIndexed (g : Graph) : List WfIri :=
  unsatNamedClassesS (Store.ofIndex (Index.ofGraph g))

theorem unsatNamedClassesIndexed_eq (g : Graph) :
    unsatNamedClassesIndexed g = unsatNamedClasses g := by
  rw [unsatNamedClassesIndexed, unsatNamedClasses,
      Store.ofIndex_eq (Index.Wf.ofGraph g)]

@[csimp] theorem unsatNamedClasses_eq_indexed :
    @unsatNamedClasses = @unsatNamedClassesIndexed := by
  funext g
  exact (unsatNamedClassesIndexed_eq g).symm

mutual

partial def normalizeUnsat (us : List WfIri) : ClassExpr → ClassExpr
  | .named c            => if us.contains c then .named owlNothing else .named c
  | .someOf p c         => .someOf p (normalizeUnsat us c)
  | .allOf p c          => .allOf p (normalizeUnsat us c)
  | .complement c       => .complement (normalizeUnsat us c)
  | .intersection cs    => .intersection (normalizeUnsatList us cs)
  | .union cs           => .union (normalizeUnsatList us cs)
  | .minQualCard k p c  => .minQualCard k p (normalizeUnsat us c)
  | .maxQualCard k p c  => .maxQualCard k p (normalizeUnsat us c)
  | .exactQualCard k p c => .exactQualCard k p (normalizeUnsat us c)
  | ce                  => ce

partial def normalizeUnsatList (us : List WfIri) : List ClassExpr → List ClassExpr
  | []      => []
  | c :: tl => normalizeUnsat us c :: normalizeUnsatList us tl

end

/-- A blank node the OWL RL closure minted as SCAFFOLDING.

    `RLRules.lean` materialises canonical restriction-membership
    blank nodes (`__rl_comp__…`, `__rl_minc1__…`) as SUPPORT triples
    for the corpus's blank-node conclusion matching. Their encoding
    is deliberately loose — membership is asserted on a weaker
    condition than the class expression they resemble would require —
    so reading one literally as a class expression MANUFACTURES
    refutations of consistent premises. Every class expression this
    module parses maps them to `unknown`, which is inert in labels,
    axioms and branching. Dropping a constraint is always sound. -/
def isScaffoldBNode : Term → Bool
  | .bnode b => b.startsWith "__rl_"
  | _        => false

/-- Normalise BETWEEN parse and NNF, so the NNF negation of a
    normalised bottom simplifies (`nnfNeg owl:Nothing = owl:Thing`)
    and the two spellings of a complement pair converge. Normalising
    AFTER the NNF would leave `∃q.¬first:Nothing` beside
    `∃q.owl:Thing` — one extension, two expressions, no match. -/
def parseNnfWith (us : List WfIri) (st : Store) (t : Term) : ClassExpr :=
  if isScaffoldBNode t then .unknown
  else nnf (normalizeUnsat us (parseClassExpr st t 32))

/-- Parsing through the index has exactly the list-store result. This
    theorem licenses reusing `initState`'s one index for its anonymous
    ranges and initial type labels. -/
theorem parseNnfWith_indexed_eq (us : List WfIri) (g : Graph) (t : Term) :
    parseNnfWith us (Store.ofIndex (Index.ofGraph g)) t =
      parseNnfWith us (Store.ofGraph g) t := by
  rw [Store.ofIndex_eq (Index.Wf.ofGraph g)]

def parseNnfSubjectWith (us : List WfIri) (st : Store) (sub : Subject) : ClassExpr :=
  if isScaffoldBNode sub.toTerm then .unknown
  else nnf (normalizeUnsat us (parseCeOfSubject st sub))

def parseNnf (st : Store) (t : Term) : ClassExpr := nnf (parseClassExpr st t 32)

def parseNnfSubject (st : Store) (s : Subject) : ClassExpr :=
  nnf (parseCeOfSubject st s)

private def markerClassList (us : List WfIri) (st : Store) (head : Term)
    : Option (List ClassExpr) :=
  (walkRdfListComplete st head).map
    (fun members => members.map (parseNnfWith us st))

/-- Four directed unfolding rules for a genuine class equivalence,
    including both NNF contrapositives. -/
private def equivalenceAxioms (a b : ClassExpr) : List (ClassExpr × ClassExpr) :=
  [(a, b), (b, a), (nnfNeg b, nnfNeg a), (nnfNeg a, nnfNeg b)]

/-- Pairwise disjointness axioms for the operands of a disjoint union. -/
private def pairwiseDisjointAxioms : List ClassExpr → List (ClassExpr × ClassExpr)
  | cs =>
    ((List.range cs.length).foldl (fun acc i =>
      match cs[i]? with
      | none => acc
      | some c => (cs.drop (i + 1)).foldl (fun out d =>
          (d, nnfNeg c) :: (c, nnfNeg d) :: out) acc) []).reverse

/-- A NAMED class that carries the restriction markers itself.

    The OWL 2 RDF mapping (Table 13 of https://www.w3.org/TR/owl2-mapping-to-rdf/)
    reads `z owl:onProperty p . z owl:maxQualifiedCardinality 1 .
    z owl:onClass c` as the class expression, whatever `z` is; when
    `z` is an IRI the triples say that the class `z` IS that
    restriction, so `CEXT(z)` and the restriction's extension are the
    same set and the inclusion holds in both directions.

    `collectAxiomsS` reads axioms off `rdfs:subClassOf`,
    `owl:equivalentClass`, `owl:disjointWith` and `owl:complementOf`
    triples only, so a restriction written directly on a named class,
    with no axiom triple beside it, produced no TBox entry at all: the
    node typed `z` got the label `.named z` from `initState`, the
    bound never became a label, and no cardinality rule could fire.
    That is the shape of `rdfbased-sem-restrict-maxqcr-inst-obj-one`.

    Only `owl:onProperty` subjects are read here. Named collection
    markers are handled separately so every marker triple supplies its
    own complete list instead of inheriting the first marker found on
    the subject. -/
def namedRestrictionAxioms (us : List WfIri) (st : Store)
    : List (ClassExpr × ClassExpr) :=
  let subs := (st.graph.filterMap (fun t =>
    if t.p == owlOnProperty then
      match t.s with
      | .iri c   => some c
      | .bnode _ => none
    else none)).eraseDups
  subs.flatMap (fun c =>
    match parseNnfSubjectWith us st (.iri c) with
    | .unknown => []
    | .named d => if d == c then [] else [(.named c, .named d), (.named d, .named c)]
    | ce       => [(.named c, ce), (ce, .named c)])

/-- Definitions written directly on a named class.

    Each marker triple is read independently. This matters when one
    class has several `owl:oneOf` declarations: every declaration is
    an equality of class extensions and all must constrain the model.
    Nominal complements stay atomic in this AST, so the oneOf pair has
    no executable contrapositive. Boolean definitions do have NNF
    contrapositives. `disjointUnionOf` adds the union equivalence and
    the pairwise disjointness required by its direct semantics. -/
def namedClassExpressionAxioms (us : List WfIri) (st : Store)
    : List (ClassExpr × ClassExpr) :=
  st.graph.flatMap (fun t =>
    match t.s with
    | .bnode _ => []
    | .iri z =>
      if t.p == owlOneOf then
        match walkRdfListComplete st t.o with
        | some members => [(.named z, .oneOf members), (.oneOf members, .named z)]
        | none         => []
      else if t.p == owlComplementOf then
        match parseNnfWith us st t.o with
        | .unknown => []
        | c        => equivalenceAxioms (.named z) (nnfNeg c)
      else if t.p == owlIntersectionOf || t.p == owlUnionOf ||
              t.p == owlDisjointUnionOf then
        match markerClassList us st t.o with
        | none => []
        | some cs =>
          let body := if t.p == owlIntersectionOf then .intersection cs else .union cs
          let eqs := equivalenceAxioms (.named z) body
          if t.p == owlDisjointUnionOf then eqs ++ pairwiseDisjointAxioms cs else eqs
      else [])

/-- Store-parameterised: the graph it reads is `st.graph`.

    Every lookup below runs through `st`, so the store decides the
    COST and not the answer. Over `Store.ofGraph g` each lookup is a
    filter of the whole list; over `Store.ofIndex (Index.ofGraph g)`
    each is a hash lookup. `collectAxioms_eq` is the record that the
    two agree. -/
def collectAxiomsS (st : Store) : List (ClassExpr × ClassExpr) :=
  let us := unsatNamedClassesS st
  namedRestrictionAxioms us st ++
  namedClassExpressionAxioms us st ++
  st.graph.flatMap (fun t =>
    if t.p == rdfsSubClassOf then
      [(parseNnfSubjectWith us st t.s, parseNnfWith us st t.o)]
    else if t.p == owlEquivalentClass then
      let a := parseNnfSubjectWith us st t.s
      let b := parseNnfWith us st t.o
      [(a, b), (b, a), (nnfNeg b, nnfNeg a), (nnfNeg a, nnfNeg b)]
    else if t.p == owlDisjointWith || t.p == owlComplementOf then
      let a := parseNnfSubjectWith us st t.s
      let b := parseNnfWith us st t.o
      [(a, nnfNeg b), (b, nnfNeg a)]
    else [])

/-- Structural equality of TBox axiom pairs. `ClassExpr.beq` and not
    `ceEq`: `ceEq a b` is `ceDefinite a && ClassExpr.beq a b`, which is
    not reflexive on an indefinite expression, and an axiom must count
    as a duplicate of ITSELF. -/
def axiomBeq (x y : ClassExpr × ClassExpr) : Bool :=
  ClassExpr.beq x.1 y.1 && ClassExpr.beq x.2 y.2

/-- The structurally distinct axioms, FIRST occurrence kept, so the
    order of the distinct axioms is the order `collectAxiomsS` emitted
    them.

    **Why a repeated axiom changes nothing.** `applyAxioms` and
    `injectGlobalAxioms` fold over the TBox calling `addLabel`, and
    `addLabel` returns the state unchanged when the label is already
    present, so the second copy of an axiom adds nothing and reports no
    change. `applyAxiomsEdges` and `applyAxiomsConj` guard on
    `memCe a ls` before firing, so the second copy is skipped there
    too. Nothing else reads the TBox: `pendingUnion`, `pendingMerge`
    and `clashNodes` read labels and nodes.

    **Why the failure direction is safe.** If that argument were wrong,
    dropping a copy could only give a node FEWER labels, hence fewer
    clashes, hence a WITHHELD refutation — never a manufactured one.
    A wrong deduplication loses conformance units, which the corpus
    score sees; it cannot invent an entailment. -/
def dedupAxioms (tb : List (ClassExpr × ClassExpr)) : List (ClassExpr × ClassExpr) :=
  (tb.foldl (fun acc a => if acc.any (axiomBeq a) then acc else a :: acc) []).reverse

/-- The TBox of a graph, read through the HASH INDEX.

    `collectAxiomsS` parses a class expression for BOTH sides of every
    `rdfs:subClassOf`, `owl:equivalentClass`, `owl:disjointWith` and
    `owl:complementOf` triple, and each parse makes several
    subject-plus-predicate lookups. Over the list store that is a scan
    of the whole graph per lookup, so the pass is quadratic in the
    graph and the tableau refuter pays it once per goal. Over the index
    each lookup is O(1). -/
def collectAxiomsRaw (g : Graph) : List (ClassExpr × ClassExpr) :=
  collectAxiomsS (Store.ofIndex (Index.ofGraph g))

/-- The index store and the list store give `collectAxiomsS` the same
    value, so `collectAxiomsRaw` is the list-scan definition it
    replaced. -/
theorem collectAxiomsRaw_eq (g : Graph) :
    collectAxiomsRaw g = collectAxiomsS (Store.ofGraph g) := by
  rw [collectAxiomsRaw, Store.ofIndex_eq (Index.Wf.ofGraph g)]

/-- The TBox the tableau runs against: one entry per STRUCTURALLY
    DISTINCT axiom.

    `collectAxiomsS` emits one axiom per triple, so two restriction
    nodes with the same `owl:onProperty` and the same filler produce
    the SAME class-expression pair. Measured over the whole OWL corpus
    with `l4owl-probe --tbox-census`, 214,466 axioms reduce to 73,653
    distinct ones, and on the heaviest case 18,099 reduce to 2,964.
    `onePass` folds over the WHOLE TBox once per node and once per
    label, and `search` runs it up to its budget per goal, so a
    duplicate is paid thousands of times. -/
def collectAxioms (g : Graph) : List (ClassExpr × ClassExpr) :=
  dedupAxioms (collectAxiomsRaw g)

/-! ## Expansion -/

def witnessId (i : Subject) (p : WfIri) (n : Nat) : BNodeId :=
  let iStr := match i with
    | .iri s   => s.val
    | .bnode b => b
  "_:tw_" ++ iStr ++ "__" ++ p.val ++ "__" ++ toString n

/-- Specification scan for whether an input graph already uses a
    blank-node identifier as a direct subject or object. OWL 2 input
    excludes RDF 1.2 triple terms, so nested triple-term positions are
    outside this refuter's input contract. -/
def inputWitnessIdUsedSpec (g : Graph) (b : BNodeId) : Bool :=
  g.any (fun t => t.s == Subject.bnode b || t.o == Term.bnode b)

/-- Indexed input lookup for witness-name freshness. -/
def inputWitnessIdUsed (st : Store) (b : BNodeId) : Bool :=
  !(st.withSubj (.bnode b)).isEmpty || !(st.withObj (.bnode b)).isEmpty

/-- The indexed lookup has exactly the list-scan answer on the store
    constructed by the refuter. -/
theorem inputWitnessIdUsed_indexed_eq_spec (g : Graph) (b : BNodeId) :
    inputWitnessIdUsed (Store.ofIndex (Index.ofGraph g)) b =
      inputWitnessIdUsedSpec g b := by
  rw [Store.ofIndex_eq (Index.Wf.ofGraph g), Bool.eq_iff_iff]
  simp [inputWitnessIdUsed, inputWitnessIdUsedSpec, Store.ofGraph,
        RL.withSubj, RL.withObj, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro (⟨x, hx, hs⟩ | ⟨x, hx, ho⟩)
    · exact ⟨x, hx, Or.inl hs⟩
    · exact ⟨x, hx, Or.inr ho⟩
  · rintro ⟨x, hx, hs | ho⟩
    · exact Or.inl ⟨x, hx, hs⟩
    · exact Or.inr ⟨x, hx, ho⟩


/-- Every place where a blank-node identifier already has meaning in
    the input or current branch. A generated witness must avoid all of
    them: colliding with an unrelated input node would pool labels that
    no model equates. -/
def witnessIdUsed (st : RState) (b : BNodeId) : Bool :=
  inputWitnessIdUsed st.store b ||
  st.nodes.any (fun n => n.id == Subject.bnode b) ||
  st.extra.any (fun e => e.s == Subject.bnode b || e.o == Term.bnode b) ||
  st.wdepth.any (fun p => p.1 == b) ||
  st.ident.any (fun p => p.1 == Term.bnode b || p.2 == Term.bnode b)

/-- More than the number of occupied blank-node occurrences. Among
    this many consecutive generated names, at least one is unused.
    This bound is computed only after the first candidate collides. -/
private def witnessFreshFuel (st : RState) : Nat :=
  2 * st.store.graph.length + st.nodes.length + 2 * st.extra.length +
  st.wdepth.length + 2 * st.ident.length + 1

private def freshWitnessIdAux (st : RState) (i : Subject) (p : WfIri) :
    Nat → Nat → Option BNodeId
  | _, 0 => none
  | n, fuel + 1 =>
      let b := witnessId i p n
      if witnessIdUsed st b then freshWitnessIdAux st i p (n + 1) fuel else some b

/-- The first unused generated name at or after `start`. In the usual
    collision-free case this is exactly `witnessId i p start`, so the
    established deterministic order is unchanged. -/
def freshWitnessId (st : RState) (i : Subject) (p : WfIri) (start : Nat)
    : Option BNodeId :=
  let first := witnessId i p start
  if witnessIdUsed st first then
    freshWitnessIdAux st i p (start + 1) (witnessFreshFuel st)
  else some first

def depthOf (st : RState) (i : Subject) : Nat :=
  match i with
  | .iri _   => 0
  | .bnode b => (st.wdepth.find? (fun q => q.1 == b)).map (·.2) |>.getD 0

/-- Mint witnesses for `i` on `p` until it has `k` successors, up to
    the depth and per-pass count bounds. The filler is put on each
    witness. `pendingWitnessObligation` later detects a bound that left
    the lower-bound label unsatisfied. -/
def ensureWitnesses (g : Graph) (st : RState) (i : Subject) (p : WfIri)
    (k : Nat) (c : ClassExpr) : RState × Bool :=
  -- `∃p.C` is DISCHARGED by a successor that carries `C`, not by any
  -- successor at all. Counting successors alone was the defect that
  -- made the ≤-rule fire and find nothing: the materialisation pass
  -- writes its own `p`-successors into the graph, and an existential
  -- whose filler is anonymous (`∃f2.¬p1`) gets an edge from it but no
  -- type — so the count said "discharged", no witness was minted, and
  -- the filler was never put on any node. Every merge branch then
  -- pooled labels that did not include it and stayed open
  -- (WebOnt-description-logic-003 and its family).
  let succs := successorsOf g st i p false
  let have' := match c with
    | .unknown => succs.length
    | _        => (successorsInFiller st c succs).length
  if have' ≥ k then (st, false)
  else if depthOf st i ≥ maxWitnessDepth then (st, false)
  else
    let want := min (k - have') maxGeneratedWitnesses
    let d := depthOf st i + 1
    (List.range want).foldl (fun (acc : RState × Bool) j =>
      let (s0, ch) := acc
      match freshWitnessId s0 i p (s0.fresh + j) with
      | none => (s0, ch)
      | some b =>
        let s1 := { s0 with
          extra := s0.extra ++ [{ s := i, p := p, o := .bnode b, counts := false }],
          wdepth := s0.wdepth ++ [(b, d)] }
        let (s2, _) := addLabel s1 (.bnode b) c
        (s2, true)) (st, false)
    |> (fun (s, ch) => ({ s with fresh := s.fresh + want }, ch))

/-- Add an edge whose exact object is entailed in every model. It is
    countable for cardinality rules, like an `owl:hasValue` edge. -/
def ensureCountableEdge (st : RState) (i : Subject) (p : WfIri) (v : Term)
    : RState × Bool :=
  if st.extra.any (fun e => e.s == i && e.p == p && e.o == v) then (st, false)
  else ({ st with extra := st.extra ++ [{ s := i, p := p, o := v, counts := true }] },
        true)

/-- The deterministic rules of one label. A union with exactly one
    live disjunct is unit-propagated; genuine alternatives remain for
    the search branch. -/
def applyLabelRules (g : Graph) (st : RState) (i : Subject) (l : ClassExpr)
    : RState × Bool :=
  match l with
  | .intersection cs =>
      cs.foldl (fun (acc : RState × Bool) c =>
        let (s, ch) := addLabel acc.1 i c
        (s, acc.2 || ch)) (st, false)
  | .union cs =>
      let ls := labelsOf st i
      if cs.any (fun c => memCe c ls) then (st, false)
      else
        match liveUnionChoices cs ls with
        | [c] => addLabel st i c
        | _   => (st, false)
  | .allOf p c =>
      -- Push the filler across every `p`-successor, WITNESSES
      -- INCLUDED: `∀` constrains successors however they arose.
      let succs := successorsOf g st i p false
      let base := succs.foldl (fun (acc : RState × Bool) y =>
        match termAsSubject y with
        | none   => acc
        | some j => let (s, ch) := addLabel acc.1 j c
                    (s, acc.2 || ch)) (st, false)
      -- The SHIQ ∀⁺ rule: across a TRANSITIVE role `r ⊑* p`, the
      -- whole `∀r.c` label is re-pushed, not only `c` — otherwise a
      -- successor two `r`-steps away escapes the restriction the
      -- transitivity puts it under.
      let transRoles := (subsOf st p).filter (roleIsTransitive st)
      let pushed := transRoles.foldl (fun (acc : RState × Bool) r =>
        (successorsOf g acc.1 i r false).foldl (fun (a2 : RState × Bool) y =>
          match termAsSubject y with
          | none   => a2
          | some j => let (s, ch) := addLabel a2.1 j (.allOf r c)
                      (s, a2.2 || ch)) acc) base
      -- `EXT(owl:topObjectProperty) = Δ × Δ`: every individual is its
      -- own top-successor, so `∀top.C` puts `C` on the node itself.
      if p == owlTopObjectProperty then
        let (s, ch) := addLabel pushed.1 i c
        (s, pushed.2 || ch)
      else pushed
  -- A witness on the bottom property is never minted: the clash rule
  -- fires on the label instead, and a minted successor over an empty
  -- property would be a fabricated edge.
  | .someOf p (.oneOf [a]) =>
      if isBottomProp p then (st, false) else ensureCountableEdge st i p a
  | .someOf p c        => if isBottomProp p then (st, false)
                          else ensureWitnesses g st i p 1 c
  | .minQualCard k p c => if isBottomProp p then (st, false)
                          else ensureWitnesses g st i p k c
  | .minCard k p       => if isBottomProp p then (st, false)
                          else ensureWitnesses g st i p k .unknown
  | .hasValue p v =>
      -- A `hasValue` edge holds in EVERY model, so it is COUNTED
      -- against cardinality bounds, unlike a witness.
      ensureCountableEdge st i p v
  | _ => (st, false)

/-- A label matching an axiom's left-hand side gains its right-hand
    side. The match is structural: two expressions that denote the
    same class but are written differently do not fire each other,
    which withholds inferences rather than inventing them. -/
def applyAxioms (tb : List (ClassExpr × ClassExpr)) (st : RState) (i : Subject)
    (l : ClassExpr) : RState × Bool :=
  tb.foldl (fun (acc : RState × Bool) (a, d) =>
    if ceEq a l then
      let (s, ch) := addLabel acc.1 i d
      (s, acc.2 || ch)
    else acc) (st, false)

/-- Removing inputs whose step is the identity preserves a left fold,
    including its result order. This is the common proof used by the
    TBox dispatch filters below. -/
theorem foldl_filter_of_rejected_identity {α β : Type} (keep : β → Bool)
    (step : α → β → α)
    (hstep : ∀ acc x, keep x = false → step acc x = acc)
    (xs : List β) (init : α) :
    (xs.filter keep).foldl step init = xs.foldl step init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      cases hx : keep x with
      | false =>
          simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte,
            List.foldl_cons]
          rw [hstep init x hx]
          exact ih init
      | true =>
          simp only [List.filter_cons, hx, ↓reduceIte,
            List.foldl_cons]
          exact ih (step init x)

/-! ### Named-antecedent dispatch

Most real TBox applications match a named label against a named
antecedent. The index stores exactly those axioms, in their original
order. Every other label keeps the complete ordered TBox fallback. -/

abbrev NamedAxiomIndex :=
  Std.HashMap WfIri (List (ClassExpr × ClassExpr))

def namedAxiomFor (q : WfIri) (ax : ClassExpr × ClassExpr) : Bool :=
  match ax.1 with
  | .named p => p == q
  | _        => false

def NamedAxiomIndex.add (index : NamedAxiomIndex)
    (ax : ClassExpr × ClassExpr) : NamedAxiomIndex :=
  match ax.1 with
  | .named p => index.insert p (index.getD p [] ++ [ax])
  | _        => index

def buildNamedAxiomIndex (tb : List (ClassExpr × ClassExpr)) : NamedAxiomIndex :=
  tb.foldl NamedAxiomIndex.add ∅

theorem NamedAxiomIndex.add_getD (index : NamedAxiomIndex)
    (ax : ClassExpr × ClassExpr) (q : WfIri) :
    (index.add ax).getD q [] =
      index.getD q [] ++ if namedAxiomFor q ax then [ax] else [] := by
  rcases ax with ⟨a, d⟩
  cases a with
  | named p =>
      by_cases hp : p.val = q.val
      · have hpq : p = q := Subtype.ext hp
        subst p
        simp [NamedAxiomIndex.add, namedAxiomFor,
          Std.HashMap.getD_eq_getD_getElem?]
      · simp [NamedAxiomIndex.add, namedAxiomFor,
          Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert,
          hp]
  | someOf p c => simp [NamedAxiomIndex.add, namedAxiomFor]
  | allOf p c => simp [NamedAxiomIndex.add, namedAxiomFor]
  | hasValue p v => simp [NamedAxiomIndex.add, namedAxiomFor]
  | intersection cs => simp [NamedAxiomIndex.add, namedAxiomFor]
  | union cs => simp [NamedAxiomIndex.add, namedAxiomFor]
  | complement c => simp [NamedAxiomIndex.add, namedAxiomFor]
  | minCard n p => simp [NamedAxiomIndex.add, namedAxiomFor]
  | maxCard n p => simp [NamedAxiomIndex.add, namedAxiomFor]
  | exactCard n p => simp [NamedAxiomIndex.add, namedAxiomFor]
  | minQualCard n p c => simp [NamedAxiomIndex.add, namedAxiomFor]
  | maxQualCard n p c => simp [NamedAxiomIndex.add, namedAxiomFor]
  | exactQualCard n p c => simp [NamedAxiomIndex.add, namedAxiomFor]
  | oneOf vs => simp [NamedAxiomIndex.add, namedAxiomFor]
  | dataRestriction dt facets => simp [NamedAxiomIndex.add, namedAxiomFor]
  | unknown => simp [NamedAxiomIndex.add, namedAxiomFor]

theorem fold_namedAxiomIndex_getD (tb : List (ClassExpr × ClassExpr))
    (index : NamedAxiomIndex) (q : WfIri) :
    (tb.foldl NamedAxiomIndex.add index).getD q [] =
      index.getD q [] ++ tb.filter (namedAxiomFor q) := by
  induction tb generalizing index with
  | nil => simp
  | cons ax tb ih =>
      simp only [List.foldl_cons]
      rw [ih, NamedAxiomIndex.add_getD]
      cases h : namedAxiomFor q ax <;>
        simp [h, List.append_assoc]

theorem buildNamedAxiomIndex_getD (tb : List (ClassExpr × ClassExpr))
    (q : WfIri) :
    (buildNamedAxiomIndex tb).getD q [] = tb.filter (namedAxiomFor q) := by
  simpa [buildNamedAxiomIndex] using fold_namedAxiomIndex_getD tb ∅ q

theorem namedAxiomFor_rejected (q : WfIri)
    (ax : ClassExpr × ClassExpr) (h : namedAxiomFor q ax = false) :
    ceEq ax.1 (.named q) = false := by
  rcases ax with ⟨a, d⟩
  cases a <;> simp_all [namedAxiomFor, ceEq, ClassExpr.beq]

theorem applyAxioms_named_filter_eq (tb : List (ClassExpr × ClassExpr))
    (st : RState) (i : Subject) (q : WfIri) :
    applyAxioms (tb.filter (namedAxiomFor q)) st i (.named q) =
      applyAxioms tb st i (.named q) := by
  simp only [applyAxioms]
  rw [foldl_filter_of_rejected_identity]
  intro acc ax h
  have heq := namedAxiomFor_rejected q ax h
  rcases ax with ⟨a, d⟩
  simp [heq]

def applyAxiomsDispatched (index : NamedAxiomIndex)
    (tb : List (ClassExpr × ClassExpr)) (st : RState) (i : Subject)
    (l : ClassExpr) : RState × Bool :=
  match l with
  | .named q => applyAxioms (index.getD q []) st i l
  | _        => applyAxioms tb st i l

theorem applyAxiomsDispatched_eq (tb : List (ClassExpr × ClassExpr))
    (st : RState) (i : Subject) (l : ClassExpr) :
    applyAxiomsDispatched (buildNamedAxiomIndex tb) tb st i l =
      applyAxioms tb st i l := by
  cases l with
  | named q =>
      simp only [applyAxiomsDispatched]
      rw [buildNamedAxiomIndex_getD]
      exact applyAxioms_named_filter_eq tb st i q
  | someOf p c => rfl
  | allOf p c => rfl
  | hasValue p v => rfl
  | intersection cs => rfl
  | union cs => rfl
  | complement c => rfl
  | minCard n p => rfl
  | maxCard n p => rfl
  | exactCard n p => rfl
  | minQualCard n p c => rfl
  | maxQualCard n p c => rfl
  | exactQualCard n p c => rfl
  | oneOf vs => rfl
  | dataRestriction dt facets => rfl
  | unknown => rfl

/-! ### Membership proved by asserted EDGES

An axiom fires when a node's LABEL matches its left-hand side. But a
node's asserted successors can PROVE it belongs to that left-hand
side even when no `rdf:type` triple says so, and without this rule
the axiom never fires on it.

Sound per shape, over COUNTED successors only:

* `≥ 1 p` — any asserted successor is a witness;
* `≥ k p` (k ≥ 2) — `k` PAIRWISE PROVABLY DISTINCT successors. A
  plain count of `k` would be unsound: two IRIs may denote one
  individual;
* `∃p.C` — a successor whose node carries `C`, which is an entailed
  membership;
* `hasValue p v` — the edge itself;
* `≥ k p.C` — as `≥ k p` over the `C`-labelled successors.

Everything else is `false`. Withholding is sound. -/
def edgeEntailsMembership (g : Graph) (st : RState) (i : Subject) (a : ClassExpr)
    : Bool :=
  match a with
  | .minCard k p =>
      if k == 0 then false
      else if k == 1 then !(successorsOf g st i p true).isEmpty
      else existsDistinctSubset g (successorsOf g st i p true) k
  | .someOf p c =>
      ceDefinite c &&
      (successorsOf g st i p true).any (fun o =>
        match termAsSubject o with
        | some j => memCe c (labelsOf st j)
        | none   => false)
  | .hasValue p v => (successorsOf g st i p true).any (· == v)
  | .minQualCard k p c =>
      if k == 0 || !(ceDefinite c) then false
      else
        let cs := successorsInFiller st c (successorsOf g st i p true)
        if k == 1 then !cs.isEmpty else existsDistinctSubset g cs k
  | _ => false

/-- Antecedent shapes for which `edgeEntailsMembership` can return
    true. This is a dispatch predicate only; it does not change any
    semantic side condition within those cases. -/
def edgeAntecedentRelevant : ClassExpr → Bool
  | .minCard _ _       => true
  | .someOf _ _        => true
  | .hasValue _ _      => true
  | .minQualCard _ _ _ => true
  | _                  => false

def edgeAxiomRelevant (ax : ClassExpr × ClassExpr) : Bool :=
  edgeAntecedentRelevant ax.1

theorem edgeEntailsMembership_irrelevant (g : Graph) (st : RState)
    (i : Subject) (a : ClassExpr) (h : edgeAntecedentRelevant a = false) :
    edgeEntailsMembership g st i a = false := by
  cases a <;> simp_all [edgeAntecedentRelevant, edgeEntailsMembership]

def applyAxiomsEdgesStep (g : Graph) (i : Subject)
    (acc : RState × Bool × List ClassExpr) (ax : ClassExpr × ClassExpr) :
    RState × Bool × List ClassExpr :=
  let (s0, c0, ls) := acc
  let (a, d) := ax
  if !(memCe a ls) && edgeEntailsMembership g s0 i a then
    let (s1, c1) := addLabel s0 i a
    let (s2, c2) := addLabel s1 i d
    (s2, c0 || c1 || c2, labelsOf s2 i)
  else acc

theorem applyAxiomsEdgesStep_rejected (g : Graph) (i : Subject)
    (acc : RState × Bool × List ClassExpr) (ax : ClassExpr × ClassExpr)
    (h : edgeAxiomRelevant ax = false) :
    applyAxiomsEdgesStep g i acc ax = acc := by
  rcases ax with ⟨a, d⟩
  simp only [edgeAxiomRelevant] at h
  have he := edgeEntailsMembership_irrelevant g acc.1 i a h
  simp [applyAxiomsEdgesStep, he]

def applyAxiomsEdgesFrom (tb : List (ClassExpr × ClassExpr)) (g : Graph)
    (st : RState) (i : Subject) : RState × Bool :=
  let (st', ch, _) := tb.foldl (applyAxiomsEdgesStep g i)
    (st, false, labelsOf st i)
  (st', ch)

/-- Fire the axioms whose left-hand side the node's EDGES prove. The
    left-hand side is added as a label too, so the label-level clash
    rules see it. -/
def applyAxiomsEdges (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    (i : Subject) : RState × Bool :=
  -- The node's label read is HOISTED and refreshed only when an axiom
  -- actually fires — the sole way the labels change in this loop.
  -- Reading them per AXIOM costs one node-list walk per axiom per
  -- node per round.
  applyAxiomsEdgesFrom tb g st i

def applyAxiomsEdgesFiltered (tb : List (ClassExpr × ClassExpr)) (g : Graph)
    (st : RState) (i : Subject) : RState × Bool :=
  applyAxiomsEdgesFrom (tb.filter edgeAxiomRelevant) g st i

theorem applyAxiomsEdgesFrom_filter_eq (tb : List (ClassExpr × ClassExpr))
    (g : Graph) (st : RState) (i : Subject) :
    applyAxiomsEdgesFrom (tb.filter edgeAxiomRelevant) g st i =
      applyAxiomsEdgesFrom tb g st i := by
  simp only [applyAxiomsEdgesFrom]
  rw [foldl_filter_of_rejected_identity]
  exact applyAxiomsEdgesStep_rejected g i

theorem applyAxiomsEdgesFiltered_eq (tb : List (ClassExpr × ClassExpr))
    (g : Graph) (st : RState) (i : Subject) :
    applyAxiomsEdgesFiltered tb g st i = applyAxiomsEdges tb g st i := by
  exact applyAxiomsEdgesFrom_filter_eq tb g st i

@[csimp] theorem applyAxiomsEdges_eq_filtered :
    @applyAxiomsEdges = @applyAxiomsEdgesFiltered := by
  funext tb g st i
  exact (applyAxiomsEdgesFiltered_eq tb g st i).symm

/-- Fire an axiom whose left-hand side is an INTERSECTION when every
    conjunct is present as a SEPARATE label.

    `applyAxioms` matches one stored label against a whole left-hand
    side, so `z ≡ C₁ ⊓ C₂` never fires on a node carrying `C₁` and
    `C₂` apart. Labels are entailed memberships, and being in each
    `Cᵢ` IS being in the intersection, so the node is entailed in the
    left-hand side and hence in the right-hand side. -/
def conjunctionAxiomRelevant (ax : ClassExpr × ClassExpr) : Bool :=
  match ax.1 with
  | .intersection (_ :: _) => true
  | _                       => false

def applyAxiomsConjStep (i : Subject)
    (acc : RState × Bool × List ClassExpr) (ax : ClassExpr × ClassExpr) :
    RState × Bool × List ClassExpr :=
  let (s0, c0, ls) := acc
  let (a, d) := ax
  match a with
  | .intersection cs =>
      if cs.isEmpty || memCe a ls then acc
      else if cs.all (fun c => memCe c ls) then
        let (s1, c1) := addLabel s0 i a
        let (s2, c2) := addLabel s1 i d
        (s2, c0 || c1 || c2, labelsOf s2 i)
      else acc
  | _ => acc

theorem applyAxiomsConjStep_rejected (i : Subject)
    (acc : RState × Bool × List ClassExpr) (ax : ClassExpr × ClassExpr)
    (h : conjunctionAxiomRelevant ax = false) :
    applyAxiomsConjStep i acc ax = acc := by
  rcases ax with ⟨a, d⟩
  cases a <;> simp_all [conjunctionAxiomRelevant, applyAxiomsConjStep]
  case intersection cs =>
    cases cs <;> simp_all

def applyAxiomsConjFrom (tb : List (ClassExpr × ClassExpr)) (st : RState)
    (i : Subject) : RState × Bool :=
  let (st', ch, _) := tb.foldl (applyAxiomsConjStep i)
    (st, false, labelsOf st i)
  (st', ch)

def applyAxiomsConj (tb : List (ClassExpr × ClassExpr)) (st : RState) (i : Subject)
    : RState × Bool :=
  applyAxiomsConjFrom tb st i

def applyAxiomsConjFiltered (tb : List (ClassExpr × ClassExpr)) (st : RState)
    (i : Subject) : RState × Bool :=
  applyAxiomsConjFrom (tb.filter conjunctionAxiomRelevant) st i

theorem applyAxiomsConjFrom_filter_eq (tb : List (ClassExpr × ClassExpr))
    (st : RState) (i : Subject) :
    applyAxiomsConjFrom (tb.filter conjunctionAxiomRelevant) st i =
      applyAxiomsConjFrom tb st i := by
  simp only [applyAxiomsConjFrom]
  rw [foldl_filter_of_rejected_identity]
  exact applyAxiomsConjStep_rejected i

theorem applyAxiomsConjFiltered_eq (tb : List (ClassExpr × ClassExpr))
    (st : RState) (i : Subject) :
    applyAxiomsConjFiltered tb st i = applyAxiomsConj tb st i := by
  exact applyAxiomsConjFrom_filter_eq tb st i

@[csimp] theorem applyAxiomsConj_eq_filtered :
    @applyAxiomsConj = @applyAxiomsConjFiltered := by
  funext tb st i
  exact (applyAxiomsConjFiltered_eq tb st i).symm

/-- A TBox axiom whose antecedent is `owl:Thing` is a GLOBAL
    constraint, not one keyed on a label. `owl:Thing` is interpreted
    as the whole domain in every interpretation, so `owl:Thing ⊑ C`
    puts `C` on EVERY individual.

    `applyAxioms` fires an axiom only when a node's label
    structurally matches the antecedent, and no node carries
    `owl:Thing` as an asserted label, so such an axiom never fired at
    all. `owl:Thing ⊑ ≤1 f` is how the OilEd t7.3 fixture
    (`WebOnt-description-logic-030`) makes `f` functional; without it
    nothing bounds `f`, the two `f`-successors of the inner witness
    are never merged, and `p1` never meets `¬p1`.

    An empty intersection is `owl:Thing` too (`ClassExpr`), so both
    spellings fire. Sound for the same reason `injectFunctional` is:
    the consequent holds of every element, so writing it on every
    node adds a label the model already satisfies. -/
def isTopAntecedent : ClassExpr → Bool
  | .named c         => c == owlThing
  | .intersection [] => true
  | _                => false

def globalAxiomRelevant (ax : ClassExpr × ClassExpr) : Bool :=
  isTopAntecedent ax.1

def applyGlobalAxiomStep (n : RNode) (acc : RState × Bool)
    (ax : ClassExpr × ClassExpr) : RState × Bool :=
  let (a, d) := ax
  if isTopAntecedent a then
    let (s, ch) := addLabel acc.1 n.id d
    (s, acc.2 || ch)
  else acc

theorem applyGlobalAxiomStep_rejected (n : RNode) (acc : RState × Bool)
    (ax : ClassExpr × ClassExpr) (h : globalAxiomRelevant ax = false) :
    applyGlobalAxiomStep n acc ax = acc := by
  rcases ax with ⟨a, d⟩
  simp_all [globalAxiomRelevant, applyGlobalAxiomStep]

def injectGlobalAxiomsFrom (tb : List (ClassExpr × ClassExpr)) (st : RState)
    : RState × Bool :=
  st.nodes.foldl (fun (acc : RState × Bool) n =>
    tb.foldl (applyGlobalAxiomStep n) acc) (st, false)

def injectGlobalAxioms (tb : List (ClassExpr × ClassExpr)) (st : RState)
    : RState × Bool :=
  injectGlobalAxiomsFrom tb st

def injectGlobalAxiomsFiltered (tb : List (ClassExpr × ClassExpr)) (st : RState)
    : RState × Bool :=
  injectGlobalAxiomsFrom (tb.filter globalAxiomRelevant) st

theorem injectGlobalAxiomsFrom_filter_eq (tb : List (ClassExpr × ClassExpr))
    (st : RState) :
    injectGlobalAxiomsFrom (tb.filter globalAxiomRelevant) st =
      injectGlobalAxiomsFrom tb st := by
  simp only [injectGlobalAxiomsFrom]
  have hfold :
      (fun (acc : RState × Bool) (n : RNode) =>
        (tb.filter globalAxiomRelevant).foldl (applyGlobalAxiomStep n) acc) =
      (fun (acc : RState × Bool) (n : RNode) =>
        tb.foldl (applyGlobalAxiomStep n) acc) := by
    funext acc n
    rw [foldl_filter_of_rejected_identity]
    exact applyGlobalAxiomStep_rejected n
  rw [hfold]

theorem injectGlobalAxiomsFiltered_eq (tb : List (ClassExpr × ClassExpr))
    (st : RState) :
    injectGlobalAxiomsFiltered tb st = injectGlobalAxioms tb st := by
  exact injectGlobalAxiomsFrom_filter_eq tb st

@[csimp] theorem injectGlobalAxioms_eq_filtered :
    @injectGlobalAxioms = @injectGlobalAxiomsFiltered := by
  funext tb st
  exact (injectGlobalAxiomsFiltered_eq tb st).symm

/-- `owl:FunctionalProperty p` is a global `≤ 1 p` on every node,
    which folds the functionality constraint into the existing
    max-cardinality clash rule with no new machinery. -/
def injectFunctional (st : RState) : RState × Bool :=
  st.nodes.foldl (fun (acc : RState × Bool) n =>
    st.funcProps.foldl (fun (a2 : RState × Bool) p =>
      let (s, ch) := addLabel a2.1 n.id (.maxCard 1 p)
      (s, a2.2 || ch)) acc) (st, false)

/-- Process one node during a saturation pass. -/
def onePassNode (tb edgeTb conjTb : List (ClassExpr × ClassExpr))
    (g : Graph) (acc : RState × Bool) (n : RNode) : RState × Bool :=
    let byLabel := (labelsOf acc.1 n.id).foldl (fun (a2 : RState × Bool) l =>
      let (s1, c1) := applyLabelRules g a2.1 n.id l
      let (s2, c2) := applyAxioms tb s1 n.id l
      (s2, a2.2 || c1 || c2)) acc
    let (s3, c3) := applyAxiomsEdgesFrom edgeTb g byLabel.1 n.id
    let (s4, c4) := applyAxiomsConjFrom conjTb s3 n.id
    (s4, byLabel.2 || c3 || c4)

def onePassNodeDispatched (index : NamedAxiomIndex)
    (tb edgeTb conjTb : List (ClassExpr × ClassExpr))
    (g : Graph) (acc : RState × Bool) (n : RNode) : RState × Bool :=
    let byLabel := (labelsOf acc.1 n.id).foldl (fun (a2 : RState × Bool) l =>
      let (s1, c1) := applyLabelRules g a2.1 n.id l
      let (s2, c2) := applyAxiomsDispatched index tb s1 n.id l
      (s2, a2.2 || c1 || c2)) acc
    let (s3, c3) := applyAxiomsEdgesFrom edgeTb g byLabel.1 n.id
    let (s4, c4) := applyAxiomsConjFrom conjTb s3 n.id
    (s4, byLabel.2 || c3 || c4)

theorem onePassNodeDispatched_eq (tb edgeTb conjTb :
    List (ClassExpr × ClassExpr)) (g : Graph) (acc : RState × Bool)
    (n : RNode) :
    onePassNodeDispatched (buildNamedAxiomIndex tb) tb edgeTb conjTb g acc n =
      onePassNode tb edgeTb conjTb g acc n := by
  simp only [onePassNodeDispatched, onePassNode]
  have hstep :
      (fun (a2 : RState × Bool) l =>
        match applyLabelRules g a2.1 n.id l with
        | (s1, c1) =>
          match applyAxiomsDispatched (buildNamedAxiomIndex tb)
              tb s1 n.id l with
          | (s2, c2) => (s2, a2.2 || c1 || c2)) =
      (fun (a2 : RState × Bool) l =>
        match applyLabelRules g a2.1 n.id l with
        | (s1, c1) =>
          match applyAxioms tb s1 n.id l with
          | (s2, c2) => (s2, a2.2 || c1 || c2)) := by
    funext a2 l
    generalize applyLabelRules g a2.1 n.id l = labelResult
    rcases labelResult with ⟨s1, c1⟩
    simp only
    rw [applyAxiomsDispatched_eq]
  rw [hstep]

theorem onePassNode_filter_eq (tb : List (ClassExpr × ClassExpr))
    (g : Graph) (acc : RState × Bool) (n : RNode) :
    onePassNode tb (tb.filter edgeAxiomRelevant)
        (tb.filter conjunctionAxiomRelevant) g acc n =
      onePassNode tb tb tb g acc n := by
  simp only [onePassNode]
  rw [applyAxiomsEdgesFrom_filter_eq]
  generalize applyAxiomsEdgesFrom tb g
    (List.foldl
      (fun a2 l =>
        match applyLabelRules g a2.1 n.id l with
        | (s1, c1) =>
          match applyAxioms tb s1 n.id l with
          | (s2, c2) => (s2, a2.2 || c1 || c2))
      acc (labelsOf acc.1 n.id)).1 n.id = edgeResult
  rcases edgeResult with ⟨s3, c3⟩
  rw [applyAxiomsConjFrom_filter_eq]

/-- Node-local part of one saturation pass, parameterized by the TBox
    subsets used by the two shape-specific rules. -/
def onePassNodes (tb edgeTb conjTb : List (ClassExpr × ClassExpr))
    (g : Graph) (st1 : RState) (ch1 : Bool) : RState × Bool :=
  st1.nodes.foldl (onePassNode tb edgeTb conjTb g) (st1, ch1)

def onePassNodesDispatched (index : NamedAxiomIndex)
    (tb edgeTb conjTb : List (ClassExpr × ClassExpr))
    (g : Graph) (st1 : RState) (ch1 : Bool) : RState × Bool :=
  st1.nodes.foldl
    (onePassNodeDispatched index tb edgeTb conjTb g) (st1, ch1)

theorem onePassNodesDispatched_eq (tb edgeTb conjTb :
    List (ClassExpr × ClassExpr)) (g : Graph) (st : RState) (ch : Bool) :
    onePassNodesDispatched (buildNamedAxiomIndex tb)
        tb edgeTb conjTb g st ch =
      onePassNodes tb edgeTb conjTb g st ch := by
  simp only [onePassNodesDispatched, onePassNodes]
  have hstep :
      onePassNodeDispatched (buildNamedAxiomIndex tb)
          tb edgeTb conjTb g =
        onePassNode tb edgeTb conjTb g := by
    funext acc n
    exact onePassNodeDispatched_eq tb edgeTb conjTb g acc n
  rw [hstep]

theorem onePassNodes_filter_eq (tb : List (ClassExpr × ClassExpr))
    (g : Graph) (st : RState) (ch : Bool) :
    onePassNodes tb (tb.filter edgeAxiomRelevant)
        (tb.filter conjunctionAxiomRelevant) g st ch =
      onePassNodes tb tb tb g st ch := by
  simp only [onePassNodes]
  have hstep :
      onePassNode tb (tb.filter edgeAxiomRelevant)
          (tb.filter conjunctionAxiomRelevant) g =
        onePassNode tb tb tb g := by
    funext acc n
    exact onePassNode_filter_eq tb g acc n
  rw [hstep]

/-- One saturation pass over every node and every label it carries. -/
def onePass (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    : RState × Bool :=
  let (st0, ch0) := injectFunctional st
  let (st1, chG) := injectGlobalAxioms tb st0
  onePassNodes tb tb tb g st1 (ch0 || chG)

/-- Compiled one-pass implementation. Each shape-specific TBox list
    and the named-antecedent dispatch index are built once before the
    node loop. Nonnamed labels retain the complete TBox fallback. -/
def onePassFiltered (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    : RState × Bool :=
  let labelIndex := buildNamedAxiomIndex tb
  let edgeTb := tb.filter edgeAxiomRelevant
  let conjTb := tb.filter conjunctionAxiomRelevant
  let globalTb := tb.filter globalAxiomRelevant
  let (st0, ch0) := injectFunctional st
  let (st1, chG) := injectGlobalAxiomsFrom globalTb st0
  onePassNodesDispatched labelIndex tb edgeTb conjTb g st1 (ch0 || chG)

theorem onePassFiltered_eq (tb : List (ClassExpr × ClassExpr)) (g : Graph)
    (st : RState) : onePassFiltered tb g st = onePass tb g st := by
  simp only [onePassFiltered, onePass, injectGlobalAxioms]
  rw [injectGlobalAxiomsFrom_filter_eq]
  rw [onePassNodesDispatched_eq]
  exact onePassNodes_filter_eq tb g _ _

@[csimp] theorem onePass_eq_filtered : @onePass = @onePassFiltered := by
  funext tb g st
  exact (onePassFiltered_eq tb g st).symm

/-! ## The ≤-rule: merging witness successors

For a positive maximum, `clashForLabel` fires only on PROVABLY
DISTINCT successors and does not count fresh witnesses. So a node with more
successors than `≤ k p` allows, whose successors are not forced
apart, is not caught by it at all — and the commonest shape is
exactly that: two separate `∃`-witnesses, or a witness and an
asserted successor of a subrole, widened together by a role
hierarchy or an `owl:FunctionalProperty` declaration. Seventeen of
the `WebOnt-description-logic` inconsistency fixtures are that shape.

The standard SHIQ ≤-rule closes it: pick two successors not yet
forced apart and IDENTIFY them, merging labels and redirecting
edges, until the count is within `k` or a clash appears.

**Why triggering on witnesses is sound.** If `≤ k p` holds of `i` in
every model and `i` has more than `k` successors as TERMS, then in
every model some two of those terms denote one domain element — that
is what `≤ k p` says, by pigeonhole. WHICH pair coincides is a
choice the rule makes arbitrarily, so for REFUTATION every choice
must close: the search branches over every mergeable pair and
requires ALL of them to clash, exactly as it does for a union's
disjuncts.

**Why named resources participate.** Identification is recorded in
the state, and label/edge readers pool each identification group.
Both named and generated resource successors may therefore be
identified. Covering every coincidence a model could choose is
necessary before all closed merge branches justify a refutation.

A pair already forced apart is never offered: merging a provably
distinct pair is unsound, not merely unhelpful. -/

/-- A term the ≤-rule may identify with another: a blank node or a
    named individual, never a literal.

    **Named individuals were excluded until 2026-09-07, and excluding
    them was not the safe direction.** The header's argument was that
    a named individual's graph-asserted edges cannot be rewritten, so
    a merge would leave a half-merged state. That argument describes
    the REWRITING merge this module no longer has: `mergeInto` records
    an identification pair, and `labelsOf` / `successorsOf` pool the
    group across the input graph as well as the expansion edges
    (`identifiedWith`, used in both). Nothing is rewritten, so nothing
    is half-rewritten.

    The exclusion was also unsound in the direction that matters. The
    ≤-rule refutes a node only when EVERY offered merge closes, and
    that is an argument only if the offered merges COVER every
    coincidence a model could choose. With `≤ k p` and more than `k`
    successors, pigeonhole says some two successor TERMS denote one
    element; if the pair a model picks is not offered, "every offered
    merge closes" proves nothing. Offering only blank nodes left every
    pair involving a named successor uncovered. Offering every
    non-provably-distinct pair of resource successors restores the
    cover.

    Literals stay out. A literal and an IRI denote in disjoint domains
    under OWL 2 Direct Semantics (§ 2.2, the object domain and the
    data domain), and two literals with different values are already
    `provablyDistinct`, so no pair involving a literal is a
    coincidence a model may choose. A cardinality bound measured over
    a literal successor of an OBJECT property is outside this
    argument; it is recorded as the residual in
    `docs/designissues/2026-09-07-lean-owl-corpus-gap.md` § 11. -/
def isMergeableTerm : Term → Bool
  | .bnode _ => true
  | .iri _   => true
  | _        => false

private def witnessPairs (g : Graph) (st : RState) (succs : List Term) (k : Nat)
    : List (Term × Term) :=
  if succs.length ≤ k then []
  else
    let ws := succs.filter isMergeableTerm
    ws.flatMap (fun a =>
      ws.filterMap (fun b =>
        if a != b && !(provablyDistinctGrouped g st a b) then some (a, b) else none))

/-- The witness pairs a `≤ k p` label could be forced to identify.
    A qualified bound ranges only over successors already proved to
    satisfy its filler. Merging other successors can manufacture a
    clash in a model where the filler extension is empty. -/
def mergePairsForLabel (g : Graph) (st : RState) (i : Subject) (l : ClassExpr)
    : List (Term × Term) :=
  match l with
  | .maxCard k p => witnessPairs g st (successorsOf g st i p false) k
  | .maxQualCard k p c =>
      witnessPairs g st (successorsInFiller st c (successorsOf g st i p false)) k
  | _ => []

/-- Identify `a` with `b`: ONE entry in the branch's identification
    list. Nothing is rewritten — `labelsOf` and `successorsOf` pool
    the group when they read it.

    Rewriting was tried first and does not work here. An edge
    asserted in the INPUT GRAPH cannot be rewritten at all, and the
    materialisation pass writes its own existential witnesses into
    the graph, so a rewriting merge silently missed every successor
    that came from there — which on the real path is most of
    them. -/
def mergeInto (st : RState) (a b : Term) : RState :=
  if repOf st a == repOf st b then st
  else { st with ident := st.ident ++ [(repOf st a, repOf st b)] }

/-- The first node whose `≤` label forces a merge, and the choices. -/
def pendingMerge (g : Graph) (st : RState) : Option (List (Term × Term)) :=
  st.nodes.findSome? (fun n =>
    n.labels.findSome? (fun l =>
      match mergePairsForLabel g st n.id l with
      | []    => none
      | pairs => some pairs))

/-! ## Nominal identification

An `i : {m₁ … mₖ}` label says that `i` denotes one of the members.
Refutation therefore branches over every live equality choice and may
close the nominal only when every choice closes. A choice already made
is idempotent. Members forced apart from `i` are impossible choices.
If any remaining member is a literal, the whole label is withheld:
exploring only the representable resource choices would not cover every
model. -/

def nominalChoiceMade (st : RState) (i : Subject) (members : List Term) : Bool :=
  members.any (fun m => repOf st i.toTerm == repOf st m)

private def nominalCandidatePairs (g : Graph) (st : RState) (i : Subject)
    (members : List Term) : Option (List (Term × Term)) :=
  (members.foldl (fun acc m =>
    match acc with
    | none => none
    | some rev =>
        if provablyDistinctGrouped g st i.toTerm m then some rev
        else if isMergeableTerm m then some ((i.toTerm, m) :: rev)
        else none) (some [])).map List.reverse

/-- Every unresolved nominal label whose complete set of live choices
    can be represented as identifications, in node and label order. -/
def pendingNominals (g : Graph) (st : RState) : List (List (Term × Term)) :=
  st.nodes.flatMap (fun n =>
    (labelsOf st n.id).filterMap (fun l =>
      match l with
      | .oneOf members =>
          if nominalChoiceMade st n.id members then none
          else
            match nominalCandidatePairs g st n.id members with
            | some (p :: rest) => some (p :: rest)
            | _                => none
      | _ => none))

/-- Every currently forced nominal equality, in node, label, and member
    order. Genuine choices are omitted: only a complete candidate list
    containing exactly one pair contributes an equality. -/
def forcedNominalPairs (g : Graph) (st : RState) : List (Term × Term) :=
  (st.nodes.foldl (fun rev n =>
    (labelsOf st n.id).foldl (fun rev l =>
      match l with
      | .oneOf members =>
          if nominalChoiceMade st n.id members then rev
          else
            match nominalCandidatePairs g st n.id members with
            | some [pair] => pair :: rev
            | _           => rev
      | _ => rev) rev) []).reverse

/-- A finite bound for repeated forced-nominal sweeps. Each productive
    sweep identifies two previously separate representatives. The node
    identifiers and the nominal member occurrences bound all terms that
    these sweeps can identify. -/
private def forcedNominalFuel (st : RState) : Nat :=
  st.nodes.foldl (fun total n =>
    n.labels.foldl (fun total l =>
      match l with
      | .oneOf members => total + members.length
      | _              => total) total) st.nodes.length

/-- Apply every entailed singleton nominal equality before returning to
    the expensive tableau pass. A new equality can expose another unit,
    so the bounded loop repeats. Exhaustion merely returns the current
    state; the ordinary search can resume propagation on its next visit. -/
private def propagateForcedNominalsLoop (g : Graph) : Nat → RState → RState
  | 0, st => st
  | fuel + 1, st =>
      match forcedNominalPairs g st with
      | [] => st
      | pairs =>
          let st' := pairs.foldl (fun acc pair => mergeInto acc pair.1 pair.2) st
          propagateForcedNominalsLoop g fuel st'

def propagateForcedNominals (g : Graph) (st : RState) : RState :=
  propagateForcedNominalsLoop g (forcedNominalFuel st) st

/-- Prefer a forced nominal equality before the first genuine choice.
    This is unit propagation: a singleton live candidate holds in every
    model of the branch and needs no suspended sibling. If no unit is
    available, the first nominal retains the source order and all its
    candidates are explored. -/
def pendingNominal (g : Graph) (st : RState) : Option (List (Term × Term)) :=
  let all := pendingNominals g st
  match all.find? (fun pairs => pairs.length == 1) with
  | some forced => some forced
  | none        => all.head?

/-- Does a lower-bound label still lack a required successor?

    At an ordinary fixpoint this is false because `processLabel`
    creates the missing witness. It remains true when a witness was
    withheld by the depth bound or fresh-name exhaustion. Such a state
    is not evidence of consistency and must not be returned as open. -/
def pendingWitnessObligation (g : Graph) (st : RState) : Bool :=
  st.nodes.any fun n =>
    (labelsOf st n.id).any fun l =>
      match l with
      | .someOf p (.oneOf [a]) =>
          !(successorsOf g st n.id p false).any (fun y => y == a)
      | .someOf p .unknown => (successorsOf g st n.id p false).isEmpty
      | .someOf p c =>
          (successorsInFiller st c (successorsOf g st n.id p false)).isEmpty
      | .minQualCard k p .unknown =>
          (successorsOf g st n.id p false).length < k
      | .minQualCard k p c =>
          (successorsInFiller st c (successorsOf g st n.id p false)).length < k
      | .minCard k p => (successorsOf g st n.id p false).length < k
      | _ => false

/-! ## The search

Saturate; if a clash appears, this branch closes. Otherwise take the
first unexpanded `union` label and try every disjunct: the node is
refuted only when EVERY disjunct closes. -/

inductive Verdict where
  | clash
  | open'
  | out
  deriving DecidableEq, Repr, Inhabited, Nonempty

/-- The first `(node, disjuncts)` of a `union` label none of whose
    disjuncts is already a label of that node. A union with a disjunct
    already present is satisfied and needs no branch. -/
def pendingUnion (st : RState) : Option (Subject × List ClassExpr) :=
  (st.nodes.findSome? (fun n =>
    let ls := labelsOf st n.id
    ls.findSome? (fun l =>
      match l with
      | .union cs =>
          if cs.any (fun c => memCe c ls) then none
          else some (n.id, cs)
      | _ => none)))

/-- A suspended branch point. The base state and unvisited choices are
    retained so each sibling is made from the same quiescent state.
    `rest` is in the original choice order. -/
private inductive SearchFrame where
  | union (base : RState) (i : Subject) (rest : List ClassExpr)
  | merge (st : RState) (rest : List (Term × Term))

/-- Remove the matching union label once for the whole branch point. -/
private def removeUnionLabel (st : RState) (i : Subject)
    (choices : List ClassExpr) : RState :=
  { st with
    nodes := st.nodes.map (fun m =>
      if m.id == i then
        { m with labels := m.labels.filter (fun l =>
            match l with
            | .union es => !(ClassExpr.beqList es choices)
            | _         => true) }
      else m) }

/-- Add one disjunct to the branch-point base state. Every sibling
    starts from this same state. -/
private def unionBranch (base : RState) (i : Subject) (c : ClassExpr) : RState :=
  (addLabel base i c).1

/-- Pop closed branch points until the next sibling is found. This is
    administrative work: it consumes no search budget. -/
private def nextAfterClash : List SearchFrame → Option (RState × List SearchFrame)
  | [] => none
  | .union _ _ [] :: frames => nextAfterClash frames
  | .union base i (c :: rest) :: frames =>
      some (unionBranch base i c, .union base i rest :: frames)
  | .merge _ [] :: frames => nextAfterClash frames
  | .merge st ((x, y) :: rest) :: frames =>
      some (mergeInto st x y, .merge st rest :: frames)

/-- Total depth-first tableau search with one shared visit budget.

    The explicit continuation stack records only unvisited siblings.
    Recursive calls always receive the predecessor budget, including
    calls made after a clash selects a sibling. Popping exhausted frames
    is a separate tail-recursive list walk and consumes no semantic
    budget. -/
private def searchLoop (tb : List (ClassExpr × ClassExpr)) (g : Graph)
    (st : RState) (frames : List SearchFrame) (budget : Nat) : Verdict × Nat :=
  match budget with
  | 0 => (.out, 0)
  | n + 1 =>
    if clashNodes g st then
      match nextAfterClash frames with
      | none => (.clash, n)
      | some (next, frames') => searchLoop tb g next frames' n
    else
      let (st', changed) := onePass tb g st
      if changed then searchLoop tb g st' frames n
      else if clashNodes g st' then
        match nextAfterClash frames with
        | none => (.clash, n)
        | some (next, frames') => searchLoop tb g next frames' n
      else
        match pendingUnion st' with
        | some (i, cs) =>
          let choices := liveUnionChoices cs (labelsOf st' i)
          match choices with
          | [] =>
            match nextAfterClash frames with
            | none => (.clash, n)
            | some (next, frames') => searchLoop tb g next frames' n
          | c :: rest =>
            let base := removeUnionLabel st' i cs
            searchLoop tb g (unionBranch base i c) (.union base i rest :: frames) n
        | none =>
          match pendingMerge g st' with
          | none =>
            match pendingNominal g st' with
            | none =>
              if pendingWitnessObligation g st' then (.out, n)
              else (.open', n)
            | some pairs =>
              match pairs with
              | [] =>
                match nextAfterClash frames with
                | none => (.clash, n)
                | some (next, frames') => searchLoop tb g next frames' n
              | [(x, y)] =>
                searchLoop tb g (propagateForcedNominals g (mergeInto st' x y)) frames n
              | (x, y) :: rest =>
                searchLoop tb g (mergeInto st' x y) (.merge st' rest :: frames) n
          | some pairs =>
            match pairs with
            | [] =>
              match nextAfterClash frames with
              | none => (.clash, n)
              | some (next, frames') => searchLoop tb g next frames' n
            | (x, y) :: rest =>
              searchLoop tb g (mergeInto st' x y) (.merge st' rest :: frames) n

/-- The search, with the budget THREADED through the branches rather
    than handed to each in full.

    A per-branch budget lets a node with `d` choices grow a tree of
    `d^budget` states: siblings each get the whole allowance and the
    total is the product. A threaded budget makes them draw from ONE
    pool, so the search costs what the pool says and no more. Running
    out answers `out`, which the caller reads as "not refuted" — the
    same withholding as every other cap here.

    Returns the verdict and what is left. -/
def search (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    (budget : Nat) : Verdict × Nat :=
  searchLoop tb g st [] budget

/-- The internal loop never returns more budget than its caller supplied. -/
private theorem searchLoop_remaining_le (tb : List (ClassExpr × ClassExpr))
    (g : Graph) (budget : Nat) : ∀ st frames,
    (searchLoop tb g st frames budget).2 ≤ budget := by
  induction budget with
  | zero => simp [searchLoop]
  | succ n ih =>
      intro st frames
      simp only [searchLoop]
      repeat' first | split
      all_goals first
        | omega
        | exact Nat.le_trans (ih _ _) (Nat.le_succ n)

/-- A search never returns more budget than its caller supplied. -/
theorem search_remaining_le (tb : List (ClassExpr × ClassExpr)) (g : Graph)
    (st : RState) (budget : Nat) : (search tb g st budget).2 ≤ budget :=
  searchLoop_remaining_le tb g budget st []

/-- Zero budget performs no state visit. -/
theorem search_zero (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState) :
    search tb g st 0 = (.out, 0) := rfl

/-- An immediate clash consumes exactly one visit when there is no
    enclosing branch continuation. -/
theorem search_immediate_clash (tb : List (ClassExpr × ClassExpr)) (g : Graph)
    (st : RState) (n : Nat) (h : clashNodes g st = true) :
    search tb g st (n + 1) = (.clash, n) := by
  simp [search, searchLoop, h, nextAfterClash]

/-- A changing saturation pass consumes one visit and continues from
    the updated state. -/
theorem search_changed (tb : List (ClassExpr × ClassExpr)) (g : Graph)
    (st st' : RState) (n : Nat) (hClash : clashNodes g st = false)
    (hPass : onePass tb g st = (st', true)) :
    search tb g st (n + 1) = search tb g st' n := by
  simp [search, searchLoop, hClash, hPass]

/-! ## The entry point -/

/-- Seed the entailed membership of every resource in every complete
    named `owl:oneOf` declaration. Processing marker triples rather
    than asking for one subject-level parse preserves multiple
    declarations on the same named class. -/
def seedNamedOneOfMembers (st : RState) : RState :=
  st.store.graph.foldl (fun acc t =>
    match t.s with
    | .bnode _ => acc
    | .iri z =>
      if t.p == owlOneOf then
        match walkRdfListComplete st.store t.o with
        | none => acc
        | some members => members.foldl (fun s m =>
            match termAsSubject m with
            | none   => s
            | some i => (addLabel s i (.named z)).1) acc
      else acc) st

/-- One parsed initial `rdf:type` membership. Keeping parsing outside
    the grouping algorithm makes its equality theorem independent of
    graph and class-expression parsing. -/
abbrev InitialLabel := Subject × ClassExpr

def keepInitialLabel : ClassExpr → Bool
  | .unknown => false
  | _        => true

/-- List specification for initial label grouping. It is the `nodes`
    part of `addLabel` when the initial state has no nodes or
    identifications. -/
def addInitialLabelNode (nodes : List RNode) (entry : InitialLabel) : List RNode :=
  let (i, c) := entry
  if keepInitialLabel c then
    let labels := match nodes.find? (fun n => n.id == i) with
      | some n => n.labels
      | none   => []
    if memCe c labels then nodes
    else if nodes.any (fun n => n.id == i) then
      nodes.map (fun n =>
        if n.id == i then { n with labels := n.labels ++ [c] } else n)
    else nodes ++ [{ id := i, labels := [c] }]
  else nodes

/-- On an unmerged initial state, `addLabel` changes exactly the node
    list described by `addInitialLabelNode`. -/
theorem addLabel_initial (st : RState) (i : Subject) (c : ClassExpr)
    (hIdent : st.ident = []) :
    (addLabel st i c).1 =
      { st with nodes := addInitialLabelNode st.nodes (i, c) } := by
  cases c <;> simp only [addLabel, addInitialLabelNode, keepInitialLabel,
    labelsOf, hIdent, List.isEmpty_nil, ↓reduceIte]
  all_goals
    repeat' split
    all_goals cases st <;> simp_all

def initialLabelNodesSpec (entries : List InitialLabel) : List RNode :=
  entries.foldl addInitialLabelNode []

/-- Add an initially empty tableau node for a graph subject, preserving
    first-subject-appearance order.  Initialising all subjects is required
    because global property characteristics can contradict assertions even
    when the assertion subject has no `rdf:type` triple. -/
def ensureInitialSubjectNode (nodes : List RNode) (i : Subject) : List RNode :=
  if nodes.any (fun n => n.id == i) then nodes
  else nodes ++ [{ id := i, labels := [] }]

theorem fold_addLabel_initial (entries : List InitialLabel) (st : RState)
    (hIdent : st.ident = []) :
    entries.foldl (fun acc entry =>
      (addLabel acc entry.1 entry.2).1) st =
    { st with nodes := entries.foldl addInitialLabelNode st.nodes } := by
  induction entries generalizing st with
  | nil =>
      simp only [List.foldl_nil]
  | cons entry entries ih =>
      rcases entry with ⟨i, c⟩
      simp only [List.foldl_cons]
      rw [addLabel_initial st i c hIdent]
      rw [ih]
      simpa using hIdent

/-- Runtime builder for initial labels. `subjects` is first-appearance
    order. Each HashMap bucket is the corresponding append-order label
    list. -/
structure InitialLabelBuilder where
  subjects : Array Subject := #[]
  labels   : Std.HashMap Subject (List ClassExpr) := ∅

def InitialLabelBuilder.add (b : InitialLabelBuilder)
    (entry : InitialLabel) : InitialLabelBuilder :=
  let (i, c) := entry
  if keepInitialLabel c then
    match b.labels[i]? with
    | some labels =>
        if memCe c labels then b
        else { b with labels := b.labels.insert i (labels ++ [c]) }
    | none =>
        { subjects := b.subjects.push i,
          labels := b.labels.insert i [c] }
  else b

/-- Indexed counterpart of `ensureInitialSubjectNode`. -/
def InitialLabelBuilder.addSubject (b : InitialLabelBuilder)
    (i : Subject) : InitialLabelBuilder :=
  if b.labels.contains i then b
  else { subjects := b.subjects.push i,
         labels := b.labels.insert i [] }

def InitialLabelBuilder.nodes (b : InitialLabelBuilder) : List RNode :=
  b.subjects.toList.map (fun i =>
    { id := i, labels := b.labels.getD i [] })

/-- Builder invariant: subjects occur once, and the HashMap domain is
    exactly the subject array. -/
def InitialLabelBuilder.WF (b : InitialLabelBuilder) : Prop :=
  b.subjects.toList.Nodup ∧
  ∀ i, i ∈ b.labels ↔ i ∈ b.subjects.toList

theorem InitialLabelBuilder.empty_wf :
    InitialLabelBuilder.WF {} := by
  simp [InitialLabelBuilder.WF]

theorem InitialLabelBuilder.addSubject_wf (b : InitialLabelBuilder)
    (i : Subject) (h : b.WF) : (b.addSubject i).WF := by
  by_cases hc : b.labels.contains i = true
  · simpa [InitialLabelBuilder.addSubject, hc] using h
  · have hiMap : i ∉ b.labels := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
      intro hi
      exact hc ((Std.HashMap.mem_iff_isSome_getElem?).mp hi)
    have hi : i ∉ b.subjects.toList := by
      intro hiSubjects
      exact hiMap ((h.2 i).mpr hiSubjects)
    simp only [InitialLabelBuilder.addSubject, hc, Bool.false_eq_true,
      ↓reduceIte, InitialLabelBuilder.WF, Array.toList_push]
    constructor
    · rw [List.nodup_append]
      refine ⟨h.1, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact fun hai => hi (hai ▸ ha)
    · intro j
      rw [Std.HashMap.mem_insert, h.2]
      simp only [beq_iff_eq, List.mem_append, List.mem_singleton]
      constructor
      · intro hj
        cases hj with
        | inl hij => exact Or.inr hij.symm
        | inr hj  => exact Or.inl hj
      · intro hj
        cases hj with
        | inl hj  => exact Or.inr hj
        | inr hji => exact Or.inl hji.symm

theorem InitialLabelBuilder.add_wf (b : InitialLabelBuilder)
    (entry : InitialLabel) (h : b.WF) : (b.add entry).WF := by
  rcases entry with ⟨i, c⟩
  by_cases hc : keepInitialLabel c = true
  · cases hget : b.labels[i]? with
    | some labels =>
        have hiMap : i ∈ b.labels := by
          rw [Std.HashMap.mem_iff_isSome_getElem?]
          simp [hget]
        have hi : i ∈ b.subjects.toList := (h.2 i).mp hiMap
        by_cases hm : memCe c labels = true
        · simpa [InitialLabelBuilder.add, hc, hget, hm] using h
        · simp only [Bool.not_eq_true] at hm
          simp only [InitialLabelBuilder.add, hc, ↓reduceIte, hget, hm,
            Bool.false_eq_true]
          constructor
          · exact h.1
          · intro j
            rw [Std.HashMap.mem_insert, h.2]
            simp only [beq_iff_eq]
            constructor
            · intro hj
              cases hj with
              | inl hij => exact hij ▸ hi
              | inr hj  => exact hj
            · intro hj
              exact Or.inr hj
    | none =>
        have hiNotMap : i ∉ b.labels := by
          intro hi
          have := (Std.HashMap.mem_iff_isSome_getElem?).mp hi
          simp [hget] at this
        have hi : i ∉ b.subjects.toList := by
          intro hiSubjects
          exact hiNotMap ((h.2 i).mpr hiSubjects)
        simp only [InitialLabelBuilder.add, hc, ↓reduceIte, hget,
          InitialLabelBuilder.WF, Array.toList_push]
        constructor
        · rw [List.nodup_append]
          refine ⟨h.1, by simp, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst b
          exact fun hai => hi (hai ▸ ha)
        · intro j
          rw [Std.HashMap.mem_insert, h.2]
          simp only [beq_iff_eq, List.mem_append, List.mem_singleton]
          constructor
          · intro hj
            cases hj with
            | inl hij => exact Or.inr hij.symm
            | inr hj  => exact Or.inl hj
          · intro hj
            cases hj with
            | inl hj  => exact Or.inr hj
            | inr hji => exact Or.inl hji.symm
  · simp only [Bool.not_eq_true] at hc
    simpa [InitialLabelBuilder.add, hc] using h

theorem findSubject_self (i : Subject) :
    ∀ xs : List Subject, i ∈ xs → xs.find? (fun j => j == i) = some i
  | [], h => by simp at h
  | x :: xs, h => by
      by_cases hx : x = i
      · subst x
        simp
      · have hi : i ∈ xs := (List.mem_cons.mp h).resolve_left
          (fun hix => hx hix.symm)
        simp [hx, findSubject_self i xs hi]

theorem findSubject_none (i : Subject) :
    ∀ xs : List Subject, i ∉ xs → xs.find? (fun j => j == i) = none := by
  intro xs hi
  rw [List.find?_eq_none]
  intro j hj hji
  exact hi ((beq_iff_eq.mp hji) ▸ hj)

theorem InitialLabelBuilder.nodes_find (b : InitialLabelBuilder)
    (h : b.WF) (i : Subject) (labels : List ClassExpr)
    (hget : b.labels[i]? = some labels) :
    b.nodes.find? (fun n => n.id == i) = some { id := i, labels := labels } := by
  have hiMap : i ∈ b.labels := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    simp [hget]
  have hi : i ∈ b.subjects.toList := (h.2 i).mp hiMap
  simp only [InitialLabelBuilder.nodes, List.find?_map]
  change Option.map (fun j => ({ id := j, labels := b.labels.getD j [] } : RNode))
      (b.subjects.toList.find? (fun j => j == i)) =
    some ({ id := i, labels := labels } : RNode)
  rw [findSubject_self i b.subjects.toList hi]
  simp only [Option.map_some]
  rw [Std.HashMap.getD_eq_getD_getElem?, hget]
  rfl

theorem InitialLabelBuilder.nodes_find_none (b : InitialLabelBuilder)
    (i : Subject) (hi : i ∉ b.subjects.toList) :
    b.nodes.find? (fun n => n.id == i) = none := by
  simp only [InitialLabelBuilder.nodes, List.find?_map]
  change Option.map (fun j => ({ id := j, labels := b.labels.getD j [] } : RNode))
      (b.subjects.toList.find? (fun j => j == i)) = none
  rw [findSubject_none i b.subjects.toList hi]
  rfl

theorem InitialLabelBuilder.nodes_any (b : InitialLabelBuilder)
    (h : b.WF) (i : Subject) :
    b.nodes.any (fun n => n.id == i) = b.labels.contains i := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro hany
    rw [List.any_eq_true] at hany
    rcases hany with ⟨n, hn, hni⟩
    simp only [InitialLabelBuilder.nodes, List.mem_map] at hn
    rcases hn with ⟨j, hj, rfl⟩
    simp only at hni
    have hji : j = i := beq_iff_eq.mp hni
    subst j
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    exact (Std.HashMap.mem_iff_isSome_getElem?).mp ((h.2 i).mpr hj)
  · intro hcontains
    have hiMap : i ∈ b.labels := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hcontains
      exact (Std.HashMap.mem_iff_isSome_getElem?).mpr hcontains
    have hi : i ∈ b.subjects.toList := (h.2 i).mp hiMap
    rw [List.any_eq_true]
    refine ⟨{ id := i, labels := b.labels.getD i [] }, ?_, by simp⟩
    unfold InitialLabelBuilder.nodes
    exact List.mem_map.mpr ⟨i, hi, rfl⟩

theorem InitialLabelBuilder.addSubject_nodes (b : InitialLabelBuilder)
    (i : Subject) (h : b.WF) :
    (b.addSubject i).nodes = ensureInitialSubjectNode b.nodes i := by
  have hany := b.nodes_any h i
  by_cases hc : b.labels.contains i = true
  · simp [InitialLabelBuilder.addSubject, ensureInitialSubjectNode, hc, hany]
  · have hcFalse : b.labels.contains i = false := by
      cases hvalue : b.labels.contains i with
      | false => rfl
      | true  => simp_all
    have hiMap : i ∉ b.labels := by
      intro hi
      have his := (Std.HashMap.mem_iff_isSome_getElem?).mp hi
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hcFalse
      simp [hcFalse] at his
    have hi : i ∉ b.subjects.toList := by
      intro hiSubjects
      exact hiMap ((h.2 i).mpr hiSubjects)
    simp only [InitialLabelBuilder.addSubject, ensureInitialSubjectNode,
      hcFalse, Bool.false_eq_true, ↓reduceIte]
    rw [hany, hcFalse]
    simp only [Bool.false_eq_true, ↓reduceIte, InitialLabelBuilder.nodes,
      Array.toList_push, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := fun hji => hi (hji ▸ hj)
      have hij : i ≠ j := fun hij => hji hij.symm
      simp [Std.HashMap.getD_eq_getD_getElem?,
        Std.HashMap.getElem?_insert, hij]
    · simp only [List.map_cons, List.map_nil]
      rw [Std.HashMap.getD_eq_getD_getElem?,
        Std.HashMap.getElem?_insert]
      simp

theorem InitialLabelBuilder.foldSubject_nodes (subjects : List Subject)
    (b : InitialLabelBuilder) (h : b.WF) :
    (subjects.foldl InitialLabelBuilder.addSubject b).nodes =
      subjects.foldl ensureInitialSubjectNode b.nodes := by
  induction subjects generalizing b with
  | nil => rfl
  | cons i subjects ih =>
      simp only [List.foldl_cons]
      rw [ih (b.addSubject i) (b.addSubject_wf i h), b.addSubject_nodes i h]

theorem InitialLabelBuilder.foldSubject_wf (subjects : List Subject)
    (b : InitialLabelBuilder) (h : b.WF) :
    (subjects.foldl InitialLabelBuilder.addSubject b).WF := by
  induction subjects generalizing b with
  | nil => exact h
  | cons i subjects ih =>
      exact ih (b.addSubject i) (b.addSubject_wf i h)

theorem InitialLabelBuilder.add_nodes (b : InitialLabelBuilder)
    (entry : InitialLabel) (h : b.WF) :
    (b.add entry).nodes = addInitialLabelNode b.nodes entry := by
  rcases entry with ⟨i, c⟩
  by_cases hc : keepInitialLabel c = true
  · cases hget : b.labels[i]? with
    | some labels =>
        have hfind := b.nodes_find h i labels hget
        have hany := b.nodes_any h i
        have hcontains : b.labels.contains i = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hget]
          rfl
        by_cases hm : memCe c labels = true
        · simp [InitialLabelBuilder.add, addInitialLabelNode, hc, hget, hm,
            hfind]
        · simp only [Bool.not_eq_true] at hm
          simp only [InitialLabelBuilder.add, addInitialLabelNode, hc,
            ↓reduceIte, hget, hfind, hm, Bool.false_eq_true]
          rw [hany, hcontains]
          simp only [↓reduceIte, InitialLabelBuilder.nodes]
          rw [List.map_map]
          apply List.map_congr_left
          intro j hj
          by_cases hji : j = i
          · subst j
            simp [Std.HashMap.getD_eq_getD_getElem?, hget]
          · have hij : i ≠ j := fun hij => hji hij.symm
            simp [Std.HashMap.getD_eq_getD_getElem?,
              Std.HashMap.getElem?_insert, hij, hji]
    | none =>
        have hiNotMap : i ∉ b.labels := by
          intro hi
          have := (Std.HashMap.mem_iff_isSome_getElem?).mp hi
          simp [hget] at this
        have hi : i ∉ b.subjects.toList := by
          intro hiSubjects
          exact hiNotMap ((h.2 i).mpr hiSubjects)
        have hany := b.nodes_any h i
        have hcontains : b.labels.contains i = false := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hget]
          rfl
        have hfind := b.nodes_find_none i hi
        simp only [InitialLabelBuilder.add, addInitialLabelNode, hc,
          ↓reduceIte, hget, hfind]
        rw [hany, hcontains]
        simp only [Bool.false_eq_true, ↓reduceIte, InitialLabelBuilder.nodes,
          Array.toList_push, List.map_append]
        congr 1
        · apply List.map_congr_left
          intro j hj
          have hji : j ≠ i := fun hji => hi (hji ▸ hj)
          have hij : i ≠ j := fun hij => hji hij.symm
          simp [Std.HashMap.getD_eq_getD_getElem?,
            Std.HashMap.getElem?_insert, hij]
        · simp only [List.map_cons, List.map_nil]
          rw [Std.HashMap.getD_eq_getD_getElem?,
            Std.HashMap.getElem?_insert]
          simp
  · simp only [Bool.not_eq_true] at hc
    simp [InitialLabelBuilder.add, addInitialLabelNode, hc]

theorem InitialLabelBuilder.fold_nodes (entries : List InitialLabel)
    (b : InitialLabelBuilder) (h : b.WF) :
    (entries.foldl InitialLabelBuilder.add b).nodes =
      entries.foldl addInitialLabelNode b.nodes := by
  induction entries generalizing b with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      rw [ih (b.add entry) (b.add_wf entry h), b.add_nodes entry h]

def initialLabelNodesIndexed (entries : List InitialLabel) : List RNode :=
  (entries.foldl InitialLabelBuilder.add {}).nodes

theorem initialLabelNodesIndexed_eq_spec (entries : List InitialLabel) :
    initialLabelNodesIndexed entries = initialLabelNodesSpec entries := by
  exact InitialLabelBuilder.fold_nodes entries {} InitialLabelBuilder.empty_wf

def initialSubjectBuilder (g : Graph) : InitialLabelBuilder :=
  (g.map (fun t => t.s)).foldl InitialLabelBuilder.addSubject {}

def initialGraphNodesIndexed (g : Graph)
    (entries : List InitialLabel) : List RNode :=
  (entries.foldl InitialLabelBuilder.add (initialSubjectBuilder g)).nodes

theorem initialGraphNodesIndexed_eq_spec (g : Graph)
    (entries : List InitialLabel) :
    initialGraphNodesIndexed g entries =
      entries.foldl addInitialLabelNode
        ((g.map (fun t => t.s)).foldl ensureInitialSubjectNode []) := by
  have hB : (initialSubjectBuilder g).WF := by
    unfold initialSubjectBuilder
    exact InitialLabelBuilder.foldSubject_wf
      (g.map (fun t => t.s)) {} InitialLabelBuilder.empty_wf
  rw [initialGraphNodesIndexed,
    InitialLabelBuilder.fold_nodes entries (initialSubjectBuilder g) hB]
  apply congrArg (entries.foldl addInitialLabelNode)
  simpa [initialSubjectBuilder, InitialLabelBuilder.nodes] using
    (InitialLabelBuilder.foldSubject_nodes
      (g.map (fun t => t.s)) {} InitialLabelBuilder.empty_wf)

def initialLabelEntries (g : Graph) (us : List WfIri) (parseStore : Store) :
    List InitialLabel :=
  g.filterMap (fun t =>
    if t.p == rdfType then some (t.s, parseNnfWith us parseStore t.o)
    else none)

theorem fold_initialLabelEntries (g : Graph) (us : List WfIri)
    (parseStore : Store) (st : RState) :
    (initialLabelEntries g us parseStore).foldl (fun acc entry =>
      (addLabel acc entry.1 entry.2).1) st =
    g.foldl (fun acc t =>
      if t.p == rdfType then
        (addLabel acc t.s (parseNnfWith us parseStore t.o)).1
      else acc) st := by
  induction g generalizing st with
  | nil => simp [initialLabelEntries]
  | cons t g ih =>
      by_cases hp : t.p.val = rdfType.val
      · simp [initialLabelEntries, hp]
        simpa [initialLabelEntries] using
          ih ((addLabel st t.s (parseNnfWith us parseStore t.o)).1)
      · simp [initialLabelEntries, hp]
        simpa [initialLabelEntries] using ih st

def ensureInitialSubject (st : RState) (i : Subject) : RState :=
  { st with nodes := ensureInitialSubjectNode st.nodes i }

theorem fold_ensureInitialSubjects (g : Graph) (st : RState) :
    g.foldl (fun acc t => ensureInitialSubject acc t.s) st =
      { st with nodes :=
          (g.map (fun t => t.s)).foldl ensureInitialSubjectNode st.nodes } := by
  induction g generalizing st with
  | nil => rfl
  | cons t g ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      rfl

/-- The indexed initial nodes equal the exact subject-seeding and
    type-label folds used by `initState` when its starting state has no
    nodes or merges. -/
theorem indexedInitialState_eq_graphFold (g : Graph) (us : List WfIri)
    (parseStore : Store) (st : RState) (hNodes : st.nodes = [])
    (hIdent : st.ident = []) :
    { st with nodes :=
        initialGraphNodesIndexed g (initialLabelEntries g us parseStore) } =
      g.foldl (fun acc t =>
        if t.p == rdfType then
          (addLabel acc t.s (parseNnfWith us parseStore t.o)).1
        else acc)
        (g.foldl (fun acc t => ensureInitialSubject acc t.s) st) := by
  rw [initialGraphNodesIndexed_eq_spec]
  rw [fold_ensureInitialSubjects]
  rw [← fold_initialLabelEntries]
  rw [fold_addLabel_initial]
  · simp [hNodes]
  · exact hIdent

def initState (g : Graph) : RState :=
  let sp := collectPairs g rdfsSubPropertyOf
  let props := ((sp.map (·.1)) ++ (sp.map (·.2))).eraseDups
  let indexedStore := Store.ofIndex (Index.ofGraph g)
  let parseStore := indexedStore
  let us := unsatNamedClasses g
  let anonymousRanges := (indexedStore.withPred rdfsRange).filterMap (fun t =>
    match t.s, t.o with
    | .iri p, .bnode _ => some (p, parseNnfWith us parseStore t.o)
    | _, _ => none)
  let st0 : RState :=
    { inv := collectPairs g owlInverseOf,
      subprop := sp,
      ranges := collectPairs g rdfsRange,
      anonymousRanges := anonymousRanges,
      transProps := collectTypedIris g owlTransitiveProperty,
      funcProps := collectTypedIris g owlFunctionalProperty,
      subClosure := props.map (fun p => (p, subpropertiesOfRaw sp p)),
      supClosure := props.map (fun p => (p, superpropertiesOfRaw sp p)),
      store := indexedStore }
  let subjects := g.foldl (fun st t => ensureInitialSubject st t.s) st0
  let typed := g.foldl (fun st t =>
    if t.p == rdfType then
      (addLabel st t.s (parseNnfWith us parseStore t.o)).1
    else st) subjects
  seedNamedOneOfMembers typed

/-- Indexed initial-node implementation. All read-only state fields
    are constructed exactly as in `initState`; graph subjects and their
    type labels are grouped through `InitialLabelBuilder`. -/
def initStateIndexed (g : Graph) : RState :=
  let sp := collectPairs g rdfsSubPropertyOf
  let props := ((sp.map (·.1)) ++ (sp.map (·.2))).eraseDups
  let indexedStore := Store.ofIndex (Index.ofGraph g)
  let parseStore := indexedStore
  let us := unsatNamedClasses g
  let anonymousRanges := (indexedStore.withPred rdfsRange).filterMap (fun t =>
    match t.s, t.o with
    | .iri p, .bnode _ => some (p, parseNnfWith us parseStore t.o)
    | _, _ => none)
  let st0 : RState :=
    { inv := collectPairs g owlInverseOf,
      subprop := sp,
      ranges := collectPairs g rdfsRange,
      anonymousRanges := anonymousRanges,
      transProps := collectTypedIris g owlTransitiveProperty,
      funcProps := collectTypedIris g owlFunctionalProperty,
      subClosure := props.map (fun p => (p, subpropertiesOfRaw sp p)),
      supClosure := props.map (fun p => (p, superpropertiesOfRaw sp p)),
      store := indexedStore }
  let entries := initialLabelEntries g us parseStore
  let typed := { st0 with nodes := initialGraphNodesIndexed g entries }
  seedNamedOneOfMembers typed

theorem initStateIndexed_eq (g : Graph) :
    initStateIndexed g = initState g := by
  simp only [initStateIndexed, initState]
  let sp := collectPairs g rdfsSubPropertyOf
  let props := ((sp.map (·.1)) ++ (sp.map (·.2))).eraseDups
  let indexedStore := Store.ofIndex (Index.ofGraph g)
  let us := unsatNamedClasses g
  let anonymousRanges := (indexedStore.withPred rdfsRange).filterMap (fun t =>
    match t.s, t.o with
    | .iri p, .bnode _ => some (p, parseNnfWith us indexedStore t.o)
    | _, _ => none)
  let st0 : RState :=
    { inv := collectPairs g owlInverseOf,
      subprop := sp,
      ranges := collectPairs g rdfsRange,
      anonymousRanges := anonymousRanges,
      transProps := collectTypedIris g owlTransitiveProperty,
      funcProps := collectTypedIris g owlFunctionalProperty,
      subClosure := props.map (fun p => (p, subpropertiesOfRaw sp p)),
      supClosure := props.map (fun p => (p, superpropertiesOfRaw sp p)),
      store := indexedStore }
  change seedNamedOneOfMembers
      { st0 with nodes :=
          initialGraphNodesIndexed g (initialLabelEntries g us indexedStore) } =
    seedNamedOneOfMembers (g.foldl (fun st t =>
      if t.p == rdfType then
        (addLabel st t.s (parseNnfWith us indexedStore t.o)).1
      else st) (g.foldl (fun st t => ensureInitialSubject st t.s) st0))
  exact congrArg seedNamedOneOfMembers
    (indexedInitialState_eq_graphFold g us indexedStore st0 rfl rfl)

@[csimp] theorem initState_eq_indexed : @initState = @initStateIndexed := by
  funext g
  exact (initStateIndexed_eq g).symm

/-- The three-valued satisfiability verdict — the Lean counterpart of
    F* `Tableau_Refute.tableau_consistent`, meaning for meaning:

    * `some false` — provably inconsistent: an immediate graph-level
      violation, or a clash on every branch of the search;
    * `some true` — saturated and branched to quiescence with no
      clash. NOT a completeness guarantee (module header);
    * `none` — visit budget exhausted or an unresolved bounded witness
      obligation remained; indeterminate.

    The budget is the caller's and is threaded through the whole
    branch search (see `search`), so the number of visited search
    states is bounded by it. The cost of one visit depends on the
    graph, nodes, labels, and axioms and may be superlinear. Budget or
    witness-limit exhaustion is reported, never silently absorbed. -/
def tableauConsistent (g : Graph) (budget : Nat) : Option Bool :=
  if immediateInconsistency g then some false
  else
    let tb := collectAxioms g
    match (search tb g { initState g with tbox := tb } budget).1 with
    | .clash => some false
    | .open' => some true
    | .out   => none

/-- Is this graph provably UNSATISFIABLE?

    The refutation-only view of `tableauConsistent` (one search path —
    this is a projection, not a second procedure): `some false` means
    refuted, no model exists; `none` means not refuted, which covers
    "the visit budget ran out", "a bounded witness remains", and "the
    expansion went quiet without a clash". Callers that must not act
    on quiescence (the harness's
    inconsistency judges) consume this view; callers serving the wire
    contract's three-valued verdict use `tableauConsistent`. -/
def refute (g : Graph) (budget : Nat) : Option Bool :=
  match tableauConsistent g budget with
  | some false => some false
  | _          => none

/-- The two views agree on refutation: `refute` says `some false`
    exactly when `tableauConsistent` does. With `refute` defined as a
    projection the proof is case analysis on the shared verdict. -/
theorem refute_eq_false_iff (g : Graph) (budget : Nat) :
    refute g budget = some false ↔ tableauConsistent g budget = some false := by
  unfold refute
  cases h : tableauConsistent g budget with
  | none => simp
  | some b => cases b <;> simp

end L4Factoidal.OWL.Refute
