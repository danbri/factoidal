/-
L4Factoidal.OWL.Refute — the OWL DL REFUTATION calculus, wave 1.

Port of `formal/fstar/Tableau.Refute.fst` — step 3 of
https://github.com/danbri/factoidal/issues/548 . Where
`L4Factoidal/OWL/Materialise.lean` is positive-sound only (it writes
entailed memberships and never detects unsatisfiability), this module
answers the other question: does this graph have a model?

## The verdicts (three-valued since 2026-08-25, issue 586)

`tableauConsistent` answers `Option Bool`, with the SAME meanings as
the F* `Tableau_Refute.tableau_consistent` verdict it mirrors:

* `some false` — REFUTED. A clash was derived on every branch, or a
  graph-level violation was found. The contract is that `some false`
  implies the graph has no model under OWL 2 Direct Semantics, and
  every rule that can contribute to one carries its model-theoretic
  argument beside it. This is the only verdict wired into suite
  scoring.
* `some true` — the expansion saturated and every branch point was
  explored to quiescence with no clash: the search state IS a
  candidate model. NOT a completeness guarantee — the calculus
  derives fewer consequences than OWL 2 DL, so an unsatisfiable
  graph outside its reach also answers `some true`. Callers may
  report it (the wire contract's `consistent: true`) but must not
  score "consistent" on it beyond what they already do by default.
* `none` — the budget ran out before the answer was determined.
  Indeterminate, never to be collapsed into either Boolean.

`refute` is the refutation-only VIEW of the same search (defined
through `tableauConsistent`; one search path, no duplicate
dispatch): `some false` = refuted, `none` = not refuted, quiescence
and budget-out deliberately indistinguishable. The harness's
inconsistency judges consume this view.

An earlier revision of this header argued for withholding
`some true` entirely. The wire contract decided otherwise
(`owlIsConsistent` must report `consistent: true|false|null`,
matching `bin/npm-entry/entry_jsoo.ml`), and the misuse the argument
feared is prevented by contract instead: the `some true` doc above
and the F* original both pin what it does NOT mean.

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

The procedural fragment is WIDER (nominal size rules, the datatype
value-space clashes C5/C6, the graph-level violations G1–G9, TBox
unfolding via `collectAxioms`, inverse roles) and, inside the shared
fragment, weaker only through its caps (witness depth ≤ 3, ≤ 6
generated witnesses, the threaded budget) — caps withhold
refutations, never invent them. `RefuteTests.lean` keeps an
instance-level paired witness: one input refuted here by `#guard`
and refuted in the calculus by an explicit `Refuted` derivation. The
general linkage — an abstraction from a clash trace to a serialisable
`Refuted` derivation, `refute g b = some false → Refuted R A` on the
shared fragment — is the certificate-checker rung
`OWL/Tableau.lean`'s header names; tracked as follow-up 6 on
https://github.com/danbri/factoidal/issues/586 .

## What is NOT here, named

The F* module carries several more waves. Each ABSENCE only makes
refutation harder — the calculus derives fewer clashes, never wrong
ones — so this port is sound with respect to the `some false`
contract while answering `none`/`some true` where the F* engine
answers `Some false`:

* named-individual identification (the ≤-rule below merges WITNESS
  blank nodes only);
* nominal (`owl:oneOf`) branching beyond the two size rules below;
* the counting oracle and the analytic min-sum counting clash
  (`OWL/CountingOracle.lean` exists, with a proved Farkas validator,
  but is not yet consulted from this search);
* the disjoint-data-property pattern collision;
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
      growing an infinite `∃`-chain. Refusing a witness only
      withholds labels. -/
  wdepth     : List (BNodeId × Nat) := []
  inv        : List (WfIri × WfIri) := []
  subprop    : List (WfIri × WfIri) := []
  transProps : List WfIri := []
  funcProps  : List WfIri := []
  /-- Declared `rdfs:range` pairs. A range confines a property's
      fillers to a datatype, which is what lets the value-space rules
      bound them. -/
  ranges     : List (WfIri × WfIri) := []
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
    edges. `counted` restricts the result to what a cardinality bound
    may be measured against. -/
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
                   | .maxQualCard k' p' c' => p' == p && k' < k && ClassExpr.beq c c'
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
      !ms.isEmpty && ms.all (provablyDistinct g i.toTerm ·)
  | .maxCard k p =>
      let succs := successorsOf g st i p true
      if k == 0 then !succs.isEmpty else existsDistinctSubset g succs (k + 1)
  | .maxQualCard k p c =>
      let succs := successorsInFiller st c (successorsOf g st i p true)
      if k == 0 then !succs.isEmpty else existsDistinctSubset g succs (k + 1)
  | _ => false

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

def collectDtProperties (ls : List ClassExpr) : List WfIri :=
  ls.filterMap (fun l => match l with
    | .someOf p _   => some p
    | .allOf p _    => some p
    | .hasValue p _ => some p
    | _             => none)

/-- Is some existence obligation on `p` unsatisfiable against the
    shared `∀`-intersection? Each obligation is checked ALONE against
    that intersection, never against another obligation. -/
def existsUnsatisfiableWitness (p : WfIri) (ls : List ClassExpr) (universal : ValueSet)
    : Bool :=
  ls.any (fun l => match l with
    | .someOf q d =>
        q == p && valueSetIsEmpty (foldDatatypeConstraint universal d)
    | .hasValue q v =>
        q == p && (match v with
                   | .literal _ => valueSetIsEmpty
                                     (valueSetIntersect universal (.enum [v]))
                   | _          => false)
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
                    (rangeValueSet st st.ranges p .unconstrained)

def datatypeRangeClash (st : RState) (ls : List ClassExpr) : Bool :=
  (collectDtProperties ls).any (fun p =>
    existsUnsatisfiableWitness p ls (fillerValueSet st p ls))

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

def clashNodes (g : Graph) (st : RState) : Bool :=
  st.nodes.any (fun n =>
    let ls := labelsOf st n.id
    ls.any (clashForLabel g st n.id ls)
    || datatypeRangeClash st ls
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

def unsatNamedClasses (g : Graph) : List WfIri :=
  let st := Store.ofGraph g
  let fillers := (g.filterMap (fun t =>
    if t.p == owlAllValuesFrom then
      match t.o with
      | .iri c => some c
      | _      => none
    else none)).eraseDups
  fillers.filter (fun c => cesMinMaxClash (superclassCes st c))

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

def parseNnfSubjectWith (us : List WfIri) (st : Store) (sub : Subject) : ClassExpr :=
  if isScaffoldBNode sub.toTerm then .unknown
  else nnf (normalizeUnsat us (parseCeOfSubject st sub))

def parseNnf (st : Store) (t : Term) : ClassExpr := nnf (parseClassExpr st t 32)

def parseNnfSubject (st : Store) (s : Subject) : ClassExpr :=
  nnf (parseCeOfSubject st s)

def collectAxioms (g : Graph) : List (ClassExpr × ClassExpr) :=
  let st := Store.ofGraph g
  let us := unsatNamedClasses g
  g.flatMap (fun t =>
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

/-! ## Expansion -/

def witnessId (i : Subject) (p : WfIri) (n : Nat) : BNodeId :=
  let iStr := match i with
    | .iri s   => s.val
    | .bnode b => b
  "_:tw_" ++ iStr ++ "__" ++ p.val ++ "__" ++ toString n

def depthOf (st : RState) (i : Subject) : Nat :=
  match i with
  | .iri _   => 0
  | .bnode b => (st.wdepth.find? (fun q => q.1 == b)).map (·.2) |>.getD 0

/-- Mint witnesses for `i` on `p` until it has `k` successors, up to
    the depth and count caps. The filler is put on each witness. -/
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
      let b := witnessId i p (s0.fresh + j)
      if s0.extra.any (fun e => e.o == Term.bnode b) then (s0, ch)
      else
        let s1 := { s0 with
          extra := s0.extra ++ [{ s := i, p := p, o := .bnode b, counts := false }],
          wdepth := s0.wdepth ++ [(b, d)] }
        let (s2, _) := addLabel s1 (.bnode b) c
        (s2, true)) (st, false)
    |> (fun (s, ch) => ({ s with fresh := s.fresh + want }, ch))

/-- The deterministic rules of one label. `union` is left alone — it
    is the branching rule and belongs to the search. -/
def applyLabelRules (g : Graph) (st : RState) (i : Subject) (l : ClassExpr)
    : RState × Bool :=
  match l with
  | .intersection cs =>
      cs.foldl (fun (acc : RState × Bool) c =>
        let (s, ch) := addLabel acc.1 i c
        (s, acc.2 || ch)) (st, false)
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
  | .someOf p c        => if isBottomProp p then (st, false)
                          else ensureWitnesses g st i p 1 c
  | .minQualCard k p c => if isBottomProp p then (st, false)
                          else ensureWitnesses g st i p k c
  | .minCard k p       => if isBottomProp p then (st, false)
                          else ensureWitnesses g st i p k .unknown
  | .hasValue p v =>
      -- A `hasValue` edge holds in EVERY model, so it is COUNTED
      -- against cardinality bounds, unlike a witness.
      if st.extra.any (fun e => e.s == i && e.p == p && e.o == v) then (st, false)
      else ({ st with extra := st.extra ++ [{ s := i, p := p, o := v, counts := true }] },
            true)
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

/-- Fire the axioms whose left-hand side the node's EDGES prove. The
    left-hand side is added as a label too, so the label-level clash
    rules see it. -/
def applyAxiomsEdges (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    (i : Subject) : RState × Bool :=
  -- The node's label read is HOISTED and refreshed only when an axiom
  -- actually fires — the sole way the labels change in this loop.
  -- Reading them per AXIOM costs one node-list walk per axiom per
  -- node per round.
  let (st', ch, _) := tb.foldl (fun (acc : RState × Bool × List ClassExpr) (a, d) =>
    let (s0, c0, ls) := acc
    if !(memCe a ls) && edgeEntailsMembership g s0 i a then
      let (s1, c1) := addLabel s0 i a
      let (s2, c2) := addLabel s1 i d
      (s2, c0 || c1 || c2, labelsOf s2 i)
    else acc) (st, false, labelsOf st i)
  (st', ch)

/-- Fire an axiom whose left-hand side is an INTERSECTION when every
    conjunct is present as a SEPARATE label.

    `applyAxioms` matches one stored label against a whole left-hand
    side, so `z ≡ C₁ ⊓ C₂` never fires on a node carrying `C₁` and
    `C₂` apart. Labels are entailed memberships, and being in each
    `Cᵢ` IS being in the intersection, so the node is entailed in the
    left-hand side and hence in the right-hand side. -/
def applyAxiomsConj (tb : List (ClassExpr × ClassExpr)) (st : RState) (i : Subject)
    : RState × Bool :=
  let (st', ch, _) := tb.foldl (fun (acc : RState × Bool × List ClassExpr) (a, d) =>
    let (s0, c0, ls) := acc
    match a with
    | .intersection cs =>
        if cs.isEmpty || memCe a ls then acc
        else if cs.all (fun c => memCe c ls) then
          let (s1, c1) := addLabel s0 i a
          let (s2, c2) := addLabel s1 i d
          (s2, c0 || c1 || c2, labelsOf s2 i)
        else acc
    | _ => acc) (st, false, labelsOf st i)
  (st', ch)

/-- `owl:FunctionalProperty p` is a global `≤ 1 p` on every node,
    which folds the functionality constraint into the existing
    max-cardinality clash rule with no new machinery. -/
def injectFunctional (st : RState) : RState × Bool :=
  st.nodes.foldl (fun (acc : RState × Bool) n =>
    st.funcProps.foldl (fun (a2 : RState × Bool) p =>
      let (s, ch) := addLabel a2.1 n.id (.maxCard 1 p)
      (s, a2.2 || ch)) acc) (st, false)

/-- One saturation pass over every node and every label it carries. -/
def onePass (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    : RState × Bool :=
  let (st1, ch1) := injectFunctional st
  st1.nodes.foldl (fun (acc : RState × Bool) n =>
    let byLabel := (labelsOf acc.1 n.id).foldl (fun (a2 : RState × Bool) l =>
      let (s1, c1) := applyLabelRules g a2.1 n.id l
      let (s2, c2) := applyAxioms tb s1 n.id l
      (s2, a2.2 || c1 || c2)) acc
    let (s3, c3) := applyAxiomsEdges tb g byLabel.1 n.id
    let (s4, c4) := applyAxiomsConj tb s3 n.id
    (s4, byLabel.2 || c3 || c4)) (st1, ch1)

/-! ## The ≤-rule: merging witness successors

`clashForLabel`'s `maxCard` case fires only on PROVABLY DISTINCT
successors, and it never counts witnesses. So a node with more
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

**Why only witnesses may be merged.** A witness blank node never
appears in the input graph, so every edge that could mention it
lives in `extra` and can be COMPLETELY redirected. A named
individual's graph-asserted edges cannot be rewritten this way, so
merging one in would leave a half-merged state — and a clash read
off a half-merged state is fabricated. Excluding named individuals
withholds refutations; including them would invent them.

A pair already forced apart is never offered: merging a provably
distinct pair is unsound, not merely unhelpful. -/

/-- A blank node stands for an EXISTENTIAL witness rather than for a
    named individual — whether this module minted it (`_:tw_`), the
    materialisation pass minted it (`_:bw_`), or the document carries
    it. All three are existentially quantified, so identifying two of
    them is a choice a model may make.

    A NAMED individual is excluded. Merging one is a further wave;
    withholding it loses refutations, which is the safe direction. -/
def isMergeableTerm : Term → Bool
  | .bnode _ => true
  | _        => false

private def witnessPairs (g : Graph) (succs : List Term) (k : Nat)
    : List (Term × Term) :=
  if succs.length ≤ k then []
  else
    let ws := succs.filter isMergeableTerm
    ws.flatMap (fun a =>
      ws.filterMap (fun b =>
        if a != b && !(provablyDistinct g a b) then some (a, b) else none))

/-- The witness pairs a `≤ k p` label could be forced to identify. -/
def mergePairsForLabel (g : Graph) (st : RState) (i : Subject) (l : ClassExpr)
    : List (Term × Term) :=
  match l with
  | .maxCard k p       => witnessPairs g (successorsOf g st i p false) k
  | .maxQualCard k p _ => witnessPairs g (successorsOf g st i p false) k
  | _                  => []

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
    (labelsOf st n.id).findSome? (fun l =>
      match l with
      | .union cs =>
          if cs.any (fun c => memCe c (labelsOf st n.id)) then none
          else some (n.id, cs)
      | _ => none)))

/-- The search, with the budget THREADED through the branches rather
    than handed to each in full.

    A per-branch budget lets a node with `d` choices grow a tree of
    `d^budget` states: siblings each get the whole allowance and the
    total is the product. A threaded budget makes them draw from ONE
    pool, so the search costs what the pool says and no more. Running
    out answers `out`, which the caller reads as "not refuted" — the
    same withholding as every other cap here.

    Returns the verdict and what is left. -/
partial def search (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    (budget : Nat) : Verdict × Nat :=
  match budget with
  | 0     => (.out, 0)
  | n + 1 =>
    if clashNodes g st then (.clash, n)
    else
      let (st', changed) := onePass tb g st
      if changed then search tb g st' n
      else if clashNodes g st' then (.clash, n)
      else
        match pendingUnion st' with
        | some (i, cs) =>
          -- EVERY disjunct must close for the union to refute the
          -- node. One branch out of budget makes the whole answer
          -- indeterminate: it might have stayed open.
          let rec tryAll (ds : List ClassExpr) (b : Nat) : Verdict × Nat :=
            match ds with
            | []      => (.clash, b)
            | c :: tl =>
                let (sb, _) := addLabel { st' with
                  nodes := st'.nodes.map (fun m =>
                    if m.id == i then
                      { m with labels := m.labels.filter (fun l =>
                          match l with
                          | .union es => !(ClassExpr.beqList es cs)
                          | _         => true) }
                    else m) } i c
                match search tb g sb b with
                | (.clash, b') => tryAll tl b'
                | (.open', b') => (.open', b')
                | (.out, b')   => (.out, b')
          tryAll cs n
        | none =>
          -- No union left. The ≤-rule may still force a choice, and
          -- every mergeable pair must close.
          match pendingMerge g st' with
          | none       => (.open', n)
          | some pairs =>
            let rec tryMerges (ps : List (Term × Term)) (b : Nat) : Verdict × Nat :=
              match ps with
              | []           => (.clash, b)
              | (x, y) :: tl =>
                  match search tb g (mergeInto st' x y) b with
                  | (.clash, b') => tryMerges tl b'
                  | (.open', b') => (.open', b')
                  | (.out, b')   => (.out, b')
            tryMerges pairs n

/-! ## The entry point -/

def initState (g : Graph) : RState :=
  let sp := collectPairs g rdfsSubPropertyOf
  let props := ((sp.map (·.1)) ++ (sp.map (·.2))).eraseDups
  let st0 : RState :=
    { inv := collectPairs g owlInverseOf,
      subprop := sp,
      ranges := collectPairs g rdfsRange,
      transProps := collectTypedIris g owlTransitiveProperty,
      funcProps := collectTypedIris g owlFunctionalProperty,
      subClosure := props.map (fun p => (p, subpropertiesOfRaw sp p)),
      supClosure := props.map (fun p => (p, superpropertiesOfRaw sp p)),
      store := Store.ofIndex (Index.ofGraph g) }
  let store := Store.ofGraph g
  let us := unsatNamedClasses g
  g.foldl (fun st t =>
    if t.p == rdfType then (addLabel st t.s (parseNnfWith us store t.o)).1 else st) st0

/-- The three-valued satisfiability verdict — the Lean counterpart of
    F* `Tableau_Refute.tableau_consistent`, meaning for meaning:

    * `some false` — provably inconsistent: an immediate graph-level
      violation, or a clash on every branch of the search;
    * `some true` — saturated and branched to quiescence with no
      clash. NOT a completeness guarantee (module header);
    * `none` — budget exhausted, indeterminate.

    The budget is the caller's: it is threaded through the whole
    branch search (see `search`), so cost is close to linear in it
    and running out is reported, never silently absorbed. -/
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
    both "the budget ran out" and "the expansion went quiet without a
    clash". Callers that must not act on quiescence (the harness's
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
