/-
L4Factoidal.OWL.Refute — the OWL DL REFUTATION calculus, wave 1.

Port of `formal/fstar/Tableau.Refute.fst` — step 3 of
https://github.com/danbri/factoidal/issues/548 . Where
`L4Factoidal/OWL/Materialise.lean` is positive-sound only (it writes
entailed memberships and never detects unsatisfiability), this module
answers the other question: does this graph have a model?

## Two answers, and the one that is missing on purpose

`refute` answers `Option Bool`:

* `some false` — REFUTED. A clash was derived on every branch, or a
  graph-level violation was found. The contract is that `some false`
  implies the graph has no model under OWL 2 Direct Semantics, and
  every rule that can contribute to one carries its model-theoretic
  argument beside it.
* `none` — not refuted. The budget ran out, or the expansion reached
  quiescence without a clash.

There is deliberately no `some true`. A saturated branch with no
clash is NOT a proof of consistency here: this calculus is
incomplete, wave 1 more so than the F* engine it ports (see "What is
NOT here"). The F* module does return `Some true` and then tells its
callers to treat it exactly like `None`; collapsing the two removes a
value that no caller may act on. A verdict a reader can misuse is a
defect, not a feature.

## What is NOT here, named

The F* module carries several more waves. Each ABSENCE only makes
refutation harder — the calculus derives fewer clashes, never wrong
ones — so wave 1 is sound with respect to the `some false` contract
while answering `none` where the F* engine answers `Some false`:

* the ≤-rule (merging witness successors) and named-individual
  identification;
* nominal (`owl:oneOf`) branching beyond the two size rules below;
* the counting oracle and the analytic min-sum counting clash;
* datatype facet and datatype-cardinality clashes;
* the disjoint-data-property pattern collision;
* DPLL-style branch-ordering heuristics.

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

def maxWitnessDepth : Nat := 3
def maxGeneratedWitnesses : Nat := 6

/-! ## Label bookkeeping -/

def memCe (c : ClassExpr) (ls : List ClassExpr) : Bool :=
  ls.any (fun l => ceEq c l)

def labelsOf (st : RState) (i : Subject) : List ClassExpr :=
  (st.nodes.filter (fun n => n.id == i)).flatMap (·.labels)

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
  let fromGraph := roles.flatMap (fun r => (st.store.withSubjPred i r).map (·.o))
  let viaInverse := roles.flatMap (fun r =>
    (inversesOf st.inv r).flatMap (fun r' =>
      (st.store.withPredObj r' i.toTerm).map (·.s.toTerm)))
  let fromExtra := st.extra.filterMap (fun e =>
    if e.s == i && roles.contains e.p && (!counted || e.counts) then some e.o
    else none)
  (fromGraph ++ viaInverse ++ fromExtra).eraseDups

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

/-- The indexed form, for the paths that run per label per round. -/
def differentFromIdx (st : RState) (a b : Term) : Bool :=
  (match termAsSubject a with
   | some sa => (st.store.withSubjPred sa owlDifferentFrom).any (fun t => t.o == b)
   | none    => false)
  || (match termAsSubject b with
      | some sb => (st.store.withSubjPred sb owlDifferentFrom).any (fun t => t.o == a)
      | none    => false)

/-- Datatypes whose LEXICAL FORM is its own value, so two different
    spellings are two different values.

    Only `xsd:string` qualifies here. The first version of this rule
    said "same datatype, different lexical form" for EVERY datatype,
    and that is false almost everywhere: `"1"` and `"01"` are one
    `xsd:integer`, `"1.0"` and `"1.00"` one `xsd:decimal`, and two
    `rdf:XMLLiteral`s differing only in insignificant whitespace are
    one value — which is exactly what
    `WebOnt-miscellaneous-202` asserts, a CONSISTENT premise the rule
    refuted by declaring a functional property's two spellings of one
    XML literal distinct. A refuter that reads a spelling difference
    as a value difference invents contradictions out of formatting. -/
def lexicalIsValue (dt : WfIri) : Bool := dt == xsdString

def provablyDistinct (g : Graph) (a b : Term) : Bool :=
  if a == b then false
  else match a, b with
    | .literal x, .literal y =>
        (x.val.datatype == y.val.datatype && lexicalIsValue x.val.datatype &&
         x.val.lexicalForm != y.val.lexicalForm)
        || differentFromAsserted g a b
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

def datatypeRangeClash (st : RState) (ls : List ClassExpr) : Bool :=
  (collectDtProperties ls).any (fun p =>
    existsUnsatisfiableWitness p ls (universalForProperty st p ls .unconstrained))

def collectCardProps (ls : List ClassExpr) : List (Nat × WfIri) :=
  ls.filterMap (fun l => match l with
    | .minCard k p   => some (k, p)
    | .exactCard k p => some (k, p)
    | _              => none)

def datatypeCardinalityClash (st : RState) (ls : List ClassExpr) : Bool :=
  (collectCardProps ls).any (fun (k, p) =>
    k ≥ 1 &&
    (let u := valueSetIntersect
                (universalForProperty st p ls .unconstrained)
                (rangeValueSet st st.ranges p .unconstrained)
     match valueSetMaxSize u with
     | some m => k > m
     | none   => false))

def clashNodes (g : Graph) (st : RState) : Bool :=
  st.nodes.any (fun n =>
    let ls := labelsOf st n.id
    ls.any (clashForLabel g st n.id ls)
    || datatypeRangeClash st ls
    || datatypeCardinalityClash st ls)

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

def immediateInconsistency (g : Graph) : Bool :=
  allDifferentViolation g || bottomPropertyAssertion g ||
  selfDisjointPropertyInUse g ||
  nilStructureViolation g || hasSelfDisjointViolation g

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

/-- Normalise BETWEEN parse and NNF, so the NNF negation of a
    normalised bottom simplifies (`nnfNeg owl:Nothing = owl:Thing`)
    and the two spellings of a complement pair converge. Normalising
    AFTER the NNF would leave `∃q.¬first:Nothing` beside
    `∃q.owl:Thing` — one extension, two expressions, no match. -/
def parseNnfWith (us : List WfIri) (st : Store) (t : Term) : ClassExpr :=
  nnf (normalizeUnsat us (parseClassExpr st t 32))

def parseNnfSubjectWith (us : List WfIri) (st : Store) (sub : Subject) : ClassExpr :=
  nnf (normalizeUnsat us (parseCeOfSubject st sub))

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
  let have' := (successorsOf g st i p false).length
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
  tb.foldl (fun (acc : RState × Bool) (a, d) =>
    if !(memCe a (labelsOf acc.1 i)) && edgeEntailsMembership g acc.1 i a then
      let (s1, c1) := addLabel acc.1 i a
      let (s2, c2) := addLabel s1 i d
      (s2, acc.2 || c1 || c2)
    else acc) (st, false)

/-- Fire an axiom whose left-hand side is an INTERSECTION when every
    conjunct is present as a SEPARATE label.

    `applyAxioms` matches one stored label against a whole left-hand
    side, so `z ≡ C₁ ⊓ C₂` never fires on a node carrying `C₁` and
    `C₂` apart. Labels are entailed memberships, and being in each
    `Cᵢ` IS being in the intersection, so the node is entailed in the
    left-hand side and hence in the right-hand side. -/
def applyAxiomsConj (tb : List (ClassExpr × ClassExpr)) (st : RState) (i : Subject)
    : RState × Bool :=
  tb.foldl (fun (acc : RState × Bool) (a, d) =>
    match a with
    | .intersection cs =>
        if cs.isEmpty || memCe a (labelsOf acc.1 i) then acc
        else if cs.all (fun c => memCe c (labelsOf acc.1 i)) then
          let (s1, c1) := addLabel acc.1 i a
          let (s2, c2) := addLabel s1 i d
          (s2, acc.2 || c1 || c2)
        else acc
    | _ => acc) (st, false)

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

partial def search (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    (fuel : Nat) : Verdict :=
  match fuel with
  | 0     => .out
  | n + 1 =>
    if clashNodes g st then .clash
    else
      let (st', changed) := onePass tb g st
      if changed then search tb g st' n
      else if clashNodes g st' then .clash
      else
        match pendingUnion st' with
        | none          => .open'
        | some (i, cs)  =>
          -- Every disjunct must close for the union to refute the
          -- node. One branch out of fuel makes the whole answer
          -- indeterminate: it might have stayed open.
          let rec tryAll : List ClassExpr → Verdict
            | []      => .clash
            | c :: tl =>
                let (sb, _) := addLabel { st' with
                  nodes := st'.nodes.map (fun m =>
                    if m.id == i then
                      { m with labels := m.labels.filter (fun l =>
                          match l with
                          | .union ds => !(ClassExpr.beqList ds cs)
                          | _         => true) }
                    else m) } i c
                match search tb g sb n with
                | .clash => tryAll tl
                | .open' => .open'
                | .out   => .out
          tryAll cs

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

/-- Is this graph provably UNSATISFIABLE?

    `some false` means refuted — no model exists. `none` means not
    refuted, which covers both "the budget ran out" and "the
    expansion went quiet without a clash". There is no `some true`:
    see the module header. -/
def refute (g : Graph) (fuel : Nat) : Option Bool :=
  if immediateInconsistency g then some false
  else
    match search (collectAxioms g) g (initState g) fuel with
    | .clash => some false
    | _      => none

end L4Factoidal.OWL.Refute
