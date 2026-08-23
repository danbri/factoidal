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

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Vocabulary this module needs and `OWL/Vocabulary.lean` does not
carry -/

def owlAllDifferent : WfIri := ⟨"http://www.w3.org/2002/07/owl#AllDifferent", rfl⟩
def owlDistinctMembers : WfIri :=
  ⟨"http://www.w3.org/2002/07/owl#distinctMembers", rfl⟩
def owlHasSelf : WfIri := ⟨"http://www.w3.org/2002/07/owl#hasSelf", rfl⟩

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

def maxWitnessDepth : Nat := 3
def maxGeneratedWitnesses : Nat := 6

/-! ## Label bookkeeping -/

def memCe (c : ClassExpr) (ls : List ClassExpr) : Bool :=
  ls.any (fun l => ClassExpr.beq c l)

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
partial def subpropertiesOf (sp : List (WfIri × WfIri)) (p : WfIri) : List WfIri :=
  let rec go (acc : List WfIri) (fuel : Nat) : List WfIri :=
    match fuel with
    | 0     => acc
    | n + 1 =>
      let more := sp.filterMap (fun (a, b) =>
        if acc.contains b && !(acc.contains a) then some a else none)
      if more.isEmpty then acc else go (acc ++ more.eraseDups) n
  go [p] (sp.length + 1)

/-- The `p`-successors of `i`: the graph's `q`-edges for every
    `q ⊑* p`, the inverse direction of each, and the expansion's own
    edges. `counted` restricts the result to what a cardinality bound
    may be measured against. -/
def successorsOf (g : Graph) (st : RState) (i : Subject) (p : WfIri)
    (counted : Bool) : List Term :=
  let roles := subpropertiesOf st.subprop p
  let fromGraph := g.filterMap (fun t =>
    if t.s == i && roles.contains t.p then some t.o else none)
  let viaInverse := roles.flatMap (fun r =>
    (inversesOf st.inv r).flatMap (fun r' =>
      g.filterMap (fun t =>
        if t.p == r' && t.o == i.toTerm then some t.s.toTerm else none)))
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

def provablyDistinct (g : Graph) (a b : Term) : Bool :=
  if a == b then false
  else match a, b with
    | .literal x, .literal y =>
        x.val.datatype == y.val.datatype && x.val.lexicalForm != y.val.lexicalForm
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
  | .minCard k p        => k ≥ 1 && existsMaxLt k p lsAll
  | .someOf p c         => existsMaxLt 1 p lsAll || existsMaxQualLt 1 p c lsAll
  | .hasValue p _       => existsMaxLt 1 p lsAll
  | .minQualCard k p c  =>
      k ≥ 1 &&
      (existsMaxLt k p lsAll || existsMaxQualLt k p c lsAll ||
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

def clashNodes (g : Graph) (st : RState) : Bool :=
  st.nodes.any (fun n =>
    let ls := labelsOf st n.id
    ls.any (clashForLabel g st n.id ls))

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

def immediateInconsistency (g : Graph) : Bool :=
  allDifferentViolation g || selfDisjointPropertyInUse g ||
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

def parseNnf (st : Store) (t : Term) : ClassExpr := nnf (parseClassExpr st t 32)

def parseNnfSubject (st : Store) (s : Subject) : ClassExpr :=
  nnf (parseCeOfSubject st s)

def collectAxioms (g : Graph) : List (ClassExpr × ClassExpr) :=
  let st := Store.ofGraph g
  g.flatMap (fun t =>
    if t.p == rdfsSubClassOf then [(parseNnfSubject st t.s, parseNnf st t.o)]
    else if t.p == owlEquivalentClass then
      let a := parseNnfSubject st t.s
      let b := parseNnf st t.o
      [(a, b), (b, a), (nnfNeg b, nnfNeg a), (nnfNeg a, nnfNeg b)]
    else if t.p == owlDisjointWith || t.p == owlComplementOf then
      let a := parseNnfSubject st t.s
      let b := parseNnf st t.o
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
      let transRoles := (subpropertiesOf st.subprop p).filter (roleIsTransitive st)
      transRoles.foldl (fun (acc : RState × Bool) r =>
        (successorsOf g acc.1 i r false).foldl (fun (a2 : RState × Bool) y =>
          match termAsSubject y with
          | none   => a2
          | some j => let (s, ch) := addLabel a2.1 j (.allOf r c)
                      (s, a2.2 || ch)) acc) base
  | .someOf p c        => ensureWitnesses g st i p 1 c
  | .minQualCard k p c => ensureWitnesses g st i p k c
  | .minCard k p       => ensureWitnesses g st i p k .unknown
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
    if ClassExpr.beq a l then
      let (s, ch) := addLabel acc.1 i d
      (s, acc.2 || ch)
    else acc) (st, false)

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
    (labelsOf acc.1 n.id).foldl (fun (a2 : RState × Bool) l =>
      let (s1, c1) := applyLabelRules g a2.1 n.id l
      let (s2, c2) := applyAxioms tb s1 n.id l
      (s2, a2.2 || c1 || c2)) acc) (st1, ch1)

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
  let st0 : RState :=
    { inv := collectPairs g owlInverseOf,
      subprop := collectPairs g rdfsSubPropertyOf,
      transProps := collectTypedIris g owlTransitiveProperty,
      funcProps := collectTypedIris g owlFunctionalProperty }
  let store := Store.ofGraph g
  g.foldl (fun st t =>
    if t.p == rdfType then (addLabel st t.s (parseNnf store t.o)).1 else st) st0

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
