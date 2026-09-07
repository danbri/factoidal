/-
L4Factoidal.OWL.Comprehension — the PositiveEntailmentTest-only
comprehension and existential-witness layer.

## Why this is a layer and not more closure rows

`OWL/RLClosure.lean` computes the OWL 2 RL/RDF closure: a fixpoint of
Horn-shaped rows over the premise. The rules in THIS file are not of
that shape. Each one mints a blank node standing for a resource the
OWL 2 RDF-Based Semantics guarantees to exist — a class expression, a
list spine, a property successor — rather than deriving a fact about
resources the premise already names. Two consequences follow, and both
are structural, not stylistic.

1. **They cannot join the fixpoint.** Every witness is itself a fresh
   `rdf:type` / property fact that the closure's own rows can chain
   off, and the chaining is unbounded in the fuel budget. The F\* tree
   measured what happens: folding the same layer into
   `owl_rl_closure_with_reflexivity` took the DL-regime
   `type-inconsistency.rdf` catalog from 124 pass, 3 fail to 63 pass,
   64 fail (`formal/fstar/OWL.Closure.fsti` § 20b banner, 2026-07-27) —
   the tableau refuter reads the same RL closure, and its budget went
   into the witnesses instead of into the clash. This file is applied
   ONCE, over the already-stable closure, by `judgePositive` alone.
2. **Their soundness statement is different.** A closure row's
   conclusion is TRUE in every model of the premise under an unchanged
   blank-node assignment. A comprehension row's conclusion is true only
   under an assignment EXTENDED at the witness labels, by the resource
   the semantics provides. That is exactly what a blank node in a
   conclusion graph asks for (RDF 1.1 Semantics § 5.1: `G ⊨ E` iff some
   mapping of `E`'s blank nodes into the model satisfies it), so the
   layer is sound for the conformance question the corpus asks — and it
   is NOT the RL consequence relation. `Comprehends` below is a
   separate inductive from `RLRules.Derives` for that reason, the same
   reason `RLRules.ExtClash` is separate from `RLRules.Clash`.

## The rows

Comprehension conditions: OWL 2 RDF-Based Semantics (W3C Rec.
2012-12-11) § 8 "Comprehension Conditions" — § 8.1 sequences, § 8.2
Boolean connectives, § 8.4 restrictions. Those conditions are
informative in OWL 2 (as iff-conditions they force infinite structure
into every interpretation); the rows here take FINITE,
premise-anchored IF-instances of them, which is the ter Horst pD\*
design (Journal of Web Semantics 3(2-3), 2005) the RL profile already
follows.

| row | driven by | emits | § |
|---|---|---|---|
| `comp-uni1` | `C rdf:type owl:Class`, `C` named | the singleton union class `UnionOf(C)` and its one-cell spine | 8.1, 8.2 |
| `comp-trp-chain` | `P rdf:type owl:TransitiveProperty` | `P owl:propertyChainAxiom (P P)` and its two-cell spine | 8.1 |
| `comp-adf-clique` | a set of individuals pairwise `owl:differentFrom` in the closure | one `owl:AllDifferent` node over the set | 8.1 |
| `svf-thing-mat` | any data edge `x P y` | the restriction `SomeValuesFrom(P, owl:Thing)` and `x`'s membership in it | 8.4 |
| `svf-thing-wit` | `x rdf:type ?r`, `?r owl:someValuesFrom owl:Thing`, `?r owl:onProperty P` | a successor edge `x P _:w` | — |
| `hasself-synth` | a self-loop `x P x` | the restriction `HasSelf(P)` and `x`'s membership in it | 8.4 |

`svf-thing-wit` needs no comprehension condition: `owl:someValuesFrom
owl:Thing` membership IS the assertion that a successor exists
(RDF-Based Semantics § 5.4), so the witness is the existential the
premise already carries. It is listed here because it mints a blank
node and therefore shares this file's assignment-extension discipline.

## Termination

Every row reads `base` and `base` only, and writes into a separate
accumulation. No row reads another row's output, and the layer is
applied once. So the synthesis cannot feed itself; it terminates
structurally, not by a fuel bound. Do not change a row to read the
accumulation — that turns bounded comprehension into the unbounded kind
(a witness for every class expression, including witness-built ones),
which does not terminate.

Blank-node labels are deterministic functions of their anchors, so
re-running a row re-derives the same labels rather than minting fresh
structure.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RLClosure

namespace L4Factoidal.OWL.Comp

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Reserved vocabulary guards

A comprehension row must not read a VOCABULARY triple as a data edge.
The F\* engine's `is_schema_metapredicate` enumerates the predicates to
skip; this port tests the namespace instead, which is a SUPERSET of
that enumeration and therefore only makes the rows fire less. Firing
less is sound (the layer only adds triples), so the coarser test costs
nothing but recall on vocabulary the corpus does not use as data. -/

def owlNs : String := "http://www.w3.org/2002/07/owl#"
def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def rdfsNs : String := "http://www.w3.org/2000/01/rdf-schema#"

/-- An IRI in the RDF, RDFS or OWL vocabulary namespace. -/
def isVocabIri (i : WfIri) : Bool :=
  i.val.startsWith owlNs || i.val.startsWith rdfNs || i.val.startsWith rdfsNs

/-- The label prefix every blank node this engine mints carries
(`RLRules`' `__rl_comp__` / `__rl_minc1__` and this file's rows). -/
def isEngineBnode (b : BNodeId) : Bool := b.startsWith "__rl_"

/-- A subject a data-edge row may read: a non-vocabulary IRI, or a
blank node this engine did not mint. -/
def edgeSubjectIsSafe (s : Subject) : Bool :=
  match s with
  | .iri i => !isVocabIri i
  | .bnode b => !isEngineBnode b

/-- A predicate a data-edge row may read: not `rdf:type`, and not
vocabulary. -/
def isDataPredicate (p : WfIri) : Bool := !isVocabIri p

/-! ## Shared list-spine synthesis (§ 8.1)

Cell labels are deterministic in `(pre, element key)`, so a repeat
application rebuilds the same spine. Callers must pass DEDUPLICATED
elements: a repeated element reuses its cell label and would fold two
list positions into one. Every cell is typed `rdf:List` — the WebOnt
conclusion documents author that triple explicitly (`WebOnt-I5.5-005`)
and it is true of every cell of every collection. -/

def subjKey : Subject → String
  | .iri i => "I" ++ i.val
  | .bnode b => "B" ++ b

def termKey : Term → String
  | .iri i => "I" ++ i.val
  | .bnode b => "B" ++ b
  | .literal l => "L" ++ l.val.lexicalForm ++ "^" ++ l.val.datatype.val
  | .tripleTerm _ _ _ => "T"

/-- The spine for `elems` under `pre`: the head term, and the cells.
`rdf:nil` for the empty list. -/
def compListCells (pre : String) : List Term → Term × List Triple
  | [] => (Term.iri rdfNil, [])
  | e :: rest =>
    let (tailTerm, tailTs) := compListCells pre rest
    let cell : BNodeId := pre ++ "__cell__" ++ termKey e
    let cs : Subject := .bnode cell
    (Term.bnode cell,
      [ ⟨cs, rdfType, Term.iri L4Factoidal.RDFS.rdfList⟩,
        ⟨cs, rdfFirst, e⟩,
        ⟨cs, rdfRest, tailTerm⟩ ] ++ tailTs)

/-! ## Row 1 — `comp-uni1`, the singleton union class (§ 8.2)

For every NAMED class `C` in the closure the class expression
`UnionOf(C)` exists. One canonical instance per declared class, not the
infinite § 8.2 family. The witness class is extensionally equal to `C`,
so the structure emitted describes a class every interpretation
contains.

Targets `WebOnt-I5.5-005`, whose conclusion is exactly this floating
anonymous `owl:unionOf` over the premise's single declared class, and
whose own `test:description` names the comprehension principles. -/

def uni1Witness (c : WfIri) : Subject := .bnode ("__rl_compw_uni1__" ++ c.val)

def uni1Triples (c : WfIri) : List Triple :=
  let (head, cells) := compListCells ("__rl_compw_uni1l__" ++ c.val) [Term.iri c]
  [ ⟨uni1Witness c, rdfType, Term.iri owlClass⟩,
    ⟨uni1Witness c, owlUnionOf, head⟩ ] ++ cells

def compUni1For (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlClass then
    (subjIri d.s).flatMap uni1Triples
  else []

/-! ## Row 2 — `comp-trp-chain`, transitivity as a self-chain (§ 8.1)

`TransitiveObjectProperty(P)` and
`SubObjectPropertyOf(ObjectPropertyChain(P P), P)` have the SAME
semantic content: both say `IEXT(P)` is closed under composition with
itself (OWL 2 Direct Semantics § 2.3.2 / RDF-Based Semantics § 5.10).
The closure already has the other direction (`chainToTransitive`); this
row supplies the converse, together with the two-cell spine § 8.1
licenses for the pair `(P, P)`.

The spine is written by hand rather than through `compListCells`: the two
cells carry the same element, so the deterministic cell label would
collapse them into one.

Targets `New-Feature-ObjectPropertyChain-BJP-002`. -/

def chainCell1 (p : WfIri) : BNodeId := "__rl_chainl1__" ++ p.val
def chainCell2 (p : WfIri) : BNodeId := "__rl_chainl2__" ++ p.val

def trpChainTriples (p : WfIri) : List Triple :=
  let l1 : Subject := .bnode (chainCell1 p)
  let l2 : Subject := .bnode (chainCell2 p)
  [ ⟨Subject.iri p, owlPropertyChainAxiom, Term.bnode (chainCell1 p)⟩,
    ⟨l1, rdfType, Term.iri L4Factoidal.RDFS.rdfList⟩,
    ⟨l1, rdfFirst, Term.iri p⟩,
    ⟨l1, rdfRest, Term.bnode (chainCell2 p)⟩,
    ⟨l2, rdfType, Term.iri L4Factoidal.RDFS.rdfList⟩,
    ⟨l2, rdfFirst, Term.iri p⟩,
    ⟨l2, rdfRest, Term.iri rdfNil⟩ ]

def compTrpChainFor (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlTransitiveProperty then
    (subjIri d.s).flatMap trpChainTriples
  else []

/-! ## Row 3 — `comp-adf-clique`, `owl:AllDifferent` over a clique

`y rdf:type owl:AllDifferent` with `y owl:members (c1 … cn)` says
exactly that `c1 … cn` are pairwise distinct (RDF-Based Semantics
§ 5.7, the same reading `RLRules`' `allDifferentToDifferentFrom` uses
in the forward direction). So a set of individuals the closure has
already made pairwise `owl:differentFrom` licenses one such node, with
the § 8.1 spine over the set.

**Anchoring.** The rule does not search for cliques. For each
individual `x` with at least one `differentFrom` edge it takes
`{x} ∪ {y : x owl:differentFrom y}` and emits ONLY if that set is
pairwise different in the closure. So it is quadratic in the
differentFrom degree of `x`, linear in the number of such `x`, and
silent on a graph whose differentFrom relation is not locally complete.

**List order.** `owl:members` is a sequence, and which sequence a
conclusion document authors is arbitrary — the semantics is invariant
under permutation but blank-node matching is not. For a set of at most
`permCap` members the row emits every permutation, each with its own
spine, so a pass does not depend on the conclusion happening to be
written in the engine's sort order. Above that cap only the sorted
order is emitted, which is a recall limit and stated as one.

Targets `New-Feature-DisjointDataProperties-002` and
`New-Feature-DisjointObjectProperties-002`, whose conclusions are
three-member `owl:AllDifferent` axioms over individuals the premise
separates through `AllDisjointProperties`. -/

def permCap : Nat := 4

/-- Insert `x` at every position of `l`. -/
def interleave (x : WfIri) : List WfIri → List (List WfIri)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (interleave x ys).map (fun r => y :: r)

def permutations : List WfIri → List (List WfIri)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap (interleave x)

def adfNodeKey (ms : List WfIri) : String :=
  String.intercalate "__x__" (ms.map (·.val))

def adfTriples (ms : List WfIri) : List Triple :=
  let key := adfNodeKey ms
  let node : Subject := .bnode ("__rl_compw_adf__" ++ key)
  let (head, cells) := compListCells ("__rl_compw_adfl__" ++ key) (ms.map Term.iri)
  [ ⟨node, rdfType, Term.iri owlAllDifferent⟩,
    ⟨node, owlMembers, head⟩,
    ⟨node, owlDistinctMembers, head⟩ ] ++ cells

/-- The IRIs `x` is asserted `owl:differentFrom` in `g`. -/
def diffPartners (g : Graph) (x : WfIri) : List WfIri :=
  (withSubjPred g (Subject.iri x) owlDifferentFrom).flatMap (fun t => asIri t.o)

def pairwiseDifferent (g : Graph) (ms : List WfIri) : Bool :=
  ms.all (fun a => ms.all (fun b =>
    a == b || memB g ⟨Subject.iri a, owlDifferentFrom, Term.iri b⟩))

/-- Order-preserving dedup. -/
def dedupAcc (seen : List WfIri) : List WfIri → List WfIri
  | [] => []
  | x :: xs => if seen.contains x then dedupAcc seen xs
               else x :: dedupAcc (x :: seen) xs

def dedupIris (l : List WfIri) : List WfIri := dedupAcc [] l

/-- Insertion sort on the IRI string, so the emitted member list has a
canonical order independent of the closure's triple order. -/
def insIri (x : WfIri) : List WfIri → List WfIri
  | [] => [x]
  | y :: ys => if x.val < y.val then x :: y :: ys else y :: insIri x ys

def sortIris : List WfIri → List WfIri
  | [] => []
  | x :: xs => insIri x (sortIris xs)

/-- Everything the row emits for a member set: every permutation up to
`permCap`, the sorted order alone above it. `owl:members` is a
sequence and the conclusion document's order is arbitrary, so a pass
must not depend on the engine's sort order agreeing with it. -/
def adfEmission (ms : List WfIri) : List Triple :=
  if ms.length ≤ permCap then (permutations ms).flatMap adfTriples
  else adfTriples ms

def compAdfCliqueFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (subjIri d.s).flatMap (fun x =>
      let ms := sortIris (dedupIris (x :: diffPartners g x))
      if ms.length < 2 || !pairwiseDifferent g ms then [] else adfEmission ms)
  else []

/-! ## Row 3a — `pdw-diff`, disjoint properties separate individuals

`p1 owl:propertyDisjointWith p2` says `IEXT(p1) ∩ IEXT(p2) = ∅`
(RDF-Based Semantics § 5.10). Two contrapositives follow, and the RL
table states neither — it states only the CLASH they collapse to when
the two individuals are the same (`prp-pdw`, `prp-adp`).

* shared value: `x p1 v` and `y p2 v` with `x` and `y` distinct names.
  If `x` and `y` denoted the same resource the pair `⟨x, v⟩` would be in
  both extensions, so `x owl:differentFrom y`.
* shared subject: `x p1 o1` and `x p2 o2` with `o1`, `o2` distinct
  names. Same argument on the object side.

Neither needs a unique-name assumption: the conclusion is
`owl:differentFrom`, which is what "these do not denote the same
resource" IS.

An `owl:AllDisjointProperties` axiom is read as pairwise
`owl:propertyDisjointWith` over its member list, which is § 5.10's own
reading of it and the same reading the closure's `prp-adp` clash row
uses.

Targets `New-Feature-DisjointDataProperties-002` and
`New-Feature-DisjointObjectProperties-002`: three individuals, three
pairwise-disjoint properties, one shared value, so the three are
pairwise different and row 3 can then name them in one
`owl:AllDifferent` node. -/

/-- Every ordered pair of properties the graph makes disjoint: asserted
`owl:propertyDisjointWith`, plus every ordered pair of distinct members
of an `owl:AllDisjointProperties` list. -/
def disjointPropPairs (g : Graph) : List (WfIri × WfIri) :=
  (withPred g owlPropertyDisjointWith).flatMap (fun t =>
    (subjIri t.s).flatMap (fun p1 => (asIri t.o).map (fun p2 => (p1, p2)))) ++
  (withPredObj g rdfType (Term.iri owlAllDisjointProperties)).flatMap (fun t =>
    (withSubjPred g t.s owlMembers).flatMap (fun mem =>
      let ps := (listElems g mem.o (listFuel g)).flatMap asIri
      ps.flatMap (fun p1 => (ps.filter (fun p2 => p2 != p1)).map (fun p2 => (p1, p2)))))

/-- Row 3a, driven by an edge `d` whose predicate is disjoint from some
`p2`. Both contrapositives, over the pairs `disjointPropPairs` names. -/
def pdwDiffFor (g : Graph) (d : Triple) : List Triple :=
  (disjointPropPairs g).flatMap (fun pr =>
    let (p1, p2) := pr
    if d.p != p1 then [] else
      -- shared value: (d.s p1 d.o) and (y p2 d.o)
      ((withPredObj g p2 d.o).filterMap (fun t =>
        if t.s == d.s then none
        else some (⟨d.s, owlDifferentFrom, t.s.toTerm⟩ : Triple))) ++
      -- shared subject: (d.s p1 d.o) and (d.s p2 o2)
      ((withSubjPred g d.s p2).filterMap (fun t =>
        if t.o == d.o then none
        else match asSubject d.o with
             | os :: _ => some (⟨os, owlDifferentFrom, t.o⟩ : Triple)
             | [] => none)))

/-! ## Rows 4 and 5 — `owl:someValuesFrom owl:Thing` (§ 8.4)

`owl:Thing` is the universal class, so `x P y` for ANY `y` puts `x` in
`SomeValuesFrom(P, owl:Thing)`, and § 8.4 provides that restriction
class for every property. Symmetrically, membership in such a
restriction says a `P`-successor exists (RDF-Based Semantics § 5.4), so
a witness edge may be minted for it.

The restriction node is keyed on `P` alone — `owl:Thing` is fixed — so
neither row invents a node per edge. The witness of row 5 is left
UNTYPED: `owl:Thing` membership is vacuous and typing it would only
give the following re-closure more to chain off for no semantic gain.

Targets `bnode2somevaluesfrom` (row 4) and `somevaluesfrom2bnode`,
`WebOnt-someValuesFrom-003` (row 5). -/

def svfThingRestriction (p : WfIri) : BNodeId := "__rl_svfthing__" ++ p.val

def svfThingShape (p : WfIri) : List Triple :=
  let r : Subject := .bnode (svfThingRestriction p)
  [ ⟨r, rdfType, Term.iri owlRestriction⟩,
    ⟨r, owlOnProperty, Term.iri p⟩,
    ⟨r, owlSomeValuesFrom, Term.iri owlThing⟩ ]

def svfThingMatFor (d : Triple) : List Triple :=
  if isDataPredicate d.p && edgeSubjectIsSafe d.s && !(asSubject d.o).isEmpty then
    svfThingShape d.p ++
      [ ⟨d.s, rdfType, Term.bnode (svfThingRestriction d.p)⟩ ]
  else []

def svfThingWitnessNode (p : WfIri) (x : Subject) : BNodeId :=
  "__rl_svfthingw__on__" ++ p.val ++ "__from__" ++ subjKey x

/-- Row 5, driven by the `owl:someValuesFrom owl:Thing` triple. -/
def svfThingWitFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom && d.o == Term.iri owlThing then
    (withSubjPred g d.s owlOnProperty).flatMap (fun op =>
      (asIri op.o).flatMap (fun p =>
        (withPredObj g rdfType d.s.toTerm).map (fun m =>
          (⟨m.s, p, Term.bnode (svfThingWitnessNode p m.s)⟩ : Triple))))
  else []

/-! ## Row 6 — `hasself-synth`, `ObjectHasSelf` (§ 8.4)

A self-loop `x P x` puts `x` in `HasSelf(P)` (RDF-Based Semantics
§ 5.4's `owl:hasSelf` condition), and § 8.4 provides that restriction
class for every property. Restriction node keyed on `P` alone.

Targets `New-Feature-SelfRestriction-002`. -/

def hasSelfRestriction (p : WfIri) : BNodeId := "__rl_hasself__" ++ p.val

def hasSelfShape (p : WfIri) : List Triple :=
  let r : Subject := .bnode (hasSelfRestriction p)
  [ ⟨r, rdfType, Term.iri owlRestriction⟩,
    ⟨r, owlOnProperty, Term.iri p⟩,
    ⟨r, owlHasSelf, Term.literal litTrueBoolean⟩ ]

def hasSelfSynthFor (d : Triple) : List Triple :=
  if isDataPredicate d.p && edgeSubjectIsSafe d.s && d.s.toTerm == d.o then
    hasSelfShape d.p ++ [ ⟨d.s, rdfType, Term.bnode (hasSelfRestriction d.p)⟩ ]
  else []

/-! ## The layer -/

/-- Stage 1: the two rows that MINT a restriction node from a data
edge. Both read `base` only. -/
def stage1For (d : Triple) : List Triple :=
  svfThingMatFor d ++ hasSelfSynthFor d

/-- Stage 2: the successor-witness row. It reads stage 1's output,
because the restriction node it is driven by may be the one stage 1
minted (`bnode2somevaluesfrom` authors no restriction at all). Stage 2
does not feed stage 1. -/
def stage2For (g1 : Graph) (d : Triple) : List Triple :=
  svfThingWitFor g1 d

/-- Stage 3: the two disjoint-property contrapositives. They mint no
blank node and read `base` only; they run before stage 4 because the
`owl:AllDifferent` row consumes the `owl:differentFrom` facts they
produce. -/
def stage3For (base : Graph) (d : Triple) : List Triple :=
  pdwDiffFor base d

/-- Stage 4: the three comprehension rows. `compUni1For` and
`compTrpChainFor` read the driving triple alone; `compAdfCliqueFor`
reads stage 3's output, which is the only place a row reads a previous
stage, and stage 3 does not read stage 4. So no witness is ever built
over a witness. -/
def stage4For (g3 : Graph) (d : Triple) : List Triple :=
  compUni1For d ++ compTrpChainFor d ++ compAdfCliqueFor g3 d

/-- The stages, named so each one has its own soundness theorem in
`ComprehensionTheorems.lean`. -/
def layerStage1 (base : Graph) : Graph :=
  base.foldl (fun acc d => addAll acc (stage1For d)) base

def layerStage2 (base : Graph) : Graph :=
  let g1 := layerStage1 base
  g1.foldl (fun acc d => addAll acc (stage2For g1 d)) g1

def layerStage3 (base : Graph) : Graph :=
  base.foldl (fun acc d => addAll acc (stage3For base d)) (layerStage2 base)

/-- The layer: `base`, then the four stages in order. Stratified, and
applied once — see the header's termination note. -/
def comprehensionLayer (base : Graph) : Graph :=
  let g3 := layerStage3 base
  g3.foldl (fun acc d => addAll acc (stage4For g3 d)) g3

end L4Factoidal.OWL.Comp
