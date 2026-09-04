/-
L4Factoidal.OWL.RLClosureIndexed — the OWL 2 RL/RDF closure over an
INDEXED triple store, with a proof that it computes the SAME list as
`RLClosure.closure`.

`RLClosure.lean` reads every premise by scanning the whole graph
(`withPred g p = g.filter …`). That is the specification-level lookup;
it costs O(|g|) per lookup, so a round over a 3 000-triple ontology
costs minutes and the W3C cases WebOnt-miscellaneous-001/002/011 hit
the 20 s budget before finishing ONE round (measured 2026-08-22, see
`PORT_NOTES.md`). The F* tree solved the same problem for RDFS with
`RDFS.Closure.SemiNaive.fst`; this file is the Lean counterpart for
OWL RL.

## Design: one row body, two premise stores

Each of the 61 row functions is written ONCE here, over an abstract
`Store` — a record holding the graph list and the six premise lookups
(`withPred`, `withSubj`, `withObj`, `withSubjPred`, `withPredObj`,
`memB`). Two stores exist:

* `Store.ofGraph g` packs `RLClosure`'s list scans. Every row applied
  to it is DEFINITIONALLY the `RLClosure` row (`eqRepSForS_ofGraph :
  eqRepSForS (Store.ofGraph g) d = eqRepSFor g d := rfl`, and so on
  for all 61 rows and the 13 clash rows). The per-row soundness
  lemmas of `RLTheorems.lean` therefore apply unchanged.
* `Store.ofIndex i` packs the hash-index lookups of an `Index`.

`Index.Wf i g` says the index is a faithful picture of the list `g`:
its array IS `g`, its membership set decides `memB g`, and each
bucket lookup returns EXACTLY the corresponding list filter, in the
same order. Under `Wf`, `Store.ofIndex i = Store.ofGraph g`
(`Store.ofIndex_eq`), so a round over the index produces the same
conclusion list as a round over the graph, the insertion of those
conclusions preserves `Wf` against `addAll`, and the fuel loop takes
the same branch at every round. The result:

    closureI_toGraph :
      (closureI (Index.ofGraph g) fuel).toGraph = closure g fuel

a LIST equality, at every fuel — stronger than the set equality the
task asked for; set membership, soundness against `Derives` and the
clash verdict follow as corollaries.

## Evaluation strategy and cost model

Evaluation is NAIVE with indexed joins, not semi-naive: every round
drives every row from every triple of the round's input snapshot,
exactly as `RLClosure.step` does. That choice is what makes the bridge
theorem a per-round list equality instead of a fixpoint argument; it
is also sufficient for the corpus (see `PORT_NOTES.md` for the
measured before/after — 0 cap hits at the same 20 s budget).

Cost model (hash operations are expected O(1); `n` = triples in the
round's input, `E` = conclusions emitted before deduplication):

* `Index.insert`: one `Array.push`, one `HashSet.insert`, five
  `HashMap.getD` + `insert` with a list cons — O(1).
* a bucket lookup: O(1) + O(result) for the reversal.
* `memB`: O(1).
* one round: 61 guard checks per input triple (string equalities on
  the predicate) + the joins, each proportional to its own output,
  + O(E) deduplication — O(n + E) instead of the list engine's
  O(n · E · n)-ish (each join a scan, each dedup a scan).
* rounds: at most the derivation depth of the graph (the loop stops
  at the first round that adds nothing), the same count as
  `RLClosure.closure`.

Buckets hold their triples in REVERSE insertion order (a cons per
insert is O(1) and needs no in-place array update); the lookup
reverses, which costs no more than consuming the result does. That is
what makes the bucket equal to the list filter as a list, not just as
a set.

## What is NOT here

No semi-naive delta evaluation and no rule stratification. Both would
change which triples each ROUND emits (not which triples the FIXPOINT
holds), so their bridge theorem is an equality at saturation, which is
a different and longer proof. They are the next step if a corpus ever
needs them; the measurements in `PORT_NOTES.md` say this one does not.
-/
import L4Factoidal.OWL.RLClosure
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## Section 1 — the abstract premise store -/

/-- The premise lookups a row reads, packaged. `graph` is the round's
input as a list — the rows that enumerate every subject (cls-int1,
prp-spo2) and the collection-walk fuel read it. -/
structure Store where
  graph        : Graph
  withPred     : WfIri → List Triple
  withSubj     : Subject → List Triple
  withObj      : Term → List Triple
  withSubjPred : Subject → WfIri → List Triple
  withPredObj  : WfIri → Term → List Triple
  memB         : Triple → Bool

/-- The list-scan store: `RLClosure`'s lookups, verbatim. -/
def Store.ofGraph (g : Graph) : Store :=
  { graph := g,
    withPred := RL.withPred g, withSubj := RL.withSubj g, withObj := RL.withObj g,
    withSubjPred := RL.withSubjPred g, withPredObj := RL.withPredObj g,
    memB := RL.memB g }

/-! ## Section 2 — the index -/

/-- The indexed triple store. `all` is the graph in insertion order;
`set` decides exact membership; the five maps are the SPO-style
access paths the rows use, each bucket holding the reversed filter. -/
structure Index where
  all  : Array Triple
  set  : Std.HashSet Triple
  byS  : Std.HashMap Subject (List Triple)
  byP  : Std.HashMap WfIri (List Triple)
  byO  : Std.HashMap Term (List Triple)
  bySP : Std.HashMap (Subject × WfIri) (List Triple)
  byPO : Std.HashMap (WfIri × Term) (List Triple)

namespace Index

def empty : Index :=
  { all := #[], set := ∅, byS := ∅, byP := ∅, byO := ∅, bySP := ∅, byPO := ∅ }

/-- The graph the index pictures, in insertion order. -/
def toGraph (i : Index) : Graph := i.all.toList

def memB (i : Index) (t : Triple) : Bool := i.set.contains t
def withSubj (i : Index) (s : Subject) : List Triple := (i.byS.getD s []).reverse
def withPred (i : Index) (p : WfIri) : List Triple := (i.byP.getD p []).reverse
def withObj (i : Index) (o : Term) : List Triple := (i.byO.getD o []).reverse
def withSubjPred (i : Index) (s : Subject) (p : WfIri) : List Triple :=
  (i.bySP.getD (s, p) []).reverse
def withPredObj (i : Index) (p : WfIri) (o : Term) : List Triple :=
  (i.byPO.getD (p, o) []).reverse

/-- Append a triple unconditionally (the index of `g ++ [t]`). -/
def push (i : Index) (t : Triple) : Index :=
  { all  := i.all.push t,
    set  := i.set.insert t,
    byS  := i.byS.insert t.s (t :: i.byS.getD t.s []),
    byP  := i.byP.insert t.p (t :: i.byP.getD t.p []),
    byO  := i.byO.insert t.o (t :: i.byO.getD t.o []),
    bySP := i.bySP.insert (t.s, t.p) (t :: i.bySP.getD (t.s, t.p) []),
    byPO := i.byPO.insert (t.p, t.o) (t :: i.byPO.getD (t.p, t.o) []) }

/-- Append every triple of a list unconditionally (the index of
`g ++ ts`). -/
def pushAll (i : Index) : List Triple → Index
  | []      => i
  | t :: ts => pushAll (i.push t) ts

/-- The index of a graph — duplicates and all, so that `toGraph` is
the input list itself. -/
def ofGraph (g : Graph) : Index := pushAll empty g

/-- Set-wise insertion with EXACT equality — the counterpart of
`RLClosure.addOne`. -/
def insert (i : Index) (t : Triple) : Index :=
  if i.memB t then i else i.push t

/-- The counterpart of `RLClosure.addAll`. -/
def insertAll (i : Index) : List Triple → Index
  | []      => i
  | t :: ts => insertAll (i.insert t) ts

end Index

/-- The hash-lookup store over an index. -/
def Store.ofIndex (i : Index) : Store :=
  { graph := i.toGraph,
    withPred := i.withPred, withSubj := i.withSubj, withObj := i.withObj,
    withSubjPred := i.withSubjPred, withPredObj := i.withPredObj,
    memB := i.memB }

/-! ## Section 3 — the collection walks and batched premises, over a
store -/

def listElemsS (s : Store) : Term → Nat → List Term
  | _,    0     => []
  | head, n + 1 =>
      (asSubject head).flatMap (fun node =>
        (s.withSubjPred node rdfFirst).map (fun u => u.o) ++
        (s.withSubjPred node rdfRest).flatMap (fun r => listElemsS s r.o n))

def listCellsS (s : Store) : Term → Nat → List Subject
  | _,    0     => []
  | head, n + 1 =>
      (asSubject head).flatMap (fun node =>
        node :: (s.withSubjPred node rdfRest).flatMap
          (fun r => listCellsS s r.o n))

def listSeqsS (s : Store) : Term → Nat → List (List Term)
  | _,    0     => []
  | head, n + 1 =>
    if head == Term.iri rdfNil then [[]]
    else
      (asSubject head).flatMap (fun node =>
        (s.withSubjPred node rdfFirst).flatMap (fun f =>
          (s.withSubjPred node rdfRest).flatMap (fun r =>
            (listSeqsS s r.o n).map (fun rest => f.o :: rest))))

def typesAllBS (s : Store) (y : Subject) (cs : List Term) : Bool :=
  cs.all (fun c => s.memB ⟨y, rdfType, c⟩)

def sharesKeyValuesBS (s : Store) (x y : Subject) (ps : List WfIri) : Bool :=
  ps.all (fun p => (s.withSubjPred x p).any (fun ux => s.memB ⟨y, p, ux.o⟩))

def chainTargetsS (s : Store) : Subject → List WfIri → List Term
  | start, []       => [start.toTerm]
  | start, [p]      => (s.withSubjPred start p).map (fun u => u.o)
  | start, p :: rest =>
      (s.withSubjPred start p).flatMap (fun u =>
        (asSubject u.o).flatMap (fun mid => chainTargetsS s mid rest))

/-! ## Section 4 — the rows, over a store

Same bodies as `RLClosure` Section 5, with the lookups read from the
store. -/

def eqRefSForS (_s : Store) (d : Triple) : List Triple :=
  [⟨d.s, owlSameAs, d.s.toTerm⟩]

def eqRefPForS (_s : Store) (d : Triple) : List Triple :=
  [⟨Subject.iri d.p, owlSameAs, Term.iri d.p⟩]

def eqRefOForS (_s : Store) (d : Triple) : List Triple :=
  (asSubject d.o).map (fun os => ⟨os, owlSameAs, os.toTerm⟩)

def eqSymForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).map (fun ys => ⟨ys, owlSameAs, d.s.toTerm⟩)
  else []

def eqTransForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).flatMap (fun ys =>
      (s.withSubjPred ys owlSameAs).map (fun u => ⟨d.s, owlSameAs, u.o⟩))
  else []

def eqRepSForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).flatMap (fun s' =>
      (s.withSubj d.s).map (fun u => ⟨s', u.p, u.o⟩))
  else []

def eqRepPForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (subjIri d.s).flatMap (fun p =>
        (asIri d.o).flatMap (fun p' =>
          (s.withPred p).map (fun u => ⟨u.s, p', u.o⟩)))
  else []

def eqRepOForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (s.withObj d.s.toTerm).map (fun u => ⟨u.s, u.p, d.o⟩)
  else []

def prpDomForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (subjIri d.s).flatMap (fun p => (s.withPred p).map (fun u => ⟨u.s, rdfType, d.o⟩))
  else []

def prpRngForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          (asSubject u.o).map (fun ys => ⟨ys, rdfType, d.o⟩)))
  else []

def prpFpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlFunctionalProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u1 =>
          (asSubject u1.o).flatMap (fun y1s =>
            (s.withSubjPred u1.s p).map (fun u2 => ⟨y1s, owlSameAs, u2.o⟩))))
  else []

def prpIfpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlInverseFunctionalProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u1 =>
          (s.withPredObj p u1.o).map (fun u2 =>
            ⟨u1.s, owlSameAs, u2.s.toTerm⟩)))
  else []

def prpSympForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlSymmetricProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          (asSubject u.o).map (fun ys => ⟨ys, p, u.s.toTerm⟩)))
  else []

def prpTrpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlTransitiveProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u1 =>
          (asSubject u1.o).flatMap (fun ys =>
            (s.withSubjPred ys p).map (fun u2 => ⟨u1.s, p, u2.o⟩))))
  else []

def prpSpo1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p1).map (fun u => ⟨u.s, p2, u.o⟩)))
  else []

def prpSpo2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlPropertyChainAxiom then
    (subjIri d.s).flatMap (fun p =>
      (listSeqsS s d.o (listFuel s.graph)).flatMap (fun terms =>
        (nonEmpty (allIris terms)).flatMap (fun preds =>
          (subjectsOf s.graph).flatMap (fun x1 =>
            (chainTargetsS s x1 preds).map (fun xn => ⟨x1, p, xn⟩)))))
  else []

def prpEqp1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p1).map (fun u => ⟨u.s, p2, u.o⟩)))
  else []

def prpEqp2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p2).map (fun u => ⟨u.s, p1, u.o⟩)))
  else []

def prpInv1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p1).flatMap (fun u =>
            (asSubject u.o).map (fun ys => ⟨ys, p2, u.s.toTerm⟩))))
  else []

def prpInv2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p2).flatMap (fun u =>
            (asSubject u.o).map (fun ys => ⟨ys, p1, u.s.toTerm⟩))))
  else []

def prpKeyForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasKey then
    (listSeqsS s d.o (listFuel s.graph)).flatMap (fun terms =>
      (nonEmpty (allIris terms)).flatMap (fun preds =>
        (s.withPredObj rdfType d.s.toTerm).flatMap (fun tx =>
          (s.withPredObj rdfType d.s.toTerm).flatMap (fun ty =>
            if sharesKeyValuesBS s tx.s ty.s preds
            then [⟨tx.s, owlSameAs, ty.s.toTerm⟩] else []))))
  else []

def clsInt1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (nonEmpty (listSeqsS s d.o (listFuel s.graph))).flatMap (fun cs =>
      (subjectsOf s.graph).flatMap (fun y =>
        if typesAllBS s y cs then [⟨y, rdfType, d.s.toTerm⟩] else []))
  else []

def clsInt2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun ci =>
      (s.withPredObj rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, ci⟩))
  else []

def clsUniForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlUnionOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun ci =>
      (s.withPredObj rdfType ci).map (fun u =>
        ⟨u.s, rdfType, d.s.toTerm⟩))
  else []

def clsSvf1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          (asSubject u.o).flatMap (fun vs =>
            if s.memB ⟨vs, rdfType, d.o⟩
            then [⟨u.s, rdfType, d.s.toTerm⟩] else []))))
  else []

def clsSvf2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom && d.o == Term.iri owlThing then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPred p).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)))
  else []

def clsAvfForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlAllValuesFrom then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).flatMap (fun tu =>
          (s.withSubjPred tu.s p).flatMap (fun u =>
            (asSubject u.o).map (fun vs => ⟨vs, rdfType, d.o⟩)))))
  else []

def clsHv1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasValue then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).map (fun tu => ⟨tu.s, p, d.o⟩)))
  else []

def clsHv2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasValue then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj p d.o).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)))
  else []

def clsHs1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasSelf && d.o == Term.literal litTrueBoolean then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).map (fun tu =>
          ⟨tu.s, p, tu.s.toTerm⟩)))
  else []

def clsHs2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasSelf && d.o == Term.literal litTrueBoolean then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          if u.o == u.s.toTerm then [⟨u.s, rdfType, d.s.toTerm⟩] else [])))
  else []

def clsMaxc2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlMaxCardinality && d.o == Term.literal litNni1 then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).flatMap (fun tu =>
          (s.withSubjPred tu.s p).flatMap (fun u1 =>
            (asSubject u1.o).flatMap (fun y1s =>
              (s.withSubjPred tu.s p).map (fun u2 =>
                ⟨y1s, owlSameAs, u2.o⟩))))))
  else []

def clsOoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlOneOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun yi =>
      (asSubject yi).map (fun yis => ⟨yis, rdfType, d.s.toTerm⟩))
  else []

def caxScoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (s.withPredObj rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, d.o⟩)
  else []

def caxEqc1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    (s.withPredObj rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, d.o⟩)
  else []

def caxEqc2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    (s.withPredObj rdfType d.o).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)
  else []

def scmClsForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlClass then
    [⟨d.s, rdfsSubClassOf, d.s.toTerm⟩,
     ⟨d.s, owlEquivalentClass, d.s.toTerm⟩,
     ⟨d.s, rdfsSubClassOf, Term.iri owlThing⟩,
     ⟨Subject.iri owlNothing, rdfsSubClassOf, d.s.toTerm⟩]
  else []

def scmScoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (asSubject d.o).flatMap (fun c2s =>
      (s.withSubjPred c2s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsSubClassOf, u.o⟩))
  else []

def scmEqc1ForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    ⟨d.s, rdfsSubClassOf, d.o⟩ ::
      (asSubject d.o).map (fun c2s => ⟨c2s, rdfsSubClassOf, d.s.toTerm⟩)
  else []

def scmEqc2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (asSubject d.o).flatMap (fun c2s =>
      if s.memB ⟨c2s, rdfsSubClassOf, d.s.toTerm⟩
      then [⟨d.s, owlEquivalentClass, d.o⟩] else [])
  else []

def scmSpoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (asSubject d.o).flatMap (fun p2s =>
      (s.withSubjPred p2s rdfsSubPropertyOf).map (fun u =>
        ⟨d.s, rdfsSubPropertyOf, u.o⟩))
  else []

def scmEqp1ForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    ⟨d.s, rdfsSubPropertyOf, d.o⟩ ::
      (asSubject d.o).map (fun p2s => ⟨p2s, rdfsSubPropertyOf, d.s.toTerm⟩)
  else []

def scmEqp2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (asSubject d.o).flatMap (fun p2s =>
      if s.memB ⟨p2s, rdfsSubPropertyOf, d.s.toTerm⟩
      then [⟨d.s, owlEquivalentProperty, d.o⟩] else [])
  else []

def scmDom1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (asSubject d.o).flatMap (fun c1s =>
      (s.withSubjPred c1s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsDomain, u.o⟩))
  else []

def scmDom2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (s.withPredObj rdfsSubPropertyOf d.s.toTerm).map (fun u =>
      ⟨u.s, rdfsDomain, d.o⟩)
  else []

def scmRng1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (asSubject d.o).flatMap (fun c1s =>
      (s.withSubjPred c1s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsRange, u.o⟩))
  else []

def scmRng2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (s.withPredObj rdfsSubPropertyOf d.s.toTerm).map (fun u =>
      ⟨u.s, rdfsRange, d.o⟩)
  else []

def scmOpForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlObjectProperty then
    [⟨d.s, rdfsSubPropertyOf, d.s.toTerm⟩,
     ⟨d.s, owlEquivalentProperty, d.s.toTerm⟩]
  else []

def scmDpForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlDatatypeProperty then
    [⟨d.s, rdfsSubPropertyOf, d.s.toTerm⟩,
     ⟨d.s, owlEquivalentProperty, d.s.toTerm⟩]
  else []

def scmIntForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (listElemsS s d.o (listFuel s.graph)).map (fun ci =>
      ⟨d.s, rdfsSubClassOf, ci⟩)
  else []

def scmUniForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlUnionOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun ci =>
      (asSubject ci).map (fun cis => ⟨cis, rdfsSubClassOf, d.s.toTerm⟩))
  else []

/-! ### The `[ext]` rows, over a store -/

def eqDiffSymForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (asSubject d.o).map (fun ys => ⟨ys, owlDifferentFrom, d.s.toTerm⟩)
  else []

def pdwToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlPropertyDisjointWith then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        (s.withPred p1).flatMap (fun t1 =>
          (asSubject t1.o).flatMap (fun o1s =>
            (s.withSubjPred t1.s p2).flatMap (fun t2 =>
              if o1s.toTerm == t2.o then []
              else [⟨o1s, owlDifferentFrom, t2.o⟩])))))
  else []

def caxDwToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlDisjointWith then
    (subjIri d.s).flatMap (fun c1 =>
      (asIri d.o).flatMap (fun c2 =>
        (s.withPredObj rdfType (Term.iri c1)).flatMap (fun tx =>
          (s.withPredObj rdfType (Term.iri c2)).flatMap (fun ty =>
            if tx.s == ty.s then [] else [⟨tx.s, owlDifferentFrom, ty.s.toTerm⟩]))))
  else []

def fpDiffToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (s.withObj d.s.toTerm).flatMap (fun t1 =>
      if s.memB ⟨Subject.iri t1.p, rdfType, Term.iri owlFunctionalProperty⟩ then
        (s.withPredObj t1.p d.o).flatMap (fun t2 =>
          if t1.s == t2.s then [] else [⟨t1.s, owlDifferentFrom, t2.s.toTerm⟩])
      else [])
  else []

def ifpDiffToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (s.withSubj d.s).flatMap (fun t1 =>
      if s.memB ⟨Subject.iri t1.p, rdfType,
          Term.iri owlInverseFunctionalProperty⟩ then
        (asSubject t1.o).flatMap (fun y1s =>
          (asSubject d.o).flatMap (fun x2s =>
            (s.withSubjPred x2s t1.p).flatMap (fun t2 =>
              if y1s.toTerm == t2.o then []
              else [⟨y1s, owlDifferentFrom, t2.o⟩])))
      else [])
  else []

def chainToTransForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlPropertyChainAxiom then
    (subjIri d.s).flatMap (fun p =>
      (listSeqsS s d.o (listFuel s.graph)).flatMap (fun terms =>
        if terms == [Term.iri p, Term.iri p]
        then [⟨Subject.iri p, rdfType, Term.iri owlTransitiveProperty⟩]
        else []))
  else []

def prpRflForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlReflexiveProperty then
    (subjIri d.s).flatMap (fun p =>
      (iriIndividuals s.graph).map (fun i => ⟨Subject.iri i, p, Term.iri i⟩))
  else []

def xsdAxiomsForS (_s : Store) (d : Triple) : List Triple :=
  if drivesXsdAxioms d then xsdAxiomTriples else []

def dtRangeIntersectForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (asIri d.o).flatMap (fun d1 =>
      (s.withSubjPred d.s rdfsRange).flatMap (fun t2 =>
        (asIri t2.o).flatMap (fun d2 =>
          xsdRangeIntersections.flatMap (fun e =>
            if (e.1 == d1 && e.2.1 == d2) || (e.1 == d2 && e.2.1 == d1)
            then e.2.2.map (fun d3 => ⟨d.s, rdfsRange, Term.iri d3⟩)
            else []))))
  else []

def caxDwToComplementForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlDisjointWith then
    (subjIri d.s).flatMap (fun c1 =>
      (asIri d.o).flatMap (fun c2 => complementWitnessTriples c1 c2))
  else []

def clsMaxqc1ToComplementForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni1 then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withSubjPred d.s owlOnClass).flatMap (fun onc =>
          (asIri onc.o).flatMap (fun c =>
            (s.withPredObj rdfType d.s.toTerm).flatMap (fun tu =>
              (s.withSubjPred tu.s p).flatMap (fun u1 =>
                (asSubject u1.o).flatMap (fun y1s =>
                  if s.memB ⟨y1s, rdfType, Term.iri c⟩ then
                    (s.withSubjPred y1s owlDifferentFrom).flatMap (fun df =>
                      (asSubject df.o).flatMap (fun y2s =>
                        if s.memB ⟨tu.s, p, y2s.toTerm⟩
                        then complementTypeTriples y2s c else []))
                  else [])))))))
  else []

def minCard1ComprehensionForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlObjectProperty then
    (subjIri d.s).flatMap minCard1WitnessTriples
  else []

def caxAdcToDwForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointClasses then
    (s.withSubjPred d.s owlMembers).flatMap (fun mem =>
      (listElemsS s mem.o (listFuel s.graph)).flatMap (fun ci =>
        (asIri ci).flatMap (fun ci' =>
          (listElemsS s mem.o (listFuel s.graph)).flatMap (fun cj =>
            (asIri cj).flatMap (fun cj' =>
              if ci' == cj' then []
              else [⟨Subject.iri ci', owlDisjointWith, Term.iri cj'⟩])))))
  else []

/-! ## Section 5 — one round and the loop, over the index -/

/-- **inv-flip** `[ext]` — the store version scans `s.graph`, exactly
as the list version scans `g`. -/
def inverseOfDomRngFlipForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        s.graph.flatMap (fun t =>
          match t.s, t.o with
          | .iri srcP, .iri c =>
              if      srcP == p1 && t.p == rdfsDomain then [(⟨.iri p2, rdfsRange, .iri c⟩ : Triple)]
              else if srcP == p1 && t.p == rdfsRange  then [(⟨.iri p2, rdfsDomain, .iri c⟩ : Triple)]
              else if srcP == p2 && t.p == rdfsDomain then [(⟨.iri p1, rdfsRange, .iri c⟩ : Triple)]
              else if srcP == p2 && t.p == rdfsRange  then [(⟨.iri p1, rdfsDomain, .iri c⟩ : Triple)]
              else []
          | _, _ => [])))
  else []

def conclusionsListS (s : Store) (d : Triple) : List (List Triple) :=
    [ eqRefSForS s d, eqRefPForS s d, eqRefOForS s d,
      eqSymForS s d, eqTransForS s d,
      eqRepSForS s d, eqRepPForS s d, eqRepOForS s d,
      prpDomForS s d, prpRngForS s d, prpFpForS s d, prpIfpForS s d,
      prpSympForS s d, prpTrpForS s d, prpSpo1ForS s d, prpSpo2ForS s d,
      prpEqp1ForS s d, prpEqp2ForS s d, prpInv1ForS s d, prpInv2ForS s d,
      prpKeyForS s d,
      clsInt1ForS s d, clsInt2ForS s d, clsUniForS s d,
      clsSvf1ForS s d, clsSvf2ForS s d, clsAvfForS s d,
      clsHv1ForS s d, clsHv2ForS s d, clsHs1ForS s d, clsHs2ForS s d,
      clsMaxc2ForS s d, clsOoForS s d,
      caxScoForS s d, caxEqc1ForS s d, caxEqc2ForS s d,
      scmClsForS s d, scmScoForS s d, scmEqc1ForS s d, scmEqc2ForS s d,
      scmSpoForS s d, scmEqp1ForS s d, scmEqp2ForS s d,
      scmDom1ForS s d, scmDom2ForS s d, scmRng1ForS s d, scmRng2ForS s d,
      scmOpForS s d, scmDpForS s d,
      scmIntForS s d, scmUniForS s d,
      eqDiffSymForS s d, pdwToDiffForS s d, caxDwToDiffForS s d,
      fpDiffToDiffForS s d, ifpDiffToDiffForS s d,
      chainToTransForS s d, prpRflForS s d,
      xsdAxiomsForS s d, dtRangeIntersectForS s d,
      caxDwToComplementForS s d, clsMaxqc1ToComplementForS s d,
      minCard1ComprehensionForS s d, caxAdcToDwForS s d,
      inverseOfDomRngFlipForS s d ]

def conclusionsFromS (s : Store) (d : Triple) : List Triple :=
  (conclusionsListS s d).flatten

def stepConclusionsS (s : Store) : List Triple :=
  axiomTriples ++ s.graph.flatMap (conclusionsFromS s)

/-- One closure round over the index — the counterpart of
`RLClosure.step`. -/
def stepI (i : Index) : Index :=
  i.insertAll (stepConclusionsS (Store.ofIndex i))

/-- The fuel loop — the counterpart of `RLClosure.closure`, same
stopping rule (the size did not change). -/
def closureI (i : Index) (fuel : Nat) : Index :=
  match fuel with
  | 0     => i
  | n + 1 =>
      let i' := stepI i
      if i'.all.size = i.all.size then i else closureI i' n

/-- The indexed closure of a graph, as a graph. -/
def indexedClosure (g : Graph) (fuel : Nat) : Graph :=
  (closureI (Index.ofGraph g) fuel).toGraph

/-! ## Section 6 — the clash rows, over a store -/

def eqDiff1AtS (s : Store) (d : Triple) : Bool :=
  d.p == owlSameAs && s.memB ⟨d.s, owlDifferentFrom, d.o⟩

def prpIrpAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlIrreflexiveProperty then
    (subjIri d.s).any (fun p => (s.withPred p).any (fun u => u.o == u.s.toTerm))
  else false

def prpAsypAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAsymmetricProperty then
    (subjIri d.s).any (fun p =>
        (s.withPred p).any (fun u1 =>
          (asSubject u1.o).any (fun y => s.memB ⟨y, p, u1.s.toTerm⟩)))
  else false

def prpPdwAtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlPropertyDisjointWith then
    (subjIri d.s).any (fun p1 =>
        (asIri d.o).any (fun p2 =>
          (s.withPred p1).any (fun u => s.memB ⟨u.s, p2, u.o⟩)))
  else false

def prpNpa1AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlSourceIndividual then
    (asSubject d.o).any (fun x =>
      (s.withSubjPred d.s owlAssertionProperty).any (fun ap =>
        (asIri ap.o).any (fun p =>
          (s.withSubjPred d.s owlTargetIndividual).any (fun ti =>
            s.memB ⟨x, p, ti.o⟩))))
  else false

def prpNpa2AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlSourceIndividual then
    (asSubject d.o).any (fun x =>
      (s.withSubjPred d.s owlAssertionProperty).any (fun ap =>
        (asIri ap.o).any (fun p =>
          (s.withSubjPred d.s owlTargetValue).any (fun tv =>
            s.memB ⟨x, p, tv.o⟩))))
  else false

def clsNothing2AtS (_s : Store) (d : Triple) : Bool :=
  d.p == rdfType && d.o == Term.iri owlNothing

def clsComAtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlComplementOf then
    (s.withPredObj rdfType d.s.toTerm).any (fun u =>
      s.memB ⟨u.s, rdfType, d.o⟩)
  else false

def clsMaxc1AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlMaxCardinality && d.o == Term.literal litNni0 then
    (s.withSubjPred d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (s.withPredObj rdfType d.s.toTerm).any (fun tu =>
          !(s.withSubjPred tu.s p).isEmpty)))
  else false

def clsMaxqc1AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni0 then
    (s.withSubjPred d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (s.withSubjPred d.s owlOnClass).any (fun onc =>
          (s.withPredObj rdfType d.s.toTerm).any (fun tu =>
            (s.withSubjPred tu.s p).any (fun u =>
              (asSubject u.o).any (fun ys =>
                s.memB ⟨ys, rdfType, onc.o⟩))))))
  else false

def clsMaxqc2AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni0 then
    (s.withSubjPred d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (s.withSubjPred d.s owlOnClass).any (fun onc =>
          onc.o == Term.iri owlThing &&
          (s.withPredObj rdfType d.s.toTerm).any (fun tu =>
            !(s.withSubjPred tu.s p).isEmpty))))
  else false

def caxDwAtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlDisjointWith then
    (s.withPredObj rdfType d.s.toTerm).any (fun u =>
      s.memB ⟨u.s, rdfType, d.o⟩)
  else false

def caxAdcAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointClasses then
    (s.withSubjPred d.s owlMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (s.withPredObj rdfType fi.o).any (fun u =>
                s.memB ⟨u.s, rdfType, fj.o⟩))))))
  else false

def eqDiff2AtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDifferent then
    (s.withSubjPred d.s owlMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asSubject fi.o).any (fun zs =>
                s.memB ⟨zs, owlSameAs, fj.o⟩))))))
  else false

def eqDiff3AtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDifferent then
    (s.withSubjPred d.s owlDistinctMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asSubject fi.o).any (fun zs =>
                s.memB ⟨zs, owlSameAs, fj.o⟩))))))
  else false

def prpAdpAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointProperties then
    (s.withSubjPred d.s owlMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asIri fi.o).any (fun p1 =>
                (asIri fj.o).any (fun p2 =>
                  (s.withPred p1).any (fun u =>
                    s.memB ⟨u.s, p2, u.o⟩))))))))
  else false

def clashRowsS (s : Store) (d : Triple) : List Bool :=
  [ eqDiff1AtS s d, prpIrpAtS s d, prpAsypAtS s d, prpPdwAtS s d,
    prpNpa1AtS s d, prpNpa2AtS s d, clsNothing2AtS s d, clsComAtS s d,
    clsMaxc1AtS s d, clsMaxqc1AtS s d, clsMaxqc2AtS s d,
    caxDwAtS s d, caxAdcAtS s d,
    eqDiff2AtS s d, eqDiff3AtS s d, prpAdpAtS s d ]

def clashFromS (s : Store) (d : Triple) : Bool :=
  (clashRowsS s d).any (fun b => b)

def detectClashS (s : Store) : Bool :=
  s.graph.any (fun d => clashFromS s d)

/-- The clash decision over an index. -/
def detectClashI (i : Index) : Bool := detectClashS (Store.ofIndex i)

/-! ## Section 7 — the list-scan store IS `RLClosure`

Every store-parameterised function, applied to `Store.ofGraph g`, is
the `RLClosure` function. The walkers need one induction each (they
are recursive definitions, so `rfl` does not see through the
recursor); every row is then `rfl`. -/

theorem listElemsS_ofGraph (g : Graph) : listElemsS (Store.ofGraph g) = listElems g := by
  funext head n
  induction n generalizing head with
  | zero => rfl
  | succ n ih =>
    simp only [listElemsS, listElems, ih]
    rfl

theorem listCellsS_ofGraph (g : Graph) : listCellsS (Store.ofGraph g) = listCells g := by
  funext head n
  induction n generalizing head with
  | zero => rfl
  | succ n ih =>
    simp only [listCellsS, listCells, ih]
    rfl

theorem listSeqsS_ofGraph (g : Graph) : listSeqsS (Store.ofGraph g) = listSeqs g := by
  funext head n
  induction n generalizing head with
  | zero => rfl
  | succ n ih =>
    simp only [listSeqsS, listSeqs, ih]
    rfl

theorem typesAllBS_ofGraph (g : Graph) : typesAllBS (Store.ofGraph g) = typesAllB g := rfl

theorem sharesKeyValuesBS_ofGraph (g : Graph) :
    sharesKeyValuesBS (Store.ofGraph g) = sharesKeyValuesB g := rfl

theorem chainTargetsS_ofGraph (g : Graph) :
    chainTargetsS (Store.ofGraph g) = chainTargets g := by
  funext start ps
  induction ps generalizing start with
  | nil => rfl
  | cons p rest ih =>
    cases rest with
    | nil => rfl
    | cons q rest' =>
      simp only [chainTargetsS, chainTargets, ih]
      rfl

theorem eqRefSForS_ofGraph (g : Graph) : eqRefSForS (Store.ofGraph g) = eqRefSFor g := rfl
theorem eqRefPForS_ofGraph (g : Graph) : eqRefPForS (Store.ofGraph g) = eqRefPFor g := rfl
theorem eqRefOForS_ofGraph (g : Graph) : eqRefOForS (Store.ofGraph g) = eqRefOFor g := rfl
theorem eqSymForS_ofGraph (g : Graph) : eqSymForS (Store.ofGraph g) = eqSymFor g := rfl
theorem eqTransForS_ofGraph (g : Graph) : eqTransForS (Store.ofGraph g) = eqTransFor g := rfl
theorem eqRepSForS_ofGraph (g : Graph) : eqRepSForS (Store.ofGraph g) = eqRepSFor g := rfl
theorem eqRepPForS_ofGraph (g : Graph) : eqRepPForS (Store.ofGraph g) = eqRepPFor g := rfl
theorem eqRepOForS_ofGraph (g : Graph) : eqRepOForS (Store.ofGraph g) = eqRepOFor g := rfl
theorem prpDomForS_ofGraph (g : Graph) : prpDomForS (Store.ofGraph g) = prpDomFor g := rfl
theorem prpRngForS_ofGraph (g : Graph) : prpRngForS (Store.ofGraph g) = prpRngFor g := rfl
theorem prpFpForS_ofGraph (g : Graph) : prpFpForS (Store.ofGraph g) = prpFpFor g := rfl
theorem prpIfpForS_ofGraph (g : Graph) : prpIfpForS (Store.ofGraph g) = prpIfpFor g := rfl
theorem prpSympForS_ofGraph (g : Graph) : prpSympForS (Store.ofGraph g) = prpSympFor g := rfl
theorem prpTrpForS_ofGraph (g : Graph) : prpTrpForS (Store.ofGraph g) = prpTrpFor g := rfl
theorem prpSpo1ForS_ofGraph (g : Graph) : prpSpo1ForS (Store.ofGraph g) = prpSpo1For g := rfl
theorem prpSpo2ForS_ofGraph (g : Graph) : prpSpo2ForS (Store.ofGraph g) = prpSpo2For g := by
  funext d
  unfold prpSpo2ForS prpSpo2For
  rw [listSeqsS_ofGraph, chainTargetsS_ofGraph]
  rfl
theorem prpEqp1ForS_ofGraph (g : Graph) : prpEqp1ForS (Store.ofGraph g) = prpEqp1For g := rfl
theorem prpEqp2ForS_ofGraph (g : Graph) : prpEqp2ForS (Store.ofGraph g) = prpEqp2For g := rfl
theorem prpInv1ForS_ofGraph (g : Graph) : prpInv1ForS (Store.ofGraph g) = prpInv1For g := rfl
theorem prpInv2ForS_ofGraph (g : Graph) : prpInv2ForS (Store.ofGraph g) = prpInv2For g := rfl
theorem prpKeyForS_ofGraph (g : Graph) : prpKeyForS (Store.ofGraph g) = prpKeyFor g := by
  funext d
  unfold prpKeyForS prpKeyFor
  rw [listSeqsS_ofGraph, sharesKeyValuesBS_ofGraph]
  rfl
theorem clsInt1ForS_ofGraph (g : Graph) : clsInt1ForS (Store.ofGraph g) = clsInt1For g := by
  funext d
  unfold clsInt1ForS clsInt1For
  rw [listSeqsS_ofGraph, typesAllBS_ofGraph]
  rfl
theorem clsInt2ForS_ofGraph (g : Graph) : clsInt2ForS (Store.ofGraph g) = clsInt2For g := by
  funext d
  unfold clsInt2ForS clsInt2For
  rw [listElemsS_ofGraph]
  rfl
theorem clsUniForS_ofGraph (g : Graph) : clsUniForS (Store.ofGraph g) = clsUniFor g := by
  funext d
  unfold clsUniForS clsUniFor
  rw [listElemsS_ofGraph]
  rfl
theorem clsSvf1ForS_ofGraph (g : Graph) : clsSvf1ForS (Store.ofGraph g) = clsSvf1For g := rfl
theorem clsSvf2ForS_ofGraph (g : Graph) : clsSvf2ForS (Store.ofGraph g) = clsSvf2For g := rfl
theorem clsAvfForS_ofGraph (g : Graph) : clsAvfForS (Store.ofGraph g) = clsAvfFor g := rfl
theorem clsHv1ForS_ofGraph (g : Graph) : clsHv1ForS (Store.ofGraph g) = clsHv1For g := rfl
theorem clsHv2ForS_ofGraph (g : Graph) : clsHv2ForS (Store.ofGraph g) = clsHv2For g := rfl
theorem clsHs1ForS_ofGraph (g : Graph) : clsHs1ForS (Store.ofGraph g) = clsHs1For g := rfl
theorem clsHs2ForS_ofGraph (g : Graph) : clsHs2ForS (Store.ofGraph g) = clsHs2For g := rfl
theorem clsMaxc2ForS_ofGraph (g : Graph) : clsMaxc2ForS (Store.ofGraph g) = clsMaxc2For g := rfl
theorem clsOoForS_ofGraph (g : Graph) : clsOoForS (Store.ofGraph g) = clsOoFor g := by
  funext d
  unfold clsOoForS clsOoFor
  rw [listElemsS_ofGraph]
  rfl
theorem caxScoForS_ofGraph (g : Graph) : caxScoForS (Store.ofGraph g) = caxScoFor g := rfl
theorem caxEqc1ForS_ofGraph (g : Graph) : caxEqc1ForS (Store.ofGraph g) = caxEqc1For g := rfl
theorem caxEqc2ForS_ofGraph (g : Graph) : caxEqc2ForS (Store.ofGraph g) = caxEqc2For g := rfl
theorem scmClsForS_ofGraph (g : Graph) : scmClsForS (Store.ofGraph g) = scmClsFor g := rfl
theorem scmScoForS_ofGraph (g : Graph) : scmScoForS (Store.ofGraph g) = scmScoFor g := rfl
theorem scmEqc1ForS_ofGraph (g : Graph) : scmEqc1ForS (Store.ofGraph g) = scmEqc1For g := rfl
theorem scmEqc2ForS_ofGraph (g : Graph) : scmEqc2ForS (Store.ofGraph g) = scmEqc2For g := rfl
theorem scmSpoForS_ofGraph (g : Graph) : scmSpoForS (Store.ofGraph g) = scmSpoFor g := rfl
theorem scmEqp1ForS_ofGraph (g : Graph) : scmEqp1ForS (Store.ofGraph g) = scmEqp1For g := rfl
theorem scmEqp2ForS_ofGraph (g : Graph) : scmEqp2ForS (Store.ofGraph g) = scmEqp2For g := rfl
theorem scmDom1ForS_ofGraph (g : Graph) : scmDom1ForS (Store.ofGraph g) = scmDom1For g := rfl
theorem scmDom2ForS_ofGraph (g : Graph) : scmDom2ForS (Store.ofGraph g) = scmDom2For g := rfl
theorem scmRng1ForS_ofGraph (g : Graph) : scmRng1ForS (Store.ofGraph g) = scmRng1For g := rfl
theorem scmRng2ForS_ofGraph (g : Graph) : scmRng2ForS (Store.ofGraph g) = scmRng2For g := rfl
theorem scmOpForS_ofGraph (g : Graph) :
    scmOpForS (Store.ofGraph g) = scmOpFor g := by
  funext d
  unfold scmOpForS scmOpFor
  rfl

theorem scmDpForS_ofGraph (g : Graph) :
    scmDpForS (Store.ofGraph g) = scmDpFor g := by
  funext d
  unfold scmDpForS scmDpFor
  rfl

theorem scmIntForS_ofGraph (g : Graph) : scmIntForS (Store.ofGraph g) = scmIntFor g := by
  funext d
  unfold scmIntForS scmIntFor
  rw [listElemsS_ofGraph]
  rfl
theorem scmUniForS_ofGraph (g : Graph) : scmUniForS (Store.ofGraph g) = scmUniFor g := by
  funext d
  unfold scmUniForS scmUniFor
  rw [listElemsS_ofGraph]
  rfl

-- The `[ext]` rows. Only the two that call a recursive walker
-- (`chainToTrans` through `listSeqsS`) or read `s.graph` through a
-- helper (`prpRfl` through `iriIndividuals`) need more than `rfl`.
theorem eqDiffSymForS_ofGraph (g : Graph) :
    eqDiffSymForS (Store.ofGraph g) = eqDiffSymFor g := rfl
theorem pdwToDiffForS_ofGraph (g : Graph) :
    pdwToDiffForS (Store.ofGraph g) = pdwToDiffFor g := rfl
theorem caxDwToDiffForS_ofGraph (g : Graph) :
    caxDwToDiffForS (Store.ofGraph g) = caxDwToDiffFor g := rfl
theorem fpDiffToDiffForS_ofGraph (g : Graph) :
    fpDiffToDiffForS (Store.ofGraph g) = fpDiffToDiffFor g := rfl
theorem ifpDiffToDiffForS_ofGraph (g : Graph) :
    ifpDiffToDiffForS (Store.ofGraph g) = ifpDiffToDiffFor g := rfl
theorem chainToTransForS_ofGraph (g : Graph) :
    chainToTransForS (Store.ofGraph g) = chainToTransFor g := by
  funext d
  unfold chainToTransForS chainToTransFor
  rw [listSeqsS_ofGraph]
  rfl
theorem prpRflForS_ofGraph (g : Graph) :
    prpRflForS (Store.ofGraph g) = prpRflFor g := rfl
theorem xsdAxiomsForS_ofGraph (g : Graph) :
    xsdAxiomsForS (Store.ofGraph g) = xsdAxiomsFor g := rfl
theorem dtRangeIntersectForS_ofGraph (g : Graph) :
    dtRangeIntersectForS (Store.ofGraph g) = dtRangeIntersectFor g := rfl
theorem caxDwToComplementForS_ofGraph (g : Graph) :
    caxDwToComplementForS (Store.ofGraph g) = caxDwToComplementFor g := rfl
theorem clsMaxqc1ToComplementForS_ofGraph (g : Graph) :
    clsMaxqc1ToComplementForS (Store.ofGraph g) = clsMaxqc1ToComplementFor g := rfl
theorem minCard1ComprehensionForS_ofGraph (g : Graph) :
    minCard1ComprehensionForS (Store.ofGraph g) = minCard1ComprehensionFor g := rfl
theorem inverseOfDomRngFlipForS_ofGraph (g : Graph) :
    inverseOfDomRngFlipForS (Store.ofGraph g) = inverseOfDomRngFlipFor g := rfl
theorem caxAdcToDwForS_ofGraph (g : Graph) :
    caxAdcToDwForS (Store.ofGraph g) = caxAdcToDwFor g := by
  funext d
  unfold caxAdcToDwForS caxAdcToDwFor
  rw [listElemsS_ofGraph]
  rfl

/-- A round's conclusion list over the list-scan store is
`RLClosure.conclusionsFrom`. -/
theorem conclusionsFromS_ofGraph (g : Graph) :
    conclusionsFromS (Store.ofGraph g) = conclusionsFrom g := by
  funext d
  simp only [conclusionsFromS, conclusionsFrom, conclusionsListS, conclusionsList,
    eqRefSForS_ofGraph, eqRefPForS_ofGraph, eqRefOForS_ofGraph,
    eqSymForS_ofGraph, eqTransForS_ofGraph,
    eqRepSForS_ofGraph, eqRepPForS_ofGraph, eqRepOForS_ofGraph,
    prpDomForS_ofGraph, prpRngForS_ofGraph, prpFpForS_ofGraph, prpIfpForS_ofGraph,
    prpSympForS_ofGraph, prpTrpForS_ofGraph, prpSpo1ForS_ofGraph, prpSpo2ForS_ofGraph,
    prpEqp1ForS_ofGraph, prpEqp2ForS_ofGraph, prpInv1ForS_ofGraph, prpInv2ForS_ofGraph,
    prpKeyForS_ofGraph,
    clsInt1ForS_ofGraph, clsInt2ForS_ofGraph, clsUniForS_ofGraph,
    clsSvf1ForS_ofGraph, clsSvf2ForS_ofGraph, clsAvfForS_ofGraph,
    clsHv1ForS_ofGraph, clsHv2ForS_ofGraph, clsHs1ForS_ofGraph, clsHs2ForS_ofGraph,
    clsMaxc2ForS_ofGraph, clsOoForS_ofGraph,
    caxScoForS_ofGraph, caxEqc1ForS_ofGraph, caxEqc2ForS_ofGraph,
    scmClsForS_ofGraph, scmScoForS_ofGraph, scmEqc1ForS_ofGraph, scmEqc2ForS_ofGraph,
    scmSpoForS_ofGraph, scmEqp1ForS_ofGraph, scmEqp2ForS_ofGraph,
    scmDom1ForS_ofGraph, scmDom2ForS_ofGraph, scmRng1ForS_ofGraph, scmRng2ForS_ofGraph,
    scmOpForS_ofGraph, scmDpForS_ofGraph,
    scmIntForS_ofGraph, scmUniForS_ofGraph,
    eqDiffSymForS_ofGraph, pdwToDiffForS_ofGraph, caxDwToDiffForS_ofGraph,
    fpDiffToDiffForS_ofGraph, ifpDiffToDiffForS_ofGraph,
    chainToTransForS_ofGraph, prpRflForS_ofGraph,
    xsdAxiomsForS_ofGraph, dtRangeIntersectForS_ofGraph,
    caxDwToComplementForS_ofGraph, clsMaxqc1ToComplementForS_ofGraph,
    minCard1ComprehensionForS_ofGraph, caxAdcToDwForS_ofGraph,
    inverseOfDomRngFlipForS_ofGraph]

theorem stepConclusionsS_ofGraph (g : Graph) :
    stepConclusionsS (Store.ofGraph g) = stepConclusions g := by
  unfold stepConclusionsS stepConclusions
  rw [conclusionsFromS_ofGraph]
  rfl

theorem caxAdcAtS_ofGraph (g : Graph) : caxAdcAtS (Store.ofGraph g) = caxAdcAt g := by
  funext d
  unfold caxAdcAtS caxAdcAt
  rw [listCellsS_ofGraph]
  rfl

theorem eqDiff2AtS_ofGraph (g : Graph) :
    eqDiff2AtS (Store.ofGraph g) = eqDiff2At g := by
  funext d
  unfold eqDiff2AtS eqDiff2At
  rw [listCellsS_ofGraph]
  rfl

theorem eqDiff3AtS_ofGraph (g : Graph) :
    eqDiff3AtS (Store.ofGraph g) = eqDiff3At g := by
  funext d
  unfold eqDiff3AtS eqDiff3At
  rw [listCellsS_ofGraph]
  rfl

theorem prpAdpAtS_ofGraph (g : Graph) :
    prpAdpAtS (Store.ofGraph g) = prpAdpAt g := by
  funext d
  unfold prpAdpAtS prpAdpAt
  rw [listCellsS_ofGraph]
  rfl

theorem clashFromS_ofGraph (g : Graph) : clashFromS (Store.ofGraph g) = clashFrom g := by
  funext d
  simp only [clashFromS, clashFrom, clashRowsS, clashRows, caxAdcAtS_ofGraph,
    eqDiff2AtS_ofGraph, eqDiff3AtS_ofGraph, prpAdpAtS_ofGraph]
  rfl

theorem detectClashS_ofGraph (g : Graph) : detectClashS (Store.ofGraph g) = detectClash g := by
  unfold detectClashS detectClash
  rw [clashFromS_ofGraph]
  rfl

/-! ## Section 8 — the index is a faithful picture of a list

`Index.Wf i g`: every component of `i` agrees with the list
functions on `g`, bucket lookups as LISTS (same order). -/

/-- A bucket map keyed by `key` holds, under each key, the reversed
filter of `g` for that key. -/
def BucketWf {κ : Type} [BEq κ] [Hashable κ]
    (m : Std.HashMap κ (List Triple)) (key : Triple → κ) (g : Graph) : Prop :=
  ∀ k, (m.getD k []).reverse = g.filter (fun u => key u == k)

theorem BucketWf.empty {κ : Type} [BEq κ] [Hashable κ] (key : Triple → κ) :
    BucketWf (∅ : Std.HashMap κ (List Triple)) key [] := by
  intro k
  simp [Std.HashMap.getD_empty]

theorem BucketWf.push {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]
    {m : Std.HashMap κ (List Triple)} {key : Triple → κ} {g : Graph}
    (h : BucketWf m key g) (t : Triple) :
    BucketWf (m.insert (key t) (t :: m.getD (key t) [])) key (g ++ [t]) := by
  intro k
  rw [Std.HashMap.getD_insert, List.filter_append]
  have hk := h k
  by_cases hkt : key t = k
  · subst hkt
    simp [hk]
  · have hb : (key t == k) = false := by simpa using hkt
    simp [hb, hk]

structure Index.Wf (i : Index) (g : Graph) : Prop where
  all  : i.all.toList = g
  mem  : ∀ t, i.memB t = RL.memB g t
  byS  : BucketWf i.byS (fun u => u.s) g
  byP  : BucketWf i.byP (fun u => u.p) g
  byO  : BucketWf i.byO (fun u => u.o) g
  bySP : BucketWf i.bySP (fun u => (u.s, u.p)) g
  byPO : BucketWf i.byPO (fun u => (u.p, u.o)) g

namespace Index

theorem Wf.empty : Wf empty [] :=
  { all := rfl,
    mem := fun t => by simp [Index.memB, Index.empty, RL.memB],
    byS := BucketWf.empty _, byP := BucketWf.empty _, byO := BucketWf.empty _,
    bySP := BucketWf.empty _, byPO := BucketWf.empty _ }

theorem memB_append_single (g : Graph) (t u : Triple) :
    RL.memB (g ++ [t]) u = (RL.memB g u || t == u) := by
  simp only [RL.memB, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem Wf.push {i : Index} {g : Graph} (h : Wf i g) (t : Triple) :
    Wf (i.push t) (g ++ [t]) :=
  { all := by simp [Index.push, h.all],
    mem := fun u => by
      simp only [Index.memB, Index.push, Std.HashSet.contains_insert, memB_append_single]
      rw [← h.mem u, Index.memB]
      exact Bool.or_comm _ _,
    byS := h.byS.push t, byP := h.byP.push t, byO := h.byO.push t,
    bySP := h.bySP.push t, byPO := h.byPO.push t }

theorem Wf.pushAll (ts : List Triple) :
    ∀ {i : Index} {g : Graph}, Wf i g → Wf (i.pushAll ts) (g ++ ts) := by
  induction ts with
  | nil => intro i g h; simpa [Index.pushAll] using h
  | cons t ts ih =>
    intro i g h
    simp only [Index.pushAll]
    have := ih (h.push t)
    simpa [List.append_assoc] using this

theorem Wf.ofGraph (g : Graph) : Wf (ofGraph g) g := by
  have := Wf.pushAll g Wf.empty
  simpa [Index.ofGraph] using this

theorem Wf.insert {i : Index} {g : Graph} (h : Wf i g) (t : Triple) :
    Wf (i.insert t) (addOne g t) := by
  unfold Index.insert addOne
  rw [h.mem t]
  split
  · exact h
  · exact h.push t

theorem Wf.insertAll (ts : List Triple) :
    ∀ {i : Index} {g : Graph}, Wf i g → Wf (i.insertAll ts) (addAll g ts) := by
  induction ts with
  | nil => intro i g h; exact h
  | cons t ts ih =>
    intro i g h
    simp only [Index.insertAll, addAll]
    exact ih (h.insert t)

/-- The lookups of a well-formed index ARE the list lookups. -/
theorem Wf.withSubj_eq {i : Index} {g : Graph} (h : Wf i g) (s : Subject) :
    i.withSubj s = RL.withSubj g s := h.byS s

theorem Wf.withPred_eq {i : Index} {g : Graph} (h : Wf i g) (p : WfIri) :
    i.withPred p = RL.withPred g p := h.byP p

theorem Wf.withObj_eq {i : Index} {g : Graph} (h : Wf i g) (o : Term) :
    i.withObj o = RL.withObj g o := h.byO o

theorem Wf.withSubjPred_eq {i : Index} {g : Graph} (h : Wf i g) (s : Subject) (p : WfIri) :
    i.withSubjPred s p = RL.withSubjPred g s p := by
  rw [Index.withSubjPred, h.bySP (s, p), RL.withSubjPred]
  -- `(u.s, u.p) == (s, p)` is the conjunction the list filter tests.
  refine List.filter_congr (fun u _ => ?_)
  rw [Bool.eq_iff_iff]
  simp [beq_iff_eq, Bool.and_eq_true, Prod.mk.injEq, Subtype.ext_iff]

theorem Wf.withPredObj_eq {i : Index} {g : Graph} (h : Wf i g) (p : WfIri) (o : Term) :
    i.withPredObj p o = RL.withPredObj g p o := by
  rw [Index.withPredObj, h.byPO (p, o), RL.withPredObj]
  refine List.filter_congr (fun u _ => ?_)
  rw [Bool.eq_iff_iff]
  simp [beq_iff_eq, Bool.and_eq_true, Prod.mk.injEq, Subtype.ext_iff]

end Index

/-- **The store bridge.** Over a well-formed index, the hash-lookup
store is the list-scan store — as a value, so every row, round and
clash function agrees on the two by rewriting. -/
theorem Store.ofIndex_eq {i : Index} {g : Graph} (h : i.Wf g) :
    Store.ofIndex i = Store.ofGraph g := by
  simp only [Store.ofIndex, Store.ofGraph, Store.mk.injEq, Index.toGraph]
  exact ⟨h.all, funext h.withPred_eq, funext h.withSubj_eq, funext h.withObj_eq,
    funext (fun s => funext (h.withSubjPred_eq s)),
    funext (fun p => funext (h.withPredObj_eq p)),
    funext h.mem⟩

/-! ## Section 9 — the bridge theorems -/

/-- One indexed round pictures one list round. -/
theorem Index.Wf.step {i : Index} {g : Graph} (h : i.Wf g) : (stepI i).Wf (RL.step g) := by
  unfold stepI RL.step
  rw [Store.ofIndex_eq h, stepConclusionsS_ofGraph]
  exact h.insertAll _

/-- The indexed loop pictures the list loop at every fuel: both take
the same branch at every round. -/
theorem Index.Wf.closure (fuel : Nat) :
    ∀ {i : Index} {g : Graph}, i.Wf g → (closureI i fuel).Wf (RL.closure g fuel) := by
  induction fuel with
  | zero => intro i g h; exact h
  | succ n ih =>
    intro i g h
    simp only [closureI, RL.closure]
    have hs : (stepI i).all.size = (RL.step g).length := by
      rw [← Array.length_toList, h.step.all]
    have hi : i.all.size = g.length := by
      rw [← Array.length_toList, h.all]
    rw [hs, hi]
    split
    · exact h
    · exact ih h.step

/-- **The bridge.** The indexed closure is the list closure — as a
LIST, at every fuel. -/
theorem indexedClosure_eq (g : Graph) (fuel : Nat) :
    indexedClosure g fuel = closure g fuel :=
  (Index.Wf.closure fuel (Index.Wf.ofGraph g)).all

/-- Set-membership form of the bridge. -/
theorem mem_indexedClosure_iff (g : Graph) (fuel : Nat) (t : Triple) :
    t ∈ indexedClosure g fuel ↔ t ∈ closure g fuel := by
  rw [indexedClosure_eq]

/-- The clash verdict over the index is the clash verdict over the
list it pictures. -/
theorem detectClashI_eq {i : Index} {g : Graph} (h : i.Wf g) :
    detectClashI i = detectClash g := by
  rw [detectClashI, Store.ofIndex_eq h, detectClashS_ofGraph]

/-- The indexed consistency check is `RLClosure.inconsistent`. -/
theorem detectClashI_closureI (g : Graph) (fuel : Nat) :
    detectClashI (closureI (Index.ofGraph g) fuel) = inconsistent g fuel :=
  detectClashI_eq (Index.Wf.closure fuel (Index.Wf.ofGraph g))

end L4Factoidal.OWL.RL
