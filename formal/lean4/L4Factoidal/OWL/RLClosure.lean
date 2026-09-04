/-
L4Factoidal.OWL.RLClosure — the EXECUTABLE OWL 2 RL/RDF closure.

Port of the extractable part of `formal/fstar/OWL.Closure.fsti`: the
`owl_rule_*` Datalog-shaped rule bodies, the `owl_rl_closure_step` /
`owl_rl_closure` fuel loop, and the `is_inconsistent` clash checker.
`RLRules.lean` is the specification; `RLTheorems.lean` connects them.

## Which F* engine rules this file ports, and which it does not

`OWL.Closure.fsti` holds 77 `owl_rule_*` functions. Its own ledger
(transcribed into `OWL.RL.Spec.fst`, landing 4) classifies each one:

* `[row]` — implements a named W3C table row. **This file ports the
  `[row]` rules**, listed in `RLRules.lean`'s header, plus the Table 4
  / Table 6 / Table 8 rows the F* engine gets from the layer BELOW it
  rather than from an `owl_rule_*` of its own. That layering is real:
  `owl_rl_closure_step_mode` runs on top of
  `owl_rdfs_closure_with_reflexivity` from `RDFS.Closure`, so prp-dom,
  prp-rng, prp-spo1, cax-sco, scm-sco and scm-spo reach the F* engine
  as rdfs2, rdfs3, rdfs7, rdfs9, rdfs11 and rdfs5. This port has no
  layering: it names those rows directly, under the OWL table ids the
  Recommendation gives them.

* `[ext]` — a sound EXTENSION with no table row. **Fourteen of them
  are ported**, in the `[ext]` block of Section 5: the
  differentFrom-synthesis family, the chain and reflexivity bridges,
  Table 7's datatype rows over the XSD map, and four
  comprehension-witness rows. Each cites the OWL 2 RDF-Based Semantics
  condition it rests on in `RLRules.lean` instead of a table id. NOT
  ported: `cls_hasself*`, `svf2_existential_witness`, the `#236`
  `cls_maxqc_comp` anchor machinery, and any witness needing a skolem
  LIST rather than a single skolem node.

* `[axm]` — materialises an axiomatic-triple table (`xsd_datatype_axioms`,
  `builtin_vocabulary_axioms`, the owl:Thing/owl:Nothing group).
  **Ported**: cls-thing and cls-nothing1 plus the two premise-free
  `rdfs:Datatype` typings are `axiomTriples`; the XSD numeric tower is
  the guarded `xsdAxiomsFor` row. `RDF/Datatypes.lean` supplies the
  datatype map, and `RLRules.lean` records which value-space facts are
  discharged against it and which are carried as an assumption.

* `[mode]` — fires only under a catalog semantics mode
  (`named_equivClass_to_sameAs_mode`, the RDF-Based full meta axioms).
  **NOT ported**: there are no semantics modes on the Lean side.

Two further gaps worth naming rather than leaving to inference:

* `cls-svf1` is ported here but the F* engine ledger names no
  `owl_rule_cls_svf1`. The engine reaches that row's effect through
  `cls_svf2_qualified` and the comprehension-witness rules instead.
  This file implements the row as the Recommendation writes it.
* `cls-maxqc3`/`cls-maxqc4` (the qualified-cardinality DERIVING rows,
  F* `owl_rule_cls_maxqc34`) are not ported; their two CLASH siblings
  cls-maxqc1 and cls-maxqc2 are.

## Three port decisions

1. **Deduplication is EXACT, not `Triple.eqb`.** `RDFS/Closure.lean`
   folds `Graph.add`, whose membership test is the engine's coarse
   `Triple.eqb` (case-folded language tags, `rdf:XMLLiteral`
   canonical-XML equality). This file folds `addOne`, which tests
   propositional equality. Two consequences, both wanted: an RDF graph
   is a SET OF TRIPLES under term identity (RDF 1.1 Concepts §3), which
   is what exact dedup implements; and every theorem in
   `RLTheorems.lean` is then stated in ONE membership relation
   (`t ∈ closure g fuel`) in both directions, instead of the
   list-membership/`Graph.mem` asymmetry the coarse test forces on the
   rdfs-core proofs. The cost is that two triples differing only by
   language-tag case both survive a round, where the F* engine would
   keep one.

2. **Every premise is read from the round's INPUT snapshot.** The F*
   step threads its accumulator through the rules, so a triple emitted
   early in a round can drive a later rule in the SAME round. Here each
   round is a plain function of its input. Per round this emits less;
   at the fixpoint it emits the same set, because the loop runs to
   saturation. Same deviation, same reasoning, as `RDFS/Closure.lean`.

3. **RDF collections are walked under a fuel bound.** `listElems`
   (members) and `listSeqs` (the whole sequence) both take fuel, and
   the rules pass `listFuel g = g.length + 1` — a chain longer than the
   graph would have to reuse a cell. Cyclic chains therefore terminate
   with a partial answer instead of diverging. `listSeqs` additionally
   refuses a chain that does not end at `rdf:nil`, which is the F*
   `owl_list_denotes` behaviour.
-/
import L4Factoidal.OWL.RLRules

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## Section 1 — set-wise insertion with EXACT equality -/

/-- Exact membership as a `Bool`. -/
def memB (g : Graph) (t : Triple) : Bool := g.any (fun u => u == t)

/-- Add a triple unless the graph already holds it — exactly. -/
def addOne (g : Graph) (t : Triple) : Graph :=
  if memB g t then g else g ++ [t]

/-- Add a list of triples set-wise. -/
def addAll (g : Graph) : List Triple → Graph
  | []      => g
  | t :: ts => addAll (addOne g t) ts

/-! ## Section 2 — premise lookup

The F* rules read premises through `RDF.Indexed`'s bucket trees. The
index is performance machinery; the specification-level lookup is a
list scan with the same answer. -/

/-- Triples of `g` with the given predicate. -/
def withPred (g : Graph) (p : WfIri) : List Triple :=
  g.filter (fun u => u.p == p)

/-- Triples of `g` with the given subject. -/
def withSubj (g : Graph) (s : Subject) : List Triple :=
  g.filter (fun u => u.s == s)

/-- Triples of `g` with the given object. -/
def withObj (g : Graph) (o : Term) : List Triple :=
  g.filter (fun u => u.o == o)

/-- Triples of `g` with the given subject and predicate. -/
def withSubjPred (g : Graph) (s : Subject) (p : WfIri) : List Triple :=
  g.filter (fun u => u.s == s && u.p == p)

/-- Triples of `g` with the given predicate and object. -/
def withPredObj (g : Graph) (p : WfIri) (o : Term) : List Triple :=
  g.filter (fun u => u.p == p && u.o == o)

/-- Every subject occurring in `g` — the candidate set for the rows
whose conclusion subject is not read off a premise (cls-int1,
prp-spo2). -/
def subjectsOf (g : Graph) : List Subject := g.map (fun u => u.s)

/-- A term in subject position, as a 0-or-1 element list. Turns the
table's "delta GR" side condition into something that composes with
`flatMap`. -/
def asSubject (t : Term) : List Subject :=
  match t.toSubject? with
  | some s => [s]
  | none   => []

/-- A term in predicate position ("delta GP"), as a 0-or-1 element
list. -/
def asIri : Term → List WfIri
  | .iri i => [i]
  | _      => []

/-- A subject that is an IRI, as a 0-or-1 element list. Blank nodes
cannot occupy a predicate position, so the rows whose driving premise
names a property (`T(?p, rdf:type, owl:TransitiveProperty)`, ...) drop
a blank-node subject here. -/
def subjIri : Subject → List WfIri
  | .iri i   => [i]
  | .bnode _ => []

/-! ## Section 3 — RDF collections -/

/-- Fuel for a collection walk: a chain longer than the graph has to
reuse a cell, so `g.length + 1` cannot cut a well-formed list short. -/
def listFuel (g : Graph) : Nat := g.length + 1

/-- Every member of the collection headed by `head`. Follows every
`rdf:first` and every `rdf:rest` — a malformed cell with two `rdf:rest`
values contributes both branches, which over-approximates in the same
direction the specification's `ListMember` does. -/
def listElems (g : Graph) : Term → Nat → List Term
  | _,    0     => []
  | head, n + 1 =>
      (asSubject head).flatMap (fun node =>
        (withSubjPred g node rdfFirst).map (fun u => u.o) ++
        (withSubjPred g node rdfRest).flatMap (fun r => listElems g r.o n))

/-- Every CELL of the collection headed by `head`, within the fuel:
the head itself, then every cell reachable through `rdf:rest`. The
rows that must read the table's `1 <= i < j <= n` side condition as
two distinct POSITIONS use this instead of `listElems`, because two
`rdf:first` values on ONE cell are one position, not two. -/
def listCells (g : Graph) : Term → Nat → List Subject
  | _,    0     => []
  | head, n + 1 =>
      (asSubject head).flatMap (fun node =>
        node :: (withSubjPred g node rdfRest).flatMap
          (fun r => listCells g r.o n))

/-- EVERY sequence the collection headed by `head` denotes, within the
fuel: the empty sequence for `rdf:nil`, and otherwise one answer per
`rdf:first`/`rdf:rest` reading of the head cell. A well-formed
collection yields exactly one; a chain that does not reach `rdf:nil`
inside the fuel yields none, which is the F* `owl_list_denotes`
behaviour. Returning a LIST of readings rather than picking the first
keeps the shape uniform with every other lookup here, and makes the
result exactly the extension of the `ListDenotes` relation. -/
def listSeqs (g : Graph) : Term → Nat → List (List Term)
  | _,    0     => []
  | head, n + 1 =>
    if head == Term.iri rdfNil then [[]]
    else
      (asSubject head).flatMap (fun node =>
        (withSubjPred g node rdfFirst).flatMap (fun f =>
          (withSubjPred g node rdfRest).flatMap (fun r =>
            (listSeqs g r.o n).map (fun rest => f.o :: rest))))

/-- The non-empty readings among a list of collection readings. The
rows whose table premise is `LIST[?x, ?e1, ..., ?en]` with n >= 1
(cls-int1, prp-spo2, prp-key) must not fire on an empty list. -/
def nonEmpty {a : Type} (ls : List (List a)) : List (List a) :=
  ls.filter (fun l => !l.isEmpty)

/-- Every reading of a list of terms as a list of IRIs — the
property-chain and key-property lists, whose members all occupy
predicate positions. Zero readings if any member is not an IRI. -/
def allIris : List Term → List (List WfIri)
  | []             => [[]]
  | .iri i :: rest => (allIris rest).map (fun l => i :: l)
  | _ :: _         => []

/-- cls-int1's batched premise as a decision. -/
def typesAllB (g : Graph) (y : Subject) (cs : List Term) : Bool :=
  cs.all (fun c => memB g ⟨y, rdfType, c⟩)

/-- prp-key's paired premises as a decision. -/
def sharesKeyValuesB (g : Graph) (x y : Subject) (ps : List WfIri) : Bool :=
  ps.all (fun p => (withSubjPred g x p).any (fun ux => memB g ⟨y, p, ux.o⟩))

/-- Every term prp-spo2's chain can reach from `start` along `preds`. -/
def chainTargets (g : Graph) : Subject → List WfIri → List Term
  | start, []       => [start.toTerm]
  | start, [p]      => (withSubjPred g start p).map (fun u => u.o)
  | start, p :: rest =>
      (withSubjPred g start p).flatMap (fun u =>
        (asSubject u.o).flatMap (fun mid => chainTargets g mid rest))

/-! ## Section 4 — the premise-free rows

Table 5's cls-thing and cls-nothing1 have no premises, so they are not
driven by any triple. -/

/-- **cls-thing** and **cls-nothing1**, plus the two premise-free
`rdfs:Datatype` typings and the Table 5.3 annotation-property typings
of the `premiseFreeAxiom` `[ext]` row. -/
def axiomTriples : List Triple :=
  [⟨Subject.iri owlThing, rdfType, Term.iri owlClass⟩,
   ⟨Subject.iri owlNothing, rdfType, Term.iri owlClass⟩] ++
  premiseFreeAxioms

/-! ## Section 5 — one function per row

Each `xxxFor g d` reads `d` as the row's DRIVING premise (the schema
declaration where there is one, the data triple otherwise) and returns
every conclusion that row licenses from `d` together with premises
found in `g`. -/

-- ---------------------------------------------------------------
-- Table 4, family 1: equality
-- ---------------------------------------------------------------

/-- **eq-ref**, subject conclusion. -/
def eqRefSFor (_g : Graph) (d : Triple) : List Triple :=
  [⟨d.s, owlSameAs, d.s.toTerm⟩]

/-- **eq-ref**, predicate conclusion. -/
def eqRefPFor (_g : Graph) (d : Triple) : List Triple :=
  [⟨Subject.iri d.p, owlSameAs, Term.iri d.p⟩]

/-- **eq-ref**, object conclusion (only for a subject-eligible
object). -/
def eqRefOFor (_g : Graph) (d : Triple) : List Triple :=
  (asSubject d.o).map (fun os => ⟨os, owlSameAs, os.toTerm⟩)

/-- **eq-sym**. -/
def eqSymFor (_g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).map (fun ys => ⟨ys, owlSameAs, d.s.toTerm⟩)
  else []

/-- **eq-trans**. -/
def eqTransFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).flatMap (fun ys =>
      (withSubjPred g ys owlSameAs).map (fun u => ⟨d.s, owlSameAs, u.o⟩))
  else []

/-- **eq-rep-s**. -/
def eqRepSFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).flatMap (fun s' =>
      (withSubj g d.s).map (fun u => ⟨s', u.p, u.o⟩))
  else []

/-- **eq-rep-p**. -/
def eqRepPFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (subjIri d.s).flatMap (fun p =>
        (asIri d.o).flatMap (fun p' =>
          (withPred g p).map (fun u => ⟨u.s, p', u.o⟩)))
  else []

/-- **eq-rep-o**. -/
def eqRepOFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (withObj g d.s.toTerm).map (fun u => ⟨u.s, u.p, d.o⟩)
  else []

-- ---------------------------------------------------------------
-- Table 4, family 2: property axioms
-- ---------------------------------------------------------------

/-- **prp-dom**. -/
def prpDomFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (subjIri d.s).flatMap (fun p => (withPred g p).map (fun u => ⟨u.s, rdfType, d.o⟩))
  else []

/-- **prp-rng**. -/
def prpRngFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (subjIri d.s).flatMap (fun p =>
        (withPred g p).flatMap (fun u =>
          (asSubject u.o).map (fun ys => ⟨ys, rdfType, d.o⟩)))
  else []

/-- **prp-fp**. -/
def prpFpFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlFunctionalProperty then
    (subjIri d.s).flatMap (fun p =>
        (withPred g p).flatMap (fun u1 =>
          (asSubject u1.o).flatMap (fun y1s =>
            (withSubjPred g u1.s p).map (fun u2 => ⟨y1s, owlSameAs, u2.o⟩))))
  else []

/-- **prp-ifp**. -/
def prpIfpFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlInverseFunctionalProperty then
    (subjIri d.s).flatMap (fun p =>
        (withPred g p).flatMap (fun u1 =>
          (withPredObj g p u1.o).map (fun u2 =>
            ⟨u1.s, owlSameAs, u2.s.toTerm⟩)))
  else []

/-- **prp-symp**. -/
def prpSympFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlSymmetricProperty then
    (subjIri d.s).flatMap (fun p =>
        (withPred g p).flatMap (fun u =>
          (asSubject u.o).map (fun ys => ⟨ys, p, u.s.toTerm⟩)))
  else []

/-- **prp-trp**. -/
def prpTrpFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlTransitiveProperty then
    (subjIri d.s).flatMap (fun p =>
        (withPred g p).flatMap (fun u1 =>
          (asSubject u1.o).flatMap (fun ys =>
            (withSubjPred g ys p).map (fun u2 => ⟨u1.s, p, u2.o⟩))))
  else []

/-- **prp-spo1**. -/
def prpSpo1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (withPred g p1).map (fun u => ⟨u.s, p2, u.o⟩)))
  else []

/-- **prp-spo2** — the property-chain row. -/
def prpSpo2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlPropertyChainAxiom then
    (subjIri d.s).flatMap (fun p =>
      (listSeqs g d.o (listFuel g)).flatMap (fun terms =>
        (nonEmpty (allIris terms)).flatMap (fun preds =>
          (subjectsOf g).flatMap (fun x1 =>
            (chainTargets g x1 preds).map (fun xn => ⟨x1, p, xn⟩)))))
  else []

/-- **prp-eqp1**. -/
def prpEqp1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (withPred g p1).map (fun u => ⟨u.s, p2, u.o⟩)))
  else []

/-- **prp-eqp2**. -/
def prpEqp2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (withPred g p2).map (fun u => ⟨u.s, p1, u.o⟩)))
  else []

/-- **prp-inv1**. -/
def prpInv1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (withPred g p1).flatMap (fun u =>
            (asSubject u.o).map (fun ys => ⟨ys, p2, u.s.toTerm⟩))))
  else []

/-- **Schema-level inverseOf flip** — NOT in OWL 2 RL/RDF Table 9.

If `p owl:inverseOf q` then `p rdfs:domain C` gives `q rdfs:range C`,
and `p rdfs:range C` gives `q rdfs:domain C`, in both directions.

Sound under both OWL 2 Direct and RDF-Based Semantics, because the
extension of an inverse property pair is the transposition of each
other's. Without it the closure derives the INSTANCE-level consequences
(prp-inv with prp-dom and prp-rng) but not the schema triple itself, so
`SELECT ?C WHERE { :parent rdfs:range ?C }` sees only scm-op's
`owl:Thing` and misses the transposed data-domain class. W3C SPARQL
entailment `sparqldl-11` ("domain test") is what catches that.

Port of `OWL.Closure.fsti`'s `owl_rule_inverseOf_domain_range_flip`.
Driven by the `owl:inverseOf` declaration, like prp-inv1 and prp-inv2
above. -/
def inverseOfDomRngFlipFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        g.flatMap (fun t =>
          match t.s, t.o with
          | .iri srcP, .iri c =>
              if      srcP == p1 && t.p == rdfsDomain then [(⟨.iri p2, rdfsRange, .iri c⟩ : Triple)]
              else if srcP == p1 && t.p == rdfsRange  then [(⟨.iri p2, rdfsDomain, .iri c⟩ : Triple)]
              else if srcP == p2 && t.p == rdfsDomain then [(⟨.iri p1, rdfsRange, .iri c⟩ : Triple)]
              else if srcP == p2 && t.p == rdfsRange  then [(⟨.iri p1, rdfsDomain, .iri c⟩ : Triple)]
              else []
          | _, _ => [])))
  else []

/-- **prp-inv2**. -/
def prpInv2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (withPred g p2).flatMap (fun u =>
            (asSubject u.o).map (fun ys => ⟨ys, p1, u.s.toTerm⟩))))
  else []

/-- **prp-key**. -/
def prpKeyFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlHasKey then
    (listSeqs g d.o (listFuel g)).flatMap (fun terms =>
      (nonEmpty (allIris terms)).flatMap (fun preds =>
        (withPredObj g rdfType d.s.toTerm).flatMap (fun tx =>
          (withPredObj g rdfType d.s.toTerm).flatMap (fun ty =>
            if sharesKeyValuesB g tx.s ty.s preds
            then [⟨tx.s, owlSameAs, ty.s.toTerm⟩] else []))))
  else []

-- ---------------------------------------------------------------
-- Table 5: classes
-- ---------------------------------------------------------------

/-- **cls-int1**. -/
def clsInt1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (nonEmpty (listSeqs g d.o (listFuel g))).flatMap (fun cs =>
      (subjectsOf g).flatMap (fun y =>
        if typesAllB g y cs then [⟨y, rdfType, d.s.toTerm⟩] else []))
  else []

/-- **cls-int2**. -/
def clsInt2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (listElems g d.o (listFuel g)).flatMap (fun ci =>
      (withPredObj g rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, ci⟩))
  else []

/-- **cls-uni**. -/
def clsUniFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlUnionOf then
    (listElems g d.o (listFuel g)).flatMap (fun ci =>
      (withPredObj g rdfType ci).map (fun u =>
        ⟨u.s, rdfType, d.s.toTerm⟩))
  else []

/-- **cls-svf1**. -/
def clsSvf1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPred g p).flatMap (fun u =>
          (asSubject u.o).flatMap (fun vs =>
            if memB g ⟨vs, rdfType, d.o⟩
            then [⟨u.s, rdfType, d.s.toTerm⟩] else []))))
  else []

/-- **cls-svf2**. -/
def clsSvf2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom && d.o == Term.iri owlThing then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPred g p).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)))
  else []

/-- **cls-avf**. -/
def clsAvfFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlAllValuesFrom then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPredObj g rdfType d.s.toTerm).flatMap (fun tu =>
          (withSubjPred g tu.s p).flatMap (fun u =>
            (asSubject u.o).map (fun vs => ⟨vs, rdfType, d.o⟩)))))
  else []

/-- **cls-hv1**. -/
def clsHv1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlHasValue then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPredObj g rdfType d.s.toTerm).map (fun tu => ⟨tu.s, p, d.o⟩)))
  else []

/-- **cls-hv2**. -/
def clsHv2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlHasValue then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPredObj g p d.o).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)))
  else []

/-- **cls-hs1**. -/
def clsHs1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlHasSelf && d.o == Term.literal litTrueBoolean then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPredObj g rdfType d.s.toTerm).map (fun tu =>
          ⟨tu.s, p, tu.s.toTerm⟩)))
  else []

/-- **cls-hs2**. -/
def clsHs2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlHasSelf && d.o == Term.literal litTrueBoolean then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPred g p).flatMap (fun u =>
          if u.o == u.s.toTerm then [⟨u.s, rdfType, d.s.toTerm⟩] else [])))
  else []

/-- **cls-maxc2**. -/
def clsMaxc2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlMaxCardinality && d.o == Term.literal litNni1 then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withPredObj g rdfType d.s.toTerm).flatMap (fun tu =>
          (withSubjPred g tu.s p).flatMap (fun u1 =>
            (asSubject u1.o).flatMap (fun y1s =>
              (withSubjPred g tu.s p).map (fun u2 =>
                ⟨y1s, owlSameAs, u2.o⟩))))))
  else []

/-- **cls-oo**. -/
def clsOoFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlOneOf then
    (listElems g d.o (listFuel g)).flatMap (fun yi =>
      (asSubject yi).map (fun yis => ⟨yis, rdfType, d.s.toTerm⟩))
  else []

-- ---------------------------------------------------------------
-- Table 6: class axioms
-- ---------------------------------------------------------------

/-- **cax-sco**. -/
def caxScoFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (withPredObj g rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, d.o⟩)
  else []

/-- **cax-eqc1**. -/
def caxEqc1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    (withPredObj g rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, d.o⟩)
  else []

/-- **cax-eqc2**. -/
def caxEqc2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    (withPredObj g rdfType d.o).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)
  else []

-- ---------------------------------------------------------------
-- Table 8: schema vocabulary
-- ---------------------------------------------------------------

/-- **scm-cls** — all four conclusions of the row. -/
def scmClsFor (_g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlClass then
    [⟨d.s, rdfsSubClassOf, d.s.toTerm⟩,
     ⟨d.s, owlEquivalentClass, d.s.toTerm⟩,
     ⟨d.s, rdfsSubClassOf, Term.iri owlThing⟩,
     ⟨Subject.iri owlNothing, rdfsSubClassOf, d.s.toTerm⟩]
  else []

/-- **scm-sco**. -/
def scmScoFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (asSubject d.o).flatMap (fun c2s =>
      (withSubjPred g c2s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsSubClassOf, u.o⟩))
  else []

/-- **scm-eqc1** — both conclusions of the row. -/
def scmEqc1For (_g : Graph) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    ⟨d.s, rdfsSubClassOf, d.o⟩ ::
      (asSubject d.o).map (fun c2s => ⟨c2s, rdfsSubClassOf, d.s.toTerm⟩)
  else []

/-- **scm-eqc2**. -/
def scmEqc2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (asSubject d.o).flatMap (fun c2s =>
      if memB g ⟨c2s, rdfsSubClassOf, d.s.toTerm⟩
      then [⟨d.s, owlEquivalentClass, d.o⟩] else [])
  else []

/-- **scm-spo**. -/
def scmSpoFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (asSubject d.o).flatMap (fun p2s =>
      (withSubjPred g p2s rdfsSubPropertyOf).map (fun u =>
        ⟨d.s, rdfsSubPropertyOf, u.o⟩))
  else []

/-- **scm-eqp1** — both conclusions of the row. -/
def scmEqp1For (_g : Graph) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    ⟨d.s, rdfsSubPropertyOf, d.o⟩ ::
      (asSubject d.o).map (fun p2s => ⟨p2s, rdfsSubPropertyOf, d.s.toTerm⟩)
  else []

/-- **scm-eqp2**. -/
def scmEqp2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (asSubject d.o).flatMap (fun p2s =>
      if memB g ⟨p2s, rdfsSubPropertyOf, d.s.toTerm⟩
      then [⟨d.s, owlEquivalentProperty, d.o⟩] else [])
  else []

/-- **scm-dom1**. -/
def scmDom1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (asSubject d.o).flatMap (fun c1s =>
      (withSubjPred g c1s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsDomain, u.o⟩))
  else []

/-- **scm-dom2**. -/
def scmDom2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (withPredObj g rdfsSubPropertyOf d.s.toTerm).map (fun u =>
      ⟨u.s, rdfsDomain, d.o⟩)
  else []

/-- **scm-rng1**. -/
def scmRng1For (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (asSubject d.o).flatMap (fun c1s =>
      (withSubjPred g c1s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsRange, u.o⟩))
  else []

/-- **scm-rng2**. -/
def scmRng2For (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (withPredObj g rdfsSubPropertyOf d.s.toTerm).map (fun u =>
      ⟨u.s, rdfsRange, d.o⟩)
  else []

/-- **scm-int**. -/
def scmIntFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (listElems g d.o (listFuel g)).map (fun ci =>
      ⟨d.s, rdfsSubClassOf, ci⟩)
  else []

/-- **scm-uni**. -/
def scmUniFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlUnionOf then
    (listElems g d.o (listFuel g)).flatMap (fun ci =>
      (asSubject ci).map (fun cis => ⟨cis, rdfsSubClassOf, d.s.toTerm⟩))
  else []

-- ---------------------------------------------------------------
-- `[ext]` — the sound extensions, no table row
--
-- Driving-premise choice matters for COST here, not just for style.
-- The two contrapositive rows (prp-fp-diff, prp-ifp-diff) are driven
-- by the `owl:differentFrom` triple rather than by the property
-- declaration: driving from the declaration would pair every
-- `p`-triple with every other `p`-triple (quadratic in the property's
-- extension), while driving from the inequality pairs only the
-- triples that MENTION the two named individuals — one bucket read
-- each in `RLClosureIndexed`.
-- ---------------------------------------------------------------

/-- **eq-diff-sym** `[ext]`. -/
def eqDiffSymFor (_g : Graph) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (asSubject d.o).map (fun ys => ⟨ys, owlDifferentFrom, d.s.toTerm⟩)
  else []

/-- **prp-pdw-diff** `[ext]`, driven by the disjointness declaration. -/
def pdwToDiffFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlPropertyDisjointWith then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        (withPred g p1).flatMap (fun t1 =>
          (asSubject t1.o).flatMap (fun o1s =>
            (withSubjPred g t1.s p2).flatMap (fun t2 =>
              if o1s.toTerm == t2.o then []
              else [⟨o1s, owlDifferentFrom, t2.o⟩])))))
  else []

/-- **cax-dw-diff** `[ext]`, driven by the disjointness declaration. -/
def caxDwToDiffFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlDisjointWith then
    (subjIri d.s).flatMap (fun c1 =>
      (asIri d.o).flatMap (fun c2 =>
        (withPredObj g rdfType (Term.iri c1)).flatMap (fun tx =>
          (withPredObj g rdfType (Term.iri c2)).flatMap (fun ty =>
            if tx.s == ty.s then [] else [⟨tx.s, owlDifferentFrom, ty.s.toTerm⟩]))))
  else []

/-- **prp-fp-diff** `[ext]`, driven by the `owl:differentFrom` triple:
`d` is `(x1 owl:differentFrom x2)`, and the row looks for a functional
property leading INTO each of them. -/
def fpDiffToDiffFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (withObj g d.s.toTerm).flatMap (fun t1 =>
      if memB g ⟨Subject.iri t1.p, rdfType, Term.iri owlFunctionalProperty⟩ then
        (withPredObj g t1.p d.o).flatMap (fun t2 =>
          if t1.s == t2.s then [] else [⟨t1.s, owlDifferentFrom, t2.s.toTerm⟩])
      else [])
  else []

/-- **prp-ifp-diff** `[ext]`, driven by the `owl:differentFrom` triple:
`d` is `(x1 owl:differentFrom x2)`, and the row looks for an
inverse-functional property leading OUT of each of them. -/
def ifpDiffToDiffFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (withSubj g d.s).flatMap (fun t1 =>
      if memB g ⟨Subject.iri t1.p, rdfType,
          Term.iri owlInverseFunctionalProperty⟩ then
        (asSubject t1.o).flatMap (fun y1s =>
          (asSubject d.o).flatMap (fun x2s =>
            (withSubjPred g x2s t1.p).flatMap (fun t2 =>
              if y1s.toTerm == t2.o then []
              else [⟨y1s, owlDifferentFrom, t2.o⟩])))
      else [])
  else []

/-- **scm-trans-from-chain** `[ext]`. -/
def chainToTransFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlPropertyChainAxiom then
    (subjIri d.s).flatMap (fun p =>
      (listSeqs g d.o (listFuel g)).flatMap (fun terms =>
        if terms == [Term.iri p, Term.iri p]
        then [⟨Subject.iri p, rdfType, Term.iri owlTransitiveProperty⟩]
        else []))
  else []

/-- **prp-rfl** `[ext]`, driven by the reflexive-property declaration.
Emits one triple per IRI of the graph, which is why the guard on the
declaration comes first — a graph with no `owl:ReflexiveProperty`
never walks the individual list at all. -/
def prpRflFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlReflexiveProperty then
    (subjIri d.s).flatMap (fun p =>
      (iriIndividuals g).map (fun i => ⟨Subject.iri i, p, Term.iri i⟩))
  else []

/-- **xsd-axioms** `[ext]`, driven by any triple mentioning an XSD IRI. -/
def xsdAxiomsFor (_g : Graph) (d : Triple) : List Triple :=
  if drivesXsdAxioms d then xsdAxiomTriples else []

/-- **dt-rng-intersect** `[ext]`, driven by one of the two range
axioms. -/
def dtRangeIntersectFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (asIri d.o).flatMap (fun d1 =>
      (withSubjPred g d.s rdfsRange).flatMap (fun t2 =>
        (asIri t2.o).flatMap (fun d2 =>
          xsdRangeIntersections.flatMap (fun e =>
            if (e.1 == d1 && e.2.1 == d2) || (e.1 == d2 && e.2.1 == d1)
            then e.2.2.map (fun d3 => ⟨d.s, rdfsRange, Term.iri d3⟩)
            else []))))
  else []

/-- **cax-dw-comp** `[ext]`, driven by the disjointness declaration. -/
def caxDwToComplementFor (_g : Graph) (d : Triple) : List Triple :=
  if d.p == owlDisjointWith then
    (subjIri d.s).flatMap (fun c1 =>
      (asIri d.o).flatMap (fun c2 => complementWitnessTriples c1 c2))
  else []

/-- **cls-maxqc1-comp** `[ext]`, driven by the cardinality
restriction. -/
def clsMaxqc1ToComplementFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni1 then
    (withSubjPred g d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (withSubjPred g d.s owlOnClass).flatMap (fun onc =>
          (asIri onc.o).flatMap (fun c =>
            (withPredObj g rdfType d.s.toTerm).flatMap (fun tu =>
              (withSubjPred g tu.s p).flatMap (fun u1 =>
                (asSubject u1.o).flatMap (fun y1s =>
                  if memB g ⟨y1s, rdfType, Term.iri c⟩ then
                    (withSubjPred g y1s owlDifferentFrom).flatMap (fun df =>
                      (asSubject df.o).flatMap (fun y2s =>
                        if memB g ⟨tu.s, p, y2s.toTerm⟩
                        then complementTypeTriples y2s c else []))
                  else [])))))))
  else []

/-- **minc1-comp** `[ext]`, driven by the object-property
declaration. -/
def minCard1ComprehensionFor (_g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlObjectProperty then
    (subjIri d.s).flatMap minCard1WitnessTriples
  else []

/-- **cax-adc-dw** `[ext]`, driven by the AllDisjointClasses typing. -/
def caxAdcToDwFor (g : Graph) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointClasses then
    (withSubjPred g d.s owlMembers).flatMap (fun mem =>
      (listElems g mem.o (listFuel g)).flatMap (fun ci =>
        (asIri ci).flatMap (fun ci' =>
          (listElems g mem.o (listFuel g)).flatMap (fun cj =>
            (asIri cj).flatMap (fun cj' =>
              if ci' == cj' then []
              else [⟨Subject.iri ci', owlDisjointWith, Term.iri cj'⟩])))))
  else []

/-! ## Section 6 — one round

`conclusionsFrom` is written as `List.flatten` of a literal list of
per-row results rather than a chain of `++`, so that the soundness
case split is a flat `rcases` over 45 alternatives instead of a
45-deep left-nested `Or`. -/

/-- Every conclusion the ported rows license from the driving triple
`d`, reading all other premises from `g`. -/
def conclusionsList (g : Graph) (d : Triple) : List (List Triple) :=
    [ eqRefSFor g d, eqRefPFor g d, eqRefOFor g d,
      eqSymFor g d, eqTransFor g d,
      eqRepSFor g d, eqRepPFor g d, eqRepOFor g d,
      prpDomFor g d, prpRngFor g d, prpFpFor g d, prpIfpFor g d,
      prpSympFor g d, prpTrpFor g d, prpSpo1For g d, prpSpo2For g d,
      prpEqp1For g d, prpEqp2For g d, prpInv1For g d, prpInv2For g d,
      prpKeyFor g d,
      clsInt1For g d, clsInt2For g d, clsUniFor g d,
      clsSvf1For g d, clsSvf2For g d, clsAvfFor g d,
      clsHv1For g d, clsHv2For g d, clsHs1For g d, clsHs2For g d,
      clsMaxc2For g d, clsOoFor g d,
      caxScoFor g d, caxEqc1For g d, caxEqc2For g d,
      scmClsFor g d, scmScoFor g d, scmEqc1For g d, scmEqc2For g d,
      scmSpoFor g d, scmEqp1For g d, scmEqp2For g d,
      scmDom1For g d, scmDom2For g d, scmRng1For g d, scmRng2For g d,
      scmIntFor g d, scmUniFor g d,
      eqDiffSymFor g d, pdwToDiffFor g d, caxDwToDiffFor g d,
      fpDiffToDiffFor g d, ifpDiffToDiffFor g d,
      chainToTransFor g d, prpRflFor g d,
      xsdAxiomsFor g d, dtRangeIntersectFor g d,
      caxDwToComplementFor g d, clsMaxqc1ToComplementFor g d,
      minCard1ComprehensionFor g d, caxAdcToDwFor g d,
      inverseOfDomRngFlipFor g d ]

/-- The flattening of `conclusionsList`. -/
def conclusionsFrom (g : Graph) (d : Triple) : List Triple :=
  (conclusionsList g d).flatten

/-- Everything the ported rows conclude from `g` in one round, before
deduplication — the counterpart of `owl_rl_closure_step`'s pre-dedup
half, plus the two premise-free Table 5 rows. -/
def stepConclusions (g : Graph) : List Triple :=
  axiomTriples ++ g.flatMap (conclusionsFrom g)

/-- One closure round: `g` plus every conclusion the rows license from
`g`, deduplicated exactly. -/
def step (g : Graph) : Graph :=
  addAll g (stepConclusions g)

/-! ## Section 7 — the fixpoint loop -/

/-- Fuel-bounded fixpoint — port of `owl_rl_closure`, including its
stopping rule: run a round, and if the LENGTH did not change, return
the INPUT (at equal length the two hold the same triples — see
`RLTheorems.addAll_eq_of_length_eq`). -/
def closure (g : Graph) (fuel : Nat) : Graph :=
  match fuel with
  | 0     => g
  | n + 1 =>
      let g' := step g
      if g'.length = g.length then g else closure g' n

/-- The fuel budget `closureFix` spends.

The F* callers pass the constant 100 — a resource budget, not a bound
with an argument behind it. The bound here has the counting argument
behind it instead:

* the loop only recurses when the round STRICTLY grew the graph, so at
  most one iteration per triple ever added;
* every rule conclusion is built from components already present in the
  round's input, PLUS the fixed vocabulary the rows name literally
  (`owl:sameAs`, `rdf:type`, `owl:Thing`, `owl:Nothing`, `owl:Class`,
  `rdfs:subClassOf`, `rdfs:subPropertyOf`, `rdfs:domain`,
  `rdfs:range`, `owl:equivalentClass`, `owl:equivalentProperty`) — so
  the closure of an `n`-triple graph draws its subjects, predicates and
  objects from a universe of size at most `n + 11` in each slot.

Hence `(n + 11)^3 + 1` rounds cannot be exhausted before the length
test fires. The counting argument is STATED, not proved:
`RLTheorems.closure_saturated_or_underfueled` is what is proved, and it
says precisely that the only alternative to saturation is a closure
that grew by at least one triple per unit of fuel. Formalising the
term-universe bound is the named remaining obligation — the same one
`RDFS/Closure.lean` names for the rdfs-core loop. -/
def closureFuelBound (g : Graph) : Nat :=
  let n := g.length + 11
  n * n * n + 1

/-- The closure at the fuel bound above. -/
def closureFix (g : Graph) : Graph :=
  closure g (closureFuelBound g)

/-! ## Section 8 — the clash rows

Port of `is_inconsistent`. Each `xxxAt g d` reads `d` as the row's
driving premise and decides whether the rest of the row's premises are
present. -/

/-- **eq-diff1**. -/
def eqDiff1At (g : Graph) (d : Triple) : Bool :=
  d.p == owlSameAs && memB g ⟨d.s, owlDifferentFrom, d.o⟩

/-- **prp-irp**. -/
def prpIrpAt (g : Graph) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlIrreflexiveProperty then
    (subjIri d.s).any (fun p => (withPred g p).any (fun u => u.o == u.s.toTerm))
  else false

/-- **prp-asyp**. -/
def prpAsypAt (g : Graph) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAsymmetricProperty then
    (subjIri d.s).any (fun p =>
        (withPred g p).any (fun u1 =>
          (asSubject u1.o).any (fun y => memB g ⟨y, p, u1.s.toTerm⟩)))
  else false

/-- **prp-pdw**. -/
def prpPdwAt (g : Graph) (d : Triple) : Bool :=
  if d.p == owlPropertyDisjointWith then
    (subjIri d.s).any (fun p1 =>
        (asIri d.o).any (fun p2 =>
          (withPred g p1).any (fun u => memB g ⟨u.s, p2, u.o⟩)))
  else false

/-- **prp-npa1**. -/
def prpNpa1At (g : Graph) (d : Triple) : Bool :=
  if d.p == owlSourceIndividual then
    (asSubject d.o).any (fun x =>
      (withSubjPred g d.s owlAssertionProperty).any (fun ap =>
        (asIri ap.o).any (fun p =>
          (withSubjPred g d.s owlTargetIndividual).any (fun ti =>
            memB g ⟨x, p, ti.o⟩))))
  else false

/-- **prp-npa2**. -/
def prpNpa2At (g : Graph) (d : Triple) : Bool :=
  if d.p == owlSourceIndividual then
    (asSubject d.o).any (fun x =>
      (withSubjPred g d.s owlAssertionProperty).any (fun ap =>
        (asIri ap.o).any (fun p =>
          (withSubjPred g d.s owlTargetValue).any (fun tv =>
            memB g ⟨x, p, tv.o⟩))))
  else false

/-- **cls-nothing2**. -/
def clsNothing2At (_g : Graph) (d : Triple) : Bool :=
  d.p == rdfType && d.o == Term.iri owlNothing

/-- **cls-com**. -/
def clsComAt (g : Graph) (d : Triple) : Bool :=
  if d.p == owlComplementOf then
    (withPredObj g rdfType d.s.toTerm).any (fun u =>
      memB g ⟨u.s, rdfType, d.o⟩)
  else false

/-- **cls-maxc1**. -/
def clsMaxc1At (g : Graph) (d : Triple) : Bool :=
  if d.p == owlMaxCardinality && d.o == Term.literal litNni0 then
    (withSubjPred g d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (withPredObj g rdfType d.s.toTerm).any (fun tu =>
          !(withSubjPred g tu.s p).isEmpty)))
  else false

/-- **cls-maxqc1**. -/
def clsMaxqc1At (g : Graph) (d : Triple) : Bool :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni0 then
    (withSubjPred g d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (withSubjPred g d.s owlOnClass).any (fun onc =>
          (withPredObj g rdfType d.s.toTerm).any (fun tu =>
            (withSubjPred g tu.s p).any (fun u =>
              (asSubject u.o).any (fun ys =>
                memB g ⟨ys, rdfType, onc.o⟩))))))
  else false

/-- **cls-maxqc2**. -/
def clsMaxqc2At (g : Graph) (d : Triple) : Bool :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni0 then
    (withSubjPred g d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (withSubjPred g d.s owlOnClass).any (fun onc =>
          onc.o == Term.iri owlThing &&
          (withPredObj g rdfType d.s.toTerm).any (fun tu =>
            !(withSubjPred g tu.s p).isEmpty))))
  else false

/-- **cax-dw**. -/
def caxDwAt (g : Graph) (d : Triple) : Bool :=
  if d.p == owlDisjointWith then
    (withPredObj g rdfType d.s.toTerm).any (fun u =>
      memB g ⟨u.s, rdfType, d.o⟩)
  else false

/-! ### The four collection clash rows, and why they walk CELLS

`caxAdcAt`, `eqDiff2At`, `eqDiff3At` and `prpAdpAt` take their member
pair from two DISTINCT CELLS of the collection, and additionally
require the two members to be distinct terms. The `Clash` constructors
they discharge ask only for the distinct TERMS — the distinct-term
reading of `1 <= i < j <= n` — so each engine row is STRICTLY WEAKER
than its `Clash` row. Soundness is what is proved; completeness of the
decision is not claimed here.

The cell walk is not decoration. eq-rep-o copies an `rdf:first` value
across an `owl:sameAs` edge, so after closure ONE cell of a well-formed
list can carry two co-referring `rdf:first` values. A member pair taken
from that one cell is one POSITION of the table's `LIST[?y, ?z1, ...,
?zn]` premise, not two, and firing on it reports an inconsistency the
corpus asserts consistent: measured 2026-09-04 on WebOnt-miscellaneous-
001/002/011 (the Wine ontology, which imports the Food ontology and
identifies `vin:Red` with `food:Red`). -/

/-- **cax-adc**, in the cell form. -/
def caxAdcAt (g : Graph) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointClasses then
    (withSubjPred g d.s owlMembers).any (fun mem =>
      (listCells g mem.o (listFuel g)).any (fun ci =>
        (listCells g mem.o (listFuel g)).any (fun cj =>
          !(ci == cj) &&
          (withSubjPred g ci rdfFirst).any (fun fi =>
            (withSubjPred g cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (withPredObj g rdfType fi.o).any (fun u =>
                memB g ⟨u.s, rdfType, fj.o⟩))))))
  else false

/-- **eq-diff2**. -/
def eqDiff2At (g : Graph) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDifferent then
    (withSubjPred g d.s owlMembers).any (fun mem =>
      (listCells g mem.o (listFuel g)).any (fun ci =>
        (listCells g mem.o (listFuel g)).any (fun cj =>
          !(ci == cj) &&
          (withSubjPred g ci rdfFirst).any (fun fi =>
            (withSubjPred g cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asSubject fi.o).any (fun zs =>
                memB g ⟨zs, owlSameAs, fj.o⟩))))))
  else false

/-- **eq-diff3** — eq-diff2 through `owl:distinctMembers`. -/
def eqDiff3At (g : Graph) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDifferent then
    (withSubjPred g d.s owlDistinctMembers).any (fun mem =>
      (listCells g mem.o (listFuel g)).any (fun ci =>
        (listCells g mem.o (listFuel g)).any (fun cj =>
          !(ci == cj) &&
          (withSubjPred g ci rdfFirst).any (fun fi =>
            (withSubjPred g cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asSubject fi.o).any (fun zs =>
                memB g ⟨zs, owlSameAs, fj.o⟩))))))
  else false

/-- **prp-adp**. -/
def prpAdpAt (g : Graph) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointProperties then
    (withSubjPred g d.s owlMembers).any (fun mem =>
      (listCells g mem.o (listFuel g)).any (fun ci =>
        (listCells g mem.o (listFuel g)).any (fun cj =>
          !(ci == cj) &&
          (withSubjPred g ci rdfFirst).any (fun fi =>
            (withSubjPred g cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asIri fi.o).any (fun p1 =>
                (asIri fj.o).any (fun p2 =>
                  (withPred g p1).any (fun u =>
                    memB g ⟨u.s, p2, u.o⟩))))))))
  else false

/-- The sixteen clash-row verdicts for one driving triple. -/
def clashRows (g : Graph) (d : Triple) : List Bool :=
  [ eqDiff1At g d, prpIrpAt g d, prpAsypAt g d, prpPdwAt g d,
    prpNpa1At g d, prpNpa2At g d, clsNothing2At g d, clsComAt g d,
    clsMaxc1At g d, clsMaxqc1At g d, clsMaxqc2At g d,
    caxDwAt g d, caxAdcAt g d,
    eqDiff2At g d, eqDiff3At g d, prpAdpAt g d ]

/-- Every clash row, driven by one triple. -/
def clashFrom (g : Graph) (d : Triple) : Bool :=
  (clashRows g d).any (fun b => b)

/-- **The clash decision.** `true` means some no-consequent row of the
tables has all its premises in `g`, i.e. `g` is OWL 2 RL inconsistent.
`RLTheorems.detectClash_sound` proves every `true` verdict is a real
`Clash`. -/
def detectClash (g : Graph) : Bool :=
  g.any (fun d => clashFrom g d)

/-- Consistency checked against the CLOSURE, which is what the F*
`entailment_closure` + `is_inconsistent` pipeline does: a clash is
usually only visible after materialisation. -/
def inconsistent (g : Graph) (fuel : Nat) : Bool :=
  detectClash (closure g fuel)

end L4Factoidal.OWL.RL
