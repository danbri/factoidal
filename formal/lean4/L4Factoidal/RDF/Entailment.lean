/-
L4Factoidal.RDF.Entailment — simple entailment (RDF 1.1 Semantics §5),
the D / RDF / RDFS entailment regimes on top of it (§7, §8, §9), and
D-inconsistency.

  https://www.w3.org/TR/rdf11-mt/#simpleentailment   (§5.2 interpolation lemma)
  https://www.w3.org/TR/rdf11-mt/#datatype-entailment (§7)
  https://www.w3.org/TR/rdf11-mt/#rdf-entailment      (§8)
  https://www.w3.org/TR/rdf11-mt/#rdfs-entailment     (§9)

## Simple entailment — the specification

§5.2, Interpolation Lemma: "S simply entails a graph E if and only if
a subgraph of S is an instance of E". An INSTANCE (§3.3 / §5.2)
replaces each blank node of E by an IRI, a literal or a blank node —
any term — consistently. That is `SimpleEntails` below: there is a
mapping `σ` from blank-node labels to terms such that every triple of
`E`, with its blank nodes replaced, is a triple of `S`.

A blank node in SUBJECT position cannot become a literal (RDF 1.1
Concepts §3.1 — this term model's `Subject` has no literal
constructor), so `Triple.instance?` is partial: such a `σ` is simply
not an instance mapping. In the suite this matters for `datatypes-
test008` (`_:x` in OBJECT position maps to the literal `"10"` — that IS
an instance) and never the other way round.

## The decision procedure — a witness, then a certificate

`searchInstance` backtracks over the triples of `E` in order, binding
each blank node the first time it is met (to a subject, a literal, an
IRI — whatever the candidate triple of `S` holds there) and checking it
thereafter. It returns the mapping; `instanceCert` then re-checks that
mapping from scratch, and `entailsWith` answers `true` only when the
certificate passes. So soundness (`simpleEntails_sound` in
`EntailmentTheorems.lean`) is a statement about the certificate alone,
exactly as `Isomorphism.lean` does for isomorphism. Termination is
structural on `E`'s triple list; breadth is bounded by `|S|` per
triple.

Both the search and the certificate are parameterised by a literal
comparison `leq` — strict term equality for simple entailment, D-value
equality for the D / RDF / RDFS regimes (§7: "literals with the same
value are interchangeable") — and by `bindable`, the terms a blank node
may be mapped to (an ill-formed literal of a recognised datatype
denotes nothing, so no blank node can be it — §7).

## The regimes

* `simple`: no closure, strict literal identity, any term bindable.
* `d`     : no closure, D-value literal equality.
* `rdf`   : `RDFS.rdfClosure` (§8.2 axioms + rdfD2), D-value equality.
* `rdfs`  : `RDFS.fullClosure` (§8 + §9 rules and axioms), D-value
            equality.

`regimeEntails r D g h` is `inconsistent ∨ instance-found`: an
inconsistent graph entails everything (§5.1, "an inconsistent graph
... entails any graph"), which rdf-mt's `mf:result false` positives
depend on.

## D-inconsistency (§7, §9.2.1 "datatype clashes")

Two decidable shapes, the same two `RDF.Entailment.RDFS.DatatypeClash`
decides in the F\* tree:

  (a) a literal typed with a recognised datatype whose lexical form is
      outside that datatype's lexical space (`literalIllFormed`);
  (b) under RDFS, a literal forced by `rdfs:range` (through any
      `rdfs:subClassOf` chain — the closure is transitively closed, so
      one lookup suffices) into a recognised datatype class whose value
      space does not contain its value (`valueInSpace`). Both the
      literal's own datatype and the range class must be recognised:
      an unrecognised literal denotes an unknown thing that might well
      be in the range (§7).

Not decided: XMLLiteral IS decided here (the XML parser is in the
tree), which the F\* module leaves as `Unsupported`. Anything needing
rdfD1's surrogate blank nodes is not, and is documented in
`RDFS/FullClosure.lean`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Datatypes
import L4Factoidal.RDFS.FullClosure

namespace L4Factoidal.RDF

open L4Factoidal.RDFS

/-! ## Instances — RDF 1.1 Semantics §3.3 -/

/-- A subject with its blank node replaced by `σ`; `none` when `σ`
sends it to a term that cannot be a subject. -/
def Subject.instance? (σ : BNodeId → Term) : Subject → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => (σ b).toSubject?

/-- A term with its blank nodes replaced by `σ`, recursing into RDF 1.2
triple terms (where a subject-position blank node has the same
restriction). -/
def Term.instance? (σ : BNodeId → Term) : Term → Option Term
  | .iri i     => some (.iri i)
  | .bnode b   => some (σ b)
  | .literal l => some (.literal l)
  | .tripleTerm s p o =>
      match s.instance? σ, o.instance? σ with
      | some s', some o' => some (.tripleTerm s' p o')
      | _, _ => none

/-- A triple with its blank nodes replaced by `σ`. -/
def Triple.instance? (σ : BNodeId → Term) (t : Triple) : Option Triple :=
  match t.s.instance? σ, t.o.instance? σ with
  | some s', some o' => some ⟨s', t.p, o'⟩
  | _, _ => none

/-- **RDF 1.1 Semantics §5.2 (interpolation lemma).** `g` simply entails
`h` iff some instance of `h` is a subgraph of `g`. -/
def SimpleEntails (g h : Graph) : Prop :=
  ∃ σ : BNodeId → Term, ∀ t ∈ h, ∃ t', t.instance? σ = some t' ∧ t' ∈ g

/-! ## Term matching under a literal comparison -/

/-- Term matching: IRIs and blank nodes by identity, literals by `leq`,
triple terms componentwise. `u` is the candidate from the premise
graph, `t` the (instantiated) conclusion term. -/
def termMatch (leq : Literal → Literal → Bool) : Term → Term → Bool
  | .iri i,     .iri j     => i == j
  | .bnode a,   .bnode b   => a == b
  | .literal l, .literal m => leq l.val m.val
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
      s1 == s2 && p1 == p2 && termMatch leq o1 o2
  | _, _ => false

/-- Triple matching: subject and predicate exact, object via `termMatch`. -/
def tripleMatch (leq : Literal → Literal → Bool) (u t : Triple) : Bool :=
  u.s == t.s && u.p == t.p && termMatch leq u.o t.o

/-- Strict literal identity (RDF 1.1 Concepts §3.3, "literal term
equality") — the comparison of SIMPLE entailment. -/
def literalStrictEq (a b : Literal) : Bool := a == b

/-! ## Candidate mappings -/

/-- An association list of blank-node labels to terms. -/
abbrev Mapping := List (BNodeId × Term)

def Mapping.lookup (m : Mapping) (b : BNodeId) : Option Term :=
  (m.find? (fun p => p.1 == b)).map Prod.snd

/-- The function a candidate mapping denotes: identity (as a blank
node) on labels it does not mention. -/
def Mapping.toFun (m : Mapping) (b : BNodeId) : Term :=
  match m.lookup b with
  | some t => t
  | none   => .bnode b

/-- The certificate: under `m`, every triple of `h` instantiates to a
triple some triple of `g` matches. -/
def instanceCert (leq : Literal → Literal → Bool) (m : Mapping) (g h : Graph) : Bool :=
  h.all (fun t =>
    match t.instance? m.toFun with
    | some t' => g.any (fun u => tripleMatch leq u t')
    | none    => false)

/-! ## The search -/

/-- Match the conclusion subject `hs` against the premise subject `gs`,
extending `m` when `hs` is an unbound blank node. -/
def matchSubject (m : Mapping) (hs gs : Subject) : Option Mapping :=
  match hs with
  | .iri i =>
      match gs with
      | .iri j   => if i == j then some m else none
      | .bnode _ => none
  | .bnode b =>
      match m.lookup b with
      | some t => if t == gs.toTerm then some m else none
      | none   => some ((b, gs.toTerm) :: m)

/-- Match the conclusion object `ho` against the premise object `go`,
threading the binding. An unbound blank node binds to `go` when
`bindable go`; an RDF 1.2 triple term is entered componentwise, so a
blank node INSIDE a triple term binds like any other.

The interior recursion is not decoration. Without it the object arm
fell straight to `termMatch`, which compares a triple term's subject
and interior object by identity — so `_:a p <<( x q _:b )>>` could
match only a premise whose interior blank node carried the SAME label,
and the decision procedure answered `false` on entailments that hold.
`entailsSimple_tripleTerm_interior_bnode` in
`RDF/EntailmentSimpleRefinement.lean` pins the witness. The F* source's
`match_term` (`RDF.Entailment.Simple.fst:94`) always recursed; this arm
did not, and the port carried the gap until 2026-08-23. -/
def matchObject (leq : Literal → Literal → Bool) (bindable : Term → Bool)
    (m : Mapping) : Term → Term → Option Mapping
  | .bnode b, go =>
      match m.lookup b with
      | some t => if t == go then some m else none
      | none   => if bindable go then some ((b, go) :: m) else none
  | .tripleTerm ps pp po, .tripleTerm gs gp go =>
      if pp == gp then
        match matchSubject m ps gs with
        | some m1 => matchObject leq bindable m1 po go
        | none    => none
      else none
  | ho, go => if termMatch leq go ho then some m else none

/-- Backtracking search for an instance mapping: structural on the
conclusion triples, breadth over the premise triples. -/
def searchInstance (leq : Literal → Literal → Bool) (bindable : Term → Bool)
    (g : Graph) : List Triple → Mapping → Option Mapping
  | [], m => some m
  | t :: rest, m =>
      g.findSome? fun u =>
        if u.p != t.p then none
        else
          match matchSubject m t.s u.s with
          | none => none
          | some m1 =>
            match matchObject leq bindable m1 t.o u.o with
            | none => none
            | some m2 => searchInstance leq bindable g rest m2

/-- Entailment by instance, under a literal comparison and a
bindability test: search, then certify. -/
def entailsWith (leq : Literal → Literal → Bool) (bindable : Term → Bool)
    (g h : Graph) : Bool :=
  match searchInstance leq bindable g h [] with
  | some m => instanceCert leq m g h
  | none   => false

/-- **Simple entailment**, decided (§5.2). -/
def simpleEntails (g h : Graph) : Bool :=
  entailsWith literalStrictEq (fun _ => true) g h

/-! ## D-inconsistency -/

/-- Every literal in object position of `g` (triple-term interiors
included). -/
def Term.literals : Term → List Literal
  | .literal l => [l.val]
  | .tripleTerm _ _ o => o.literals
  | _ => []

def literalsOf (g : Graph) : List Literal :=
  g.flatMap (fun t => t.o.literals)

/-- Rule (a): some recognised literal is ill-formed. -/
def hasIllFormedLiteral (D : List WfIri) (g : Graph) : Bool :=
  (literalsOf g).any (literalIllFormed D)

/-- The classes a literal object of property `p` is forced into by
`rdfs:range` in the (closed) graph `c`: every range class and every
superclass of one. -/
def rangeClassesOf (c : Graph) (p : WfIri) : List WfIri :=
  let ranges := (objectsOf c (.iri p) rdfsRange).filterMap (fun o =>
    match o with | .iri i => some i | _ => none)
  ranges.flatMap (fun r =>
    r :: (objectsOf c (.iri r) rdfsSubClassOf).filterMap (fun o =>
      match o with | .iri i => some i | _ => none))

/-- Rule (b): some recognised, well-formed literal is range-forced into
a recognised datatype whose value space does not hold its value. -/
def hasRangeClash (D : List WfIri) (c : Graph) : Bool :=
  c.any (fun t =>
    match t.o with
    | .literal l =>
        D.contains l.val.datatype && !literalIllFormed D l.val &&
        (rangeClassesOf c t.p).any (fun cls => D.contains cls && !valueInSpace l.val cls)
    | _ => false)

/-! ## Regimes -/

/-- The entailment regimes this module decides. -/
inductive Regime where
  | simple
  | d
  | rdf
  | rdfs
  deriving DecidableEq, Repr

/-- Parse the names the rdf-mt manifest (`mf:entailmentRegime` literal)
and the sparql11 entailment manifest (`ent:` local names) use. -/
def Regime.ofName? : String → Option Regime
  | "simple" => some .simple
  | "D"      => some .d
  | "RDF"    => some .rdf
  | "RDFS"   => some .rdfs
  | _        => none

def Regime.name : Regime → String
  | .simple => "simple"
  | .d      => "D"
  | .rdf    => "RDF"
  | .rdfs   => "RDFS"

/-- The antecedent closure a regime applies. `cmps` is the `rdf:_n`
slice (see `RDFS/FullClosure.lean`). -/
def Regime.closure (r : Regime) (D cmps : List WfIri) (g : Graph) : Graph :=
  match r with
  | .simple => g
  | .d      => g
  | .rdf    => rdfClosure cmps g
  | .rdfs   => fullClosure D cmps g

/-- The literal comparison a regime matches with. -/
def Regime.literalEq (r : Regime) (D : List WfIri) : Literal → Literal → Bool :=
  match r with
  | .simple => literalStrictEq
  | _       => literalValueEq D

/-- What a blank node may range over under a regime: anything, except
(under D) an ill-formed recognised literal. -/
def Regime.bindable (r : Regime) (D : List WfIri) : Term → Bool :=
  match r with
  | .simple => fun _ => true
  | _ => fun t => match t with
                  | .literal l => !literalIllFormed D l.val
                  | _ => true

/-- Is the closed graph D-inconsistent under the regime? Rule (a) in
every D-aware regime; rule (b) only where `rdfs:range` has force. -/
def Regime.inconsistent (r : Regime) (D : List WfIri) (closed : Graph) : Bool :=
  match r with
  | .simple => false
  | .d | .rdf => hasIllFormedLiteral D closed
  | .rdfs => hasIllFormedLiteral D closed || hasRangeClash D closed

/-- **Regime entailment**: close `g`, then `h` follows if the closure
is inconsistent or has an instance of `h` as a subgraph (up to the
regime's literal equality). `D` is taken as given (callers apply
`withMinimalD`); the `rdf:_n` slice is harvested from both graphs. -/
def regimeEntails (r : Regime) (D : List WfIri) (g h : Graph) : Bool :=
  let cmps := (containerMembershipIn (g ++ h)).foldl
                (fun acc i => if acc.contains i then acc else acc ++ [i]) [rdf1]
  let c := r.closure D cmps g
  r.inconsistent D c || entailsWith (r.literalEq D) (r.bindable D) c h

/-- **Regime consistency check** on a graph by itself. -/
def regimeInconsistent (r : Regime) (D : List WfIri) (g : Graph) : Bool :=
  let cmps := (containerMembershipIn g).foldl
                (fun acc i => if acc.contains i then acc else acc ++ [i]) [rdf1]
  r.inconsistent D (r.closure D cmps g)

end L4Factoidal.RDF
