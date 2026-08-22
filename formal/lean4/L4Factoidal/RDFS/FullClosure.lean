/-
L4Factoidal.RDFS.FullClosure — the full RDF 1.1 Semantics rule set:
the RDF rule rdfD2 (§8.1), the RDFS rules rdfs1–rdfs13 (§9.2), and the
RDF / RDFS axiomatic triples (§8.2, §9.3) — as a derivation relation
`DerivesFull` and as an executable fixpoint closure `fullClosure`.

  https://www.w3.org/TR/rdf11-mt/#rdf-entailment    (§8)
  https://www.w3.org/TR/rdf11-mt/#rdfs-entailment   (§9)

`RdfsCore.lean` / `Closure.lean` are the six-row rdfs-core fragment and
stay exactly as they were: this module EXTENDS them. `fullStep` runs the
rdfs-core step's conclusions plus the eight single-premise rows below,
and `FullClosureTheorems.lean` proves that every rdfs-core derivation
is a full-RDFS derivation (`Derives.toFull`) and that everything the
full closure computes is derivable (`fullClosure_sound`).

## What is in the rule set, row by row

RDF 1.1 Semantics §8.1, RDF entailment rules:

  * rdfD2  `xxx aaa yyy .`  ⊢  `aaa rdf:type rdf:Property .`
  * rdfD1  `xxx aaa "sss"^^ddd .` (ddd in D)  ⊢  `_:nnn rdf:type ddd .`
    NOT a row here: it mints a fresh blank node per literal. Its only
    observable consequences on a non-generalised conclusion graph are
    (a) `_:b rdf:type ddd` answered by a blank node that can ALSO map
    to the literal itself under simple entailment, which the instance
    search in `RDF/Entailment.lean` permits, and (b) D-inconsistency
    of ill-formed literals, which `Entailment.dInconsistent` decides.
    The F\* tree makes the same cut (`RDFS.Closure.fsti` banner:
    "rdfD1 ... mint fresh blank nodes — a scoped gap").

RDF 1.1 Semantics §9.2, RDFS entailment rules (quoted from the table):

  * rdfs1   any IRI aaa in D  ⊢  `aaa rdf:type rdfs:Datatype .`
            — premise-free, so it is emitted as an AXIOM over D
            (`datatypeAxioms`), exactly like the §9.3 triples.
  * rdfs2   `aaa rdfs:domain xxx . yyy aaa zzz .`  ⊢  `yyy rdf:type xxx .`
  * rdfs3   `aaa rdfs:range xxx . yyy aaa zzz .`   ⊢  `zzz rdf:type xxx .`
  * rdfs4a  `xxx aaa yyy .`  ⊢  `xxx rdf:type rdfs:Resource .`
  * rdfs4b  `xxx aaa yyy .`  ⊢  `yyy rdf:type rdfs:Resource .`
  * rdfs5   `xxx rdfs:subPropertyOf yyy . yyy rdfs:subPropertyOf zzz .`
            ⊢  `xxx rdfs:subPropertyOf zzz .`
  * rdfs6   `xxx rdf:type rdf:Property .`  ⊢  `xxx rdfs:subPropertyOf xxx .`
  * rdfs7   `aaa rdfs:subPropertyOf bbb . xxx aaa yyy .`  ⊢  `xxx bbb yyy .`
  * rdfs8   `xxx rdf:type rdfs:Class .`  ⊢  `xxx rdfs:subClassOf rdfs:Resource .`
  * rdfs9   `xxx rdfs:subClassOf yyy . zzz rdf:type xxx .`  ⊢  `zzz rdf:type yyy .`
  * rdfs10  `xxx rdf:type rdfs:Class .`  ⊢  `xxx rdfs:subClassOf xxx .`
  * rdfs11  `xxx rdfs:subClassOf yyy . yyy rdfs:subClassOf zzz .`
            ⊢  `xxx rdfs:subClassOf zzz .`
  * rdfs12  `xxx rdf:type rdfs:ContainerMembershipProperty .`
            ⊢  `xxx rdfs:subPropertyOf rdfs:member .`
  * rdfs13  `xxx rdf:type rdfs:Datatype .`  ⊢  `xxx rdfs:subClassOf rdfs:Literal .`

rdfs2, 3, 5, 7, 9, 11 are the rdfs-core rows and are NOT restated: the
relation below embeds `RdfsCore.Derives` (see `Derives.toFull`) and the
executable step reuses `Closure.stepConclusions`.

## Generalised RDF, and what this port drops

§9.2 says the rules are stated for GENERALISED RDF: rdfs3 / rdfs4b can
put a literal in subject position. The term model here (`Subject` is
IRI-or-blank-node, RDF 1.1 Concepts §3.1) cannot build such a triple,
so those conclusions are dropped — the same `term_to_subject` guard the
F\* rows carry (`RDFS.Closure.fsti`, "GENERALIZED-RDF PREMISE"). The
dropped triples matter in exactly two places, and both are handled
elsewhere by name: a literal forced into a datatype class it is not a
member of is a D-INCONSISTENCY (`Entailment.dInconsistent`, rule (b)),
and a query for `?L rdf:type rdfs:Literal` must NOT answer with a
literal (SPARQL 1.1 Entailment Regimes §4.2 — rdfs13 / d-ent-01).

## The infinite `rdf:_n` family

§8.2 and §9.3 list axioms for EVERY `rdf:_n`. A closure can only carry
a finite slice; the slice taken is `rdf:_1` plus every `rdf:_n` the
graphs under consideration mention (`containerMembershipIn`), and the
caller passes that list in as `cmps`. This is complete for entailment
checking: no rule ever introduces an `rdf:_n` that is not already in a
premise or an axiom instance, so an `rdf:_n` absent from both the
premise and the conclusion graph can appear in no derivation of a
conclusion triple.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDFS.Closure

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## Axiomatic triples — RDF 1.1 Semantics §8.2 and §9.3 -/

/-- Shorthand: an all-IRI triple. -/
def iriTriple (s p o : WfIri) : Triple := ⟨.iri s, p, .iri o⟩

/-- Is this IRI a container-membership property `rdf:_n` (n ≥ 1, digits
only)? RDF Schema §5.1.3: "rdf:_1, rdf:_2, rdf:_3, …". -/
def isContainerMembershipIri (s : String) : Bool :=
  let pre := rdfNs ++ "_"
  s.startsWith pre &&
  (let digits := s.toList.drop pre.length
   !digits.isEmpty && digits.all Char.isDigit)

/-- Every `rdf:_n` IRI a graph mentions in subject, predicate or object
position (without duplicates). Triple-term interiors are searched too. -/
def cmpOfIri (i : WfIri) : List WfIri :=
  if isContainerMembershipIri i.val then [i] else []

def cmpOfSubject : Subject → List WfIri
  | .iri i   => cmpOfIri i
  | .bnode _ => []

def cmpOfTerm : Term → List WfIri
  | .iri i            => cmpOfIri i
  | .tripleTerm s p o => cmpOfSubject s ++ cmpOfIri p ++ cmpOfTerm o
  | _                 => []

def containerMembershipIn (g : Graph) : List WfIri :=
  let all := g.flatMap (fun t => cmpOfSubject t.s ++ cmpOfIri t.p ++ cmpOfTerm t.o)
  all.foldl (fun acc i => if acc.contains i then acc else acc ++ [i]) []

/-- §8.2, the RDF axiomatic triples, for the given `rdf:_n` slice.
Quoted: "rdf:type rdf:type rdf:Property . rdf:subject rdf:type
rdf:Property . rdf:predicate … rdf:object … rdf:first … rdf:rest …
rdf:value rdf:type rdf:Property . rdf:nil rdf:type rdf:List . rdf:_1
rdf:type rdf:Property . rdf:_2 … ". -/
def rdfAxiomaticTriples (cmps : List WfIri) : Graph :=
  [ iriTriple rdfType rdfType rdfProperty,
    iriTriple rdfSubject rdfType rdfProperty,
    iriTriple rdfPredicate rdfType rdfProperty,
    iriTriple rdfObject rdfType rdfProperty,
    iriTriple rdfFirst rdfType rdfProperty,
    iriTriple rdfRest rdfType rdfProperty,
    iriTriple rdfValue rdfType rdfProperty,
    iriTriple rdfNil rdfType rdfList ] ++
  cmps.map (fun c => iriTriple c rdfType rdfProperty)

/-- §9.3, the RDFS axiomatic triples (the fixed part). Transcribed in
the table's order: the `rdfs:domain` block, the `rdfs:range` block,
then the subclass / subproperty / datatype block. -/
def rdfsAxiomaticTriplesFixed : Graph :=
  [ iriTriple rdfType rdfsDomain rdfsResource,
    iriTriple rdfsDomain rdfsDomain rdfProperty,
    iriTriple rdfsRange rdfsDomain rdfProperty,
    iriTriple rdfsSubPropertyOf rdfsDomain rdfProperty,
    iriTriple rdfsSubClassOf rdfsDomain rdfsClass,
    iriTriple rdfSubject rdfsDomain rdfStatement,
    iriTriple rdfPredicate rdfsDomain rdfStatement,
    iriTriple rdfObject rdfsDomain rdfStatement,
    iriTriple rdfsMember rdfsDomain rdfsResource,
    iriTriple rdfFirst rdfsDomain rdfList,
    iriTriple rdfRest rdfsDomain rdfList,
    iriTriple rdfsSeeAlso rdfsDomain rdfsResource,
    iriTriple rdfsIsDefinedBy rdfsDomain rdfsResource,
    iriTriple rdfsComment rdfsDomain rdfsResource,
    iriTriple rdfsLabel rdfsDomain rdfsResource,
    iriTriple rdfValue rdfsDomain rdfsResource,

    iriTriple rdfType rdfsRange rdfsClass,
    iriTriple rdfsDomain rdfsRange rdfsClass,
    iriTriple rdfsRange rdfsRange rdfsClass,
    iriTriple rdfsSubPropertyOf rdfsRange rdfProperty,
    iriTriple rdfsSubClassOf rdfsRange rdfsClass,
    iriTriple rdfSubject rdfsRange rdfsResource,
    iriTriple rdfPredicate rdfsRange rdfsResource,
    iriTriple rdfObject rdfsRange rdfsResource,
    iriTriple rdfsMember rdfsRange rdfsResource,
    iriTriple rdfFirst rdfsRange rdfsResource,
    iriTriple rdfRest rdfsRange rdfList,
    iriTriple rdfsSeeAlso rdfsRange rdfsResource,
    iriTriple rdfsIsDefinedBy rdfsRange rdfsResource,
    iriTriple rdfsComment rdfsRange rdfsLiteral,
    iriTriple rdfsLabel rdfsRange rdfsLiteral,
    iriTriple rdfValue rdfsRange rdfsResource,

    iriTriple rdfAlt rdfsSubClassOf rdfsContainer,
    iriTriple rdfBag rdfsSubClassOf rdfsContainer,
    iriTriple rdfSeq rdfsSubClassOf rdfsContainer,
    iriTriple rdfsContainerMembershipProperty rdfsSubClassOf rdfProperty,
    iriTriple rdfsIsDefinedBy rdfsSubPropertyOf rdfsSeeAlso,
    iriTriple rdfXMLLiteral rdfType rdfsDatatype,
    iriTriple rdfXMLLiteral rdfsSubClassOf rdfsLiteral,
    iriTriple rdfsDatatype rdfsSubClassOf rdfsClass ]

/-- §9.3, the per-`rdf:_n` RDFS axioms: "rdf:_1 rdf:type
rdfs:ContainerMembershipProperty . rdf:_1 rdfs:domain rdfs:Resource .
rdf:_1 rdfs:range rdfs:Resource ." for every n in the slice. -/
def rdfsContainerAxioms (cmps : List WfIri) : Graph :=
  cmps.flatMap (fun c =>
    [ iriTriple c rdfType rdfsContainerMembershipProperty,
      iriTriple c rdfsDomain rdfsResource,
      iriTriple c rdfsRange rdfsResource ])

/-- rdfs1 as an axiom table: every recognised datatype IRI is an
`rdfs:Datatype`. (§9.2 rdfs1 has no premise from the graph.) -/
def datatypeAxioms (D : List WfIri) : Graph :=
  D.map (fun d => iriTriple d rdfType rdfsDatatype)

/-- The RDFS axiom set for a datatype map `D` and an `rdf:_n` slice. -/
def rdfsAxiomaticTriples (D cmps : List WfIri) : Graph :=
  rdfsAxiomaticTriplesFixed ++ rdfsContainerAxioms cmps ++ datatypeAxioms D

/-- Everything the RDFS regime seeds: RDF axioms, RDFS axioms, rdfs1. -/
def axiomaticTriples (D cmps : List WfIri) : Graph :=
  rdfAxiomaticTriples cmps ++ rdfsAxiomaticTriples D cmps

/-! ## The derivation relation

`DerivesFull ax g t`: `t` is derivable from the graph `g` together with
the axiom set `ax` by the rules above. `ax` is a parameter rather than
`axiomaticTriples D cmps` baked in, so the relation also serves the
pure-RDF regime (`ax := rdfAxiomaticTriples cmps`) and the statement
stays independent of how a caller slices the infinite families. -/

inductive DerivesFull (ax : Graph) (g : Graph) : Triple → Prop where
  /-- Every triple of the graph. -/
  | base {t : Triple} (h : t ∈ g) : DerivesFull ax g t
  /-- Every axiomatic triple (§8.2, §9.3, and rdfs1 over D). -/
  | axiomatic {t : Triple} (h : t ∈ ax) : DerivesFull ax g t
  /-- **rdfD2** — §8.1: `xxx aaa yyy .` ⊢ `aaa rdf:type rdf:Property .` -/
  | rdfD2 {s : Subject} {p : WfIri} {o : Term}
      (h : DerivesFull ax g ⟨s, p, o⟩) :
      DerivesFull ax g ⟨Subject.iri p, rdfType, Term.iri rdfProperty⟩
  /-- **rdfs2** — as in `RdfsCore.Derives.rdfs2`. -/
  | rdfs2 {p : WfIri} {cls : Term} {s : Subject} {o : Term}
      (hdecl : DerivesFull ax g ⟨Subject.iri p, rdfsDomain, cls⟩)
      (hdata : DerivesFull ax g ⟨s, p, o⟩) :
      DerivesFull ax g ⟨s, rdfType, cls⟩
  /-- **rdfs3** — as in `RdfsCore.Derives.rdfs3` (object must be usable
  as a subject; the generalised-RDF literal case is dropped). -/
  | rdfs3 {p : WfIri} {cls : Term} {s : Subject} {o : Term} {osub : Subject}
      (hdecl : DerivesFull ax g ⟨Subject.iri p, rdfsRange, cls⟩)
      (hdata : DerivesFull ax g ⟨s, p, o⟩)
      (hsub  : o.toSubject? = some osub) :
      DerivesFull ax g ⟨osub, rdfType, cls⟩
  /-- **rdfs4a** — §9.2: `xxx aaa yyy .` ⊢ `xxx rdf:type rdfs:Resource .` -/
  | rdfs4a {s : Subject} {p : WfIri} {o : Term}
      (h : DerivesFull ax g ⟨s, p, o⟩) :
      DerivesFull ax g ⟨s, rdfType, Term.iri rdfsResource⟩
  /-- **rdfs4b** — §9.2: `xxx aaa yyy .` ⊢ `yyy rdf:type rdfs:Resource .`
  (when `yyy` can be a subject). -/
  | rdfs4b {s : Subject} {p : WfIri} {o : Term} {osub : Subject}
      (h : DerivesFull ax g ⟨s, p, o⟩)
      (hsub : o.toSubject? = some osub) :
      DerivesFull ax g ⟨osub, rdfType, Term.iri rdfsResource⟩
  /-- **rdfs5** — as in `RdfsCore.Derives.rdfs5`. -/
  | rdfs5 {a : Subject} {b : Term} {bsub : Subject} {c : Term}
      (h1   : DerivesFull ax g ⟨a, rdfsSubPropertyOf, b⟩)
      (hsub : b.toSubject? = some bsub)
      (h2   : DerivesFull ax g ⟨bsub, rdfsSubPropertyOf, c⟩) :
      DerivesFull ax g ⟨a, rdfsSubPropertyOf, c⟩
  /-- **rdfs6** — §9.2: `xxx rdf:type rdf:Property .` ⊢
  `xxx rdfs:subPropertyOf xxx .` -/
  | rdfs6 {x : Subject}
      (h : DerivesFull ax g ⟨x, rdfType, Term.iri rdfProperty⟩) :
      DerivesFull ax g ⟨x, rdfsSubPropertyOf, x.toTerm⟩
  /-- **rdfs7** — as in `RdfsCore.Derives.rdfs7`. -/
  | rdfs7 {p q : WfIri} {s : Subject} {o : Term}
      (hdecl : DerivesFull ax g ⟨Subject.iri p, rdfsSubPropertyOf, Term.iri q⟩)
      (hdata : DerivesFull ax g ⟨s, p, o⟩) :
      DerivesFull ax g ⟨s, q, o⟩
  /-- **rdfs8** — §9.2: `xxx rdf:type rdfs:Class .` ⊢
  `xxx rdfs:subClassOf rdfs:Resource .` -/
  | rdfs8 {x : Subject}
      (h : DerivesFull ax g ⟨x, rdfType, Term.iri rdfsClass⟩) :
      DerivesFull ax g ⟨x, rdfsSubClassOf, Term.iri rdfsResource⟩
  /-- **rdfs9** — as in `RdfsCore.Derives.rdfs9`. -/
  | rdfs9 {s : Subject} {a : WfIri} {b : Term}
      (hdata : DerivesFull ax g ⟨s, rdfType, Term.iri a⟩)
      (hdecl : DerivesFull ax g ⟨Subject.iri a, rdfsSubClassOf, b⟩) :
      DerivesFull ax g ⟨s, rdfType, b⟩
  /-- **rdfs10** — §9.2: `xxx rdf:type rdfs:Class .` ⊢
  `xxx rdfs:subClassOf xxx .` -/
  | rdfs10 {x : Subject}
      (h : DerivesFull ax g ⟨x, rdfType, Term.iri rdfsClass⟩) :
      DerivesFull ax g ⟨x, rdfsSubClassOf, x.toTerm⟩
  /-- **rdfs11** — as in `RdfsCore.Derives.rdfs11`. -/
  | rdfs11 {a : Subject} {b : Term} {bsub : Subject} {c : Term}
      (h1   : DerivesFull ax g ⟨a, rdfsSubClassOf, b⟩)
      (hsub : b.toSubject? = some bsub)
      (h2   : DerivesFull ax g ⟨bsub, rdfsSubClassOf, c⟩) :
      DerivesFull ax g ⟨a, rdfsSubClassOf, c⟩
  /-- **rdfs12** — §9.2: `xxx rdf:type rdfs:ContainerMembershipProperty .`
  ⊢ `xxx rdfs:subPropertyOf rdfs:member .` -/
  | rdfs12 {x : Subject}
      (h : DerivesFull ax g ⟨x, rdfType, Term.iri rdfsContainerMembershipProperty⟩) :
      DerivesFull ax g ⟨x, rdfsSubPropertyOf, Term.iri rdfsMember⟩
  /-- **rdfs13** — §9.2: `xxx rdf:type rdfs:Datatype .` ⊢
  `xxx rdfs:subClassOf rdfs:Literal .` -/
  | rdfs13 {x : Subject}
      (h : DerivesFull ax g ⟨x, rdfType, Term.iri rdfsDatatype⟩) :
      DerivesFull ax g ⟨x, rdfsSubClassOf, Term.iri rdfsLiteral⟩

/-! ## The eight single-premise rows, executable

Each `…For t` reads `t` as the row's only premise and returns the
conclusions it licenses. They are premise-local (no second lookup in
the graph), which keeps their soundness lemmas one `cases` each. -/

/-- Is `t` of the shape `x rdf:type <c>`? -/
def typedAs (t : Triple) (c : WfIri) : Bool :=
  t.p == rdfType && t.o == Term.iri c

/-- **rdfD2.** -/
def rdfD2For (t : Triple) : List Triple :=
  [⟨Subject.iri t.p, rdfType, Term.iri rdfProperty⟩]

/-- **rdfs4a.** -/
def rdfs4aFor (t : Triple) : List Triple :=
  [⟨t.s, rdfType, Term.iri rdfsResource⟩]

/-- **rdfs4b** (object usable as a subject). -/
def rdfs4bFor (t : Triple) : List Triple :=
  match t.o.toSubject? with
  | some os => [⟨os, rdfType, Term.iri rdfsResource⟩]
  | none    => []

/-- **rdfs6.** -/
def rdfs6For (t : Triple) : List Triple :=
  if typedAs t rdfProperty then [⟨t.s, rdfsSubPropertyOf, t.s.toTerm⟩] else []

/-- **rdfs8.** -/
def rdfs8For (t : Triple) : List Triple :=
  if typedAs t rdfsClass then [⟨t.s, rdfsSubClassOf, Term.iri rdfsResource⟩] else []

/-- **rdfs10.** -/
def rdfs10For (t : Triple) : List Triple :=
  if typedAs t rdfsClass then [⟨t.s, rdfsSubClassOf, t.s.toTerm⟩] else []

/-- **rdfs12.** -/
def rdfs12For (t : Triple) : List Triple :=
  if typedAs t rdfsContainerMembershipProperty
  then [⟨t.s, rdfsSubPropertyOf, Term.iri rdfsMember⟩] else []

/-- **rdfs13.** -/
def rdfs13For (t : Triple) : List Triple :=
  if typedAs t rdfsDatatype then [⟨t.s, rdfsSubClassOf, Term.iri rdfsLiteral⟩] else []

/-! ## One step, and the fixpoint -/

/-- Everything the full rule set concludes from `g` in one round: the
rdfs-core conclusions, then the eight rows above, each read from the
input snapshot (the same snapshot discipline `Closure.stepConclusions`
documents). -/
def fullStepConclusions (g : Graph) : List Triple :=
  stepConclusions g ++
  g.flatMap rdfD2For ++
  g.flatMap rdfs4aFor ++
  g.flatMap rdfs4bFor ++
  g.flatMap rdfs6For ++
  g.flatMap rdfs8For ++
  g.flatMap rdfs10For ++
  g.flatMap rdfs12For ++
  g.flatMap rdfs13For

/-- One round: `g` plus every conclusion, set-wise. -/
def fullStep (g : Graph) : Graph :=
  addAll g (fullStepConclusions g)

/-- Fuel-bounded fixpoint with the F\* length test, exactly as
`Closure.closure`. -/
def fullClosureLoop (g : Graph) (fuel : Nat) : Graph :=
  match fuel with
  | 0     => g
  | n + 1 =>
      let g' := fullStep g
      if g'.length = g.length then g else fullClosureLoop g' n

/-- Fuel budget. Same counting shape as `closureFuelBound`: the loop
only recurses on strict growth, and every conclusion is built from
components of the seeded graph plus the fixed vocabulary IRIs this
module names, so the closure of an `n`-triple seed holds at most
`(n + k) * (n + k + 1) * (n + k)` triples for the constant `k` of
vocabulary terms. The bound is stated, not proved (the same named
obligation as `Closure.closureFuelBound`). -/
def fullClosureFuelBound (g : Graph) : Nat :=
  let n := g.length + 32
  n * (n + 1) * n + 1

/-- **The RDFS-regime closure** of `g` under datatype map `D` and
`rdf:_n` slice `cmps`: seed the axioms, then run the full rule set to
saturation. -/
def fullClosure (D cmps : List WfIri) (g : Graph) : Graph :=
  let seeded := addAll g (axiomaticTriples D cmps)
  fullClosureLoop seeded (fullClosureFuelBound seeded)

/-- **The RDF-regime closure** (§8.1 only): the RDF axiomatic triples
and rdfD2. rdfD2 cannot chain (its conclusion `aaa rdf:type
rdf:Property` feeds rdfD2 only to yield `rdf:type rdf:type
rdf:Property`, which is an axiom), so one pass over the seeded graph
is already saturated. -/
def rdfClosure (cmps : List WfIri) (g : Graph) : Graph :=
  let seeded := addAll g (rdfAxiomaticTriples cmps)
  addAll seeded (seeded.flatMap rdfD2For)

end L4Factoidal.RDFS
