/-
L4Factoidal.OWL.CountingOracle — the counting-fragment consistency path.

Port of `formal/fstar/Tableau.CountingOracle.fst` (1,663 lines).

The clash-detecting refutation tableau decides OWL 2 DL consistency for
everything except one fragment: finite-model cardinality COUNTING, where
the contradiction is a linear system over the sizes of named classes
(the pigeonhole shape). This module is that fragment — recognised,
extracted, encoded, and, for the systems the corpus actually produces,
DECIDED inside the verified boundary.

## The single `assume val` becomes a parameter

The F\* module's one `assume val` is

    assume val z3_check_sat : smtlib:string -> rlimit:nat -> Tot z3_verdict

realised by glue that, in its Phase 0, returns `Z3_Unknown`
unconditionally. Lean has no `assume val` and no axiom, so the oracle is
a PARAMETER: `SatOracle` is a function a caller supplies. `noOracle`
below is the Phase-0 stub, written out rather than assumed.

That is not a workaround. An assumed value is a fact about the world the
proof rests on; a parameter is an input the theorems quantify over. The
verdict below (`classSizeUnsat`) does not consult the oracle at all, and
its soundness theorem holds for every oracle, because the decision is
the Farkas validator rather than the solver.

## What is PROVED, and what is prose

PROVED here, and the reason this path exists at all:
`farkasSound` — when `farkasCheck` accepts a multiplier vector, NO
integer assignment satisfies the linear system. The combined coefficient
vector is zero, so the combined left-hand side is 0 for every `x`, while
the combined right-hand side is strictly positive and the weighted
combination of satisfied constraints would force LHS ≥ RHS.
`classSizeUnsat_sound` lifts it to the system built from a graph.

NOT proved, and the F\* module is equally explicit about it: that UNSAT
of the class-size system IMPLIES the closure is inconsistent under
Direct Semantics. The FIBER / BIJECTION / DISJOINT-UNION / ONEOF
arguments that justify each row are prose in both trees. What is inside
the verified boundary is the LIA decision — the arithmetic — not the
model theory that licenses the rows.

Read `classSizeUnsat g = true` as "the linear system this module builds
from `g` has no integer solution, and that is proved", NOT as "`g` is
inconsistent, and that is proved".

## dl-909 is not decided by this path, on purpose

Its class-size system is genuinely satisfiable — the all-empty
assignment with `|only-d| ≥ 1` is a model — so no Farkas certificate
exists and the checker returns `false`. Deriving `|finite| ≥ 1` would
need an UNSOUND nonemptiness rule, which is not added.
-/
import L4Factoidal.OWL.Vocabulary
import L4Factoidal.RDFS.Vocabulary
import L4Factoidal.RDF.Graph

namespace L4Factoidal.OWL.CountingOracle

open L4Factoidal.RDF
open L4Factoidal.OWL.RL

/-! ## 1. The verdict, and the oracle seam -/

/-- A closed sum. No solver internals reach this module. -/
inductive Verdict where
  | sat
  | unsat
  | unknown
  | timeout
deriving DecidableEq, Repr, Inhabited

/-- A satisfiability oracle: SMT-LIB 2 text and an instruction budget in,
a verdict out. The F\* tree assumes one; here a caller passes one. -/
abbrev SatOracle := String → Nat → Verdict

/-- The Phase-0 stub, written out rather than assumed: consult nothing,
answer `unknown`. A caller with no solver uses this and the engine's
behaviour is unchanged. -/
def noOracle : SatOracle := fun _ _ => .unknown

/-! ## 2. Vocabulary this module needs and the shared files do not -/

private def mkIri (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

def owlCardinality : WfIri := mkIri "http://www.w3.org/2002/07/owl#cardinality"
def owlMinQualifiedCardinality : WfIri :=
  mkIri "http://www.w3.org/2002/07/owl#minQualifiedCardinality"
def owlQualifiedCardinality : WfIri :=
  mkIri "http://www.w3.org/2002/07/owl#qualifiedCardinality"
def owlDatatypeComplementOf : WfIri :=
  mkIri "http://www.w3.org/2002/07/owl#datatypeComplementOf"
def owlOnDatatype : WfIri := mkIri "http://www.w3.org/2002/07/owl#onDatatype"
def owlWithRestrictions : WfIri :=
  mkIri "http://www.w3.org/2002/07/owl#withRestrictions"
def owlOnDataRange : WfIri := mkIri "http://www.w3.org/2002/07/owl#onDataRange"
def owlDatatypeProperty : WfIri :=
  mkIri "http://www.w3.org/2002/07/owl#DatatypeProperty"

def xsdMinInclusive : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "minInclusive")
def xsdMaxInclusive : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "maxInclusive")
def xsdMinExclusive : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "minExclusive")
def xsdMaxExclusive : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "maxExclusive")
def xsdPattern : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "pattern")
def xsdLength : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "length")
def xsdMinLength : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "minLength")
def xsdMaxLength : WfIri := mkIri ("http://www.w3.org/2001/XMLSchema#" ++ "maxLength")

/-! ### Graph lookups

Local, over a plain `Graph`. The F\* module reads through
`Tableau`'s helpers; the shapes are the same. -/

def firstObjectOf (g : Graph) (s : Subject) (p : WfIri) : Option Term :=
  (g.find? (fun t => t.s == s && t.p == p)).map (·.o)

def objectsOfSubj (g : Graph) (s : Subject) (p : WfIri) : List Term :=
  (g.filter (fun t => t.s == s && t.p == p)).map (·.o)

def termAsSubject : Term → Option Subject
  | .iri i => some (.iri i)
  | .bnode b => some (.bnode b)
  | _ => none

/-- Walk an `rdf:first`/`rdf:rest` list, fuel-bounded. -/
def walkList (g : Graph) : Term → Nat → List Term
  | _, 0 => []
  | t, fuel + 1 =>
      match termAsSubject t with
      | none => []
      | some s =>
          match firstObjectOf g s rdfFirst with
          | none => []
          | some hd =>
              match firstObjectOf g s rdfRest with
              | some rest => hd :: walkList g rest fuel
              | none => [hd]

/-- Multi-digit non-negative decimal. The tableau's own reader covers
only 0–9; dl-910's bounds are 20 / 30 / 601. -/
def parseNat (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldl
    (fun acc c => match acc with
                  | none => none
                  | some n => if c.isDigit then some (n * 10 + (c.toNat - 48))
                              else none)
    (some 0)

/-! ## 3. The counting AST

The fragment: object-property cardinality bounds plus pairwise
distinctness over a finite named domain. No datatypes, no negation, no
general boolean class structure — the recogniser in §5 keeps inputs
inside that shape. -/

inductive CardBound where
  | min (k : Nat)
  | max (k : Nat)
  | exact (k : Nat)
deriving DecidableEq, Repr, Inhabited

/-- One bound on `subj`, over object property `role`, optionally
qualified by a named filler. -/
structure CountAxiom where
  subj   : Term
  role   : WfIri
  filler : Option WfIri
  bound  : CardBound
deriving DecidableEq, Repr

structure CountingAst where
  individuals : List Term := []
  axioms      : List CountAxiom := []
  distinct    : List (Term × Term) := []
deriving DecidableEq, Repr, Inhabited

/-! ## 4. Extraction -/

def isCardPred (p : WfIri) : Bool :=
  p == owlMinCardinality || p == owlMaxCardinality || p == owlCardinality
    || p == owlMinQualifiedCardinality || p == owlMaxQualifiedCardinality
    || p == owlQualifiedCardinality

def boundOf (p : WfIri) (k : Nat) : Option CardBound :=
  if p == owlMinCardinality || p == owlMinQualifiedCardinality then some (.min k)
  else if p == owlMaxCardinality || p == owlMaxQualifiedCardinality then some (.max k)
  else if p == owlCardinality || p == owlQualifiedCardinality then some (.exact k)
  else none

/-- One restriction triple into one axiom, pulling `owl:onProperty`
(required) and `owl:onClass` (optional) off the same subject. A bound
that does not read as a number yields NO axiom rather than a guessed
one, which is the sound direction under an open world. -/
def axiomOf (g : Graph) (t : Triple) : Option CountAxiom :=
  if !isCardPred t.p then none
  else match t.o with
    | .literal l =>
        match parseNat l.val.lexicalForm with
        | none => none
        | some k =>
            match boundOf t.p k with
            | none => none
            | some b =>
                match firstObjectOf g t.s owlOnProperty with
                | some (.iri role) =>
                    some { subj := t.s.toTerm, role := role
                         , filler := match firstObjectOf g t.s owlOnClass with
                                     | some (.iri c) => some c
                                     | _ => none
                         , bound := b }
                | _ => none
    | _ => none

def axiomsOf (g : Graph) : List CountAxiom := g.filterMap (axiomOf g)

def distinctPairs (g : Graph) : List (Term × Term) :=
  g.filterMap (fun t =>
    if t.p == owlDifferentFrom then some (t.s.toTerm, t.o) else none)

/-- Order-preserving dedup keeping the FIRST occurrence, by the engine
term equality. -/
def dedupTerms : List Term → List Term
  | [] => []
  | h :: tl => if tl.any (fun u => u.eqb h) then dedupTerms tl
               else h :: dedupTerms tl

def extractCountingFragment (g : Graph) : CountingAst :=
  let axs := axiomsOf g
  let dis := distinctPairs g
  { individuals := dedupTerms (dis.map Prod.fst ++ dis.map Prod.snd
                                ++ axs.map CountAxiom.subj)
  , axioms := axs
  , distinct := dis }

/-! ## 5. The recogniser

`inCountingFragment g` is true ONLY when the inconsistency question sits
entirely inside the fragment the encoding is faithful for. False means
"do not consult the oracle" — erring toward false is always sound, since
the verified tableau's verdict then stands.

REJECTED: datatype facets and data-range reasoning (the inconsistency
would live in a data range, not in object-successor counting), and
general boolean class structure via an AUTHORED `owl:complementOf`.

An engine-generated complement is NOT authored structure: the RL closure
materialises a canonical complement bnode per named class from every
`owl:disjointWith`, and the refutation path generates negation
scaffolding. Rejecting those would drop legitimate disjoint-union
counting problems, so they are exempted by prefix. -/

def isFacetPred (p : WfIri) : Bool :=
  p == xsdMinInclusive || p == xsdMaxInclusive || p == xsdMinExclusive
    || p == xsdMaxExclusive || p == xsdPattern || p == xsdLength
    || p == xsdMinLength || p == xsdMaxLength

def rlCanonicalPrefix : String := "__rl_"
def peScaffoldPrefix : String := "__factoidal_pe_"

def bnodeIsEngineGenerated (b : BNodeId) : Bool :=
  b.startsWith rlCanonicalPrefix || b.startsWith peScaffoldPrefix

def authoredComplement (t : Triple) : Bool :=
  t.p == owlComplementOf &&
    (match t.s with
     | .bnode b => !(bnodeIsEngineGenerated b)
     | .iri _   => true)

def rejectTriple (t : Triple) : Bool :=
  t.p == owlOnDatatype || t.p == owlWithRestrictions
    || t.p == owlDatatypeComplementOf || t.p == owlOnDataRange
    || authoredComplement t || isFacetPred t.p
    || (t.p == rdfType && (match t.o with
                           | .iri i => i == owlDatatypeProperty
                           | _ => false))

/-- A counting CONSTRUCT: a cardinality restriction, or a functional /
inverse-functional property declaration. Its presence is what makes the
question a counting problem at all. -/
def countingTriple (t : Triple) : Bool :=
  isCardPred t.p
    || (t.p == rdfType && (match t.o with
                           | .iri i => i == owlFunctionalProperty
                                        || i == owlInverseFunctionalProperty
                           | _ => false))

def inCountingFragment (g : Graph) : Bool :=
  !(g.any rejectTriple) && g.any countingTriple

/-! ## 6. The restriction encoder (QF_LIA)

One Int successor-count per cardinality axiom, `≥ 0`, bounded per the
min / max / exact bound. Two axioms on the SAME (subject, role, filler)
key share one variable, so a min-k above a max-m is `(>= v k)` and
`(<= v m)` — unsat exactly when `k > m`. Symbol names are index-based, so
no IRI text is embedded and no SMT-LIB escaping is needed. -/

def indexOfTerm (xs : List Term) (t : Term) : Nat :=
  match xs.findIdx? (fun u => u.eqb t) with
  | some i => i
  | none   => xs.length

def indexOfIri (xs : List WfIri) (i : WfIri) : Nat :=
  match xs.idxOf? i with
  | some k => k
  | none   => xs.length

def dedupIris : List WfIri → List WfIri
  | [] => []
  | h :: tl => if tl.contains h then dedupIris tl else h :: dedupIris tl

def varName (inds : List Term) (roles fillers : List WfIri) (a : CountAxiom) :
    String :=
  "n_s" ++ toString (indexOfTerm inds a.subj)
    ++ "_r" ++ toString (indexOfIri roles a.role)
    ++ "_c" ++ (match a.filler with
                | some c => toString (indexOfIri fillers c)
                | none   => "u")

def boundAssert (name : String) : CardBound → String
  | .min k   => "(assert (>= " ++ name ++ " " ++ toString k ++ "))\n"
  | .max k   => "(assert (<= " ++ name ++ " " ++ toString k ++ "))\n"
  | .exact k => "(assert (= "  ++ name ++ " " ++ toString k ++ "))\n"

def dedupStrings : List String → List String
  | [] => []
  | h :: tl => if tl.contains h then dedupStrings tl else h :: dedupStrings tl

def encodeCountingFragment (ast : CountingAst) : String :=
  let inds := ast.individuals
  let axs := ast.axioms
  let roles := dedupIris (axs.map CountAxiom.role)
  let fillers := dedupIris (axs.filterMap CountAxiom.filler)
  let names := dedupStrings (axs.map (varName inds roles fillers))
  let idDecls := String.join
    ((List.range inds.length).map
      (fun i => "(declare-const id_" ++ toString i ++ " Int)\n"))
  let distinctAsserts := String.join (ast.distinct.map (fun (a, b) =>
    let ia := indexOfTerm inds a
    let ib := indexOfTerm inds b
    if ia < inds.length && ib < inds.length && ia != ib then
      "(assert (not (= id_" ++ toString ia ++ " id_" ++ toString ib ++ ")))\n"
    else ""))
  let decls := String.join (names.map (fun h =>
    "(declare-const " ++ h ++ " Int)\n(assert (>= " ++ h ++ " 0))\n"))
  let bounds := String.join (axs.map (fun a =>
    boundAssert (varName inds roles fillers a) a.bound))
  "(set-logic QF_LIA)\n; counting-fragment encoding (restriction counts)\n"
    ++ idDecls ++ distinctAsserts ++ decls ++ bounds ++ "(check-sat)\n"

/-! ## 7. The class-size relations

The restriction encoder above is faithful to a single min-above-max
clash on ONE restriction subject. The residual finite-model failures are
class-size MULTIPLICATION arguments: the contradiction is a linear
system over the CARDINALITIES of named classes, related by three
relations.

* **FIBER** — `p` functional with domain `D` and inverse `ip`,
  `D ⊑ ∃p.X`, `X ≡ (ip exactly k)`: gives `|D| = k·|X|`.
* **BIJECTION** — `p` functional and inverse-functional with inverse
  `ip`, `D ⊑ ∃p.Y` and `Y ⊑ ∃ip.D`: gives `|D| = |Y|`.
* **DISJOINT UNION** — `Z ≡ m1 ⊔ m2` with `m1` disjoint from `m2`:
  gives `|Z| = |m1| + |m2|`.
* **ONEOF nonemptiness** — a class enumerated by a non-empty
  `owl:oneOf`: gives `|C| ≥ 1`.

These are the readers both the SMT emitter (§8) and the linear-system
builder (§10) use, so the two describe the same system by construction
rather than by inspection. -/

def allIris (g : Graph) : List WfIri :=
  g.flatMap (fun t =>
    (match t.s with | .iri i => [i] | _ => []) ++
    (match t.o with | .iri i => [i] | _ => []))

def propsTyped (g : Graph) (cls : WfIri) : List WfIri :=
  g.filterMap (fun t =>
    if t.p == rdfType && (match t.o with | .iri i => i == cls | _ => false) then
      match t.s with | .iri i => some i | _ => none
    else none)

/-- The first non-`owl:Thing` `rdfs:domain` of `p`: the closure also
asserts `p rdfs:domain owl:Thing`, which has to be skipped. -/
def findDom (g : Graph) (p : WfIri) : Option WfIri :=
  (g.filterMap (fun t =>
    if t.p == RL.rdfsDomain && (match t.s with | .iri i => i == p | _ => false) then
      match t.o with
      | .iri i => if i == owlThing then none else some i
      | _ => none
    else none)).head?

/-- The inverse of `p`, either direction of `owl:inverseOf`. -/
def findInv (g : Graph) (p : WfIri) : Option WfIri :=
  (g.filterMap (fun t =>
    if t.p == owlInverseOf then
      match t.s, t.o with
      | .iri a, .iri b => if a == p then some b else if b == p then some a else none
      | _, _ => none
    else none)).head?

def disjointPair (g : Graph) (a b : WfIri) : Bool :=
  g.any (fun t =>
    t.p == owlDisjointWith &&
      (match t.s, t.o with
       | .iri x, .iri y => (x == a && y == b) || (x == b && y == a)
       | _, _ => false))

/-- Restriction bnodes a named class is linked to, by `rdfs:subClassOf`
or `owl:equivalentClass` — both directions of an equivalence appear
after closure. -/
def restrOf (g : Graph) (c : WfIri) : List Term :=
  objectsOfSubj g (.iri c) RL.rdfsSubClassOf
    ++ objectsOfSubj g (.iri c) owlEquivalentClass

/-- Among restriction bnodes, the `someValuesFrom` target of the first
whose `onProperty` is `p`. -/
def svfVia (g : Graph) (bs : List Term) (p : WfIri) : Option WfIri :=
  bs.findSome? (fun b =>
    match termAsSubject b with
    | none => none
    | some s =>
        match firstObjectOf g s owlOnProperty with
        | some (.iri pp) =>
            if pp == p then
              match firstObjectOf g s owlSomeValuesFrom with
              | some (.iri x) => some x
              | _ => none
            else none
        | _ => none)

/-- Among restriction bnodes, the exact `owl:cardinality` of the first
whose `onProperty` is `invp`. -/
def exactCardVia (g : Graph) (bs : List Term) (invp : WfIri) : Option Nat :=
  bs.findSome? (fun b =>
    match termAsSubject b with
    | none => none
    | some s =>
        match firstObjectOf g s owlOnProperty with
        | some (.iri pp) =>
            if pp == invp then
              match firstObjectOf g s owlCardinality with
              | some (.literal l) => parseNat l.val.lexicalForm
              | _ => none
            else none
        | _ => none)

def listNonEmpty (g : Graph) (head : Term) : Bool :=
  match termAsSubject head with
  | some s => (firstObjectOf g s rdfFirst).isSome
  | none   => false

def classHasOneOf (g : Graph) (c : WfIri) : Bool :=
  (match firstObjectOf g (.iri c) owlOneOf with
   | some l => listNonEmpty g l
   | none   => false)
  || (objectsOfSubj g (.iri c) owlEquivalentClass).any (fun b =>
       match termAsSubject b with
       | some s => match firstObjectOf g s owlOneOf with
                   | some l => listNonEmpty g l
                   | none => false
       | none => false)

/-- The `Z ≡ m1 ⊔ m2` pattern with `m1` disjoint from `m2`, read off one
triple. Both the SMT emitter and the linear-system builder go through
this, so they cannot drift apart. -/
def unionPairOf (g : Graph) (t : Triple) : Option (WfIri × WfIri × WfIri) :=
  if t.p != owlEquivalentClass then none
  else match t.s, t.o with
    | .iri z, .bnode _ =>
        match termAsSubject t.o with
        | none => none
        | some bs =>
            match firstObjectOf g bs owlUnionOf with
            | none => none
            | some lterm =>
                match walkList g lterm g.length with
                | [.iri m1, .iri m2] =>
                    if disjointPair g m1 m2 then some (z, m1, m2) else none
                | _ => none
    | _, _ => none

/-- `(D, X, k)` for the FIBER relation on `p`, when it applies. -/
def fiberOf (g : Graph) (p : WfIri) : Option (WfIri × WfIri × Nat) :=
  match findDom g p, findInv g p with
  | some d, some ip =>
      match svfVia g (restrOf g d) p with
      | none => none
      | some x =>
          match exactCardVia g (restrOf g x) ip with
          | none => none
          | some k => some (d, x, k)
  | _, _ => none

/-- `(D, Y)` for the BIJECTION relation on `p`/`ip` at class `d`. -/
def bijOf (g : Graph) (p ip : WfIri) (d : WfIri) : Option (WfIri × WfIri) :=
  match svfVia g (restrOf g d) p with
  | none => none
  | some y =>
      match svfVia g (restrOf g y) ip with
      | some dback => if dback == d then some (d, y) else none
      | none => none

def iriInter (xs ys : List WfIri) : List WfIri := xs.filter (ys.contains ·)

/-- The functional-and-inverse-functional properties: the ones a
bijection relation can rest on. -/
def bijProps (g : Graph) : List WfIri :=
  iriInter (propsTyped g owlFunctionalProperty)
           (propsTyped g owlInverseFunctionalProperty)

/-! ## 8. The class-size SMT encoder

The same relations as §7, emitted as QF_LIA text for a caller that has a
solver. The verified path in §9–§11 does not use it. -/

def cvar (classes : List WfIri) (c : WfIri) : String :=
  "c" ++ toString (indexOfIri classes c)

def encodeCountingSmt (g : Graph) : String :=
  let classes := dedupIris (allIris g)
  let fprops := propsTyped g owlFunctionalProperty
  let bprops := bijProps g
  let classDecls := String.join (classes.map (fun c =>
    "(declare-const " ++ cvar classes c ++ " Int)\n"
      ++ "(assert (>= " ++ cvar classes c ++ " 0))\n"))
  let fiberAsserts := String.join (fprops.map (fun p =>
    match fiberOf g p with
    | some (d, x, k) =>
        "(assert (= " ++ cvar classes d ++ " (* " ++ toString k ++ " "
          ++ cvar classes x ++ ")))\n"
    | none => ""))
  let bijAsserts := String.join (bprops.map (fun p =>
    match findInv g p with
    | some ip => String.join (classes.map (fun d =>
        match bijOf g p ip d with
        | some (_, y) =>
            "(assert (= " ++ cvar classes d ++ " " ++ cvar classes y ++ "))\n"
        | none => ""))
    | none => ""))
  let unionAsserts := String.join (g.map (fun t =>
    match unionPairOf g t with
    | some (z, m1, m2) =>
        "(assert (= " ++ cvar classes z ++ " (+ " ++ cvar classes m1 ++ " "
          ++ cvar classes m2 ++ ")))\n"
    | none => ""))
  let oneofAsserts := String.join (classes.map (fun c =>
    if classHasOneOf g c then "(assert (>= " ++ cvar classes c ++ " 1))\n" else ""))
  "(set-logic QF_LIA)\n; counting-fragment class-size encoding\n"
    ++ classDecls ++ fiberAsserts ++ bijAsserts ++ unionAsserts
    ++ oneofAsserts ++ "(check-sat)\n"

/-! ## 9. Linear systems and the Farkas validator

This is the part that replaces a solver call with a proof. -/

/-- One constraint over the class-size variables `c0 … c(N-1)`:
`isEq` means `coeffs · x = rhs`, otherwise `coeffs · x ≥ rhs`. -/
structure LinConstraint where
  coeffs : List Int
  rhs    : Int
  isEq   : Bool
deriving DecidableEq, Repr, Inhabited

def linDot : List Int → List Int → Int
  | c :: cs, v :: vs => c * v + linDot cs vs
  | _, _ => 0

def linSat1 (c : LinConstraint) (x : List Int) : Bool :=
  if c.isEq then linDot c.coeffs x == c.rhs else linDot c.coeffs x ≥ c.rhs

def linSat (cs : List LinConstraint) (x : List Int) : Bool := cs.all (linSat1 · x)

/-- One integer multiplier per constraint. A `≥` constraint takes a
NONNEGATIVE multiplier; an equality takes any integer, since both
directions are available. -/
def validMults : List LinConstraint → List Int → Bool
  | c :: cs, m :: ms => (if c.isEq then true else m ≥ 0) && validMults cs ms
  | [], [] => true
  | _, _ => false

def weightedLhs : List LinConstraint → List Int → List Int → Int
  | c :: cs, m :: ms, x => m * linDot c.coeffs x + weightedLhs cs ms x
  | _, _, _ => 0

def weightedRhs : List LinConstraint → List Int → Int
  | c :: cs, m :: ms => m * c.rhs + weightedRhs cs ms
  | _, _ => 0

def zeros : Nat → List Int
  | 0 => []
  | n + 1 => 0 :: zeros n

def vscale (m : Int) (v : List Int) : List Int := v.map (m * ·)

def vadd : List Int → List Int → List Int
  | ha :: ta, hb :: tb => (ha + hb) :: vadd ta tb
  | _, _ => []

/-- `Σ mᵢ · coeffsᵢ`, of length `n`. -/
def combCoeffs (n : Nat) : List LinConstraint → List Int → List Int
  | c :: cs, m :: ms => vadd (vscale m c.coeffs) (combCoeffs n cs ms)
  | _, _ => zeros n

def allLen (n : Nat) (cs : List LinConstraint) : Bool :=
  cs.all (fun c => c.coeffs.length == n)

/-! ### Length lemmas -/

theorem zeros_len (n : Nat) : (zeros n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [zeros, ih]

theorem vscale_len (m : Int) (v : List Int) : (vscale m v).length = v.length := by
  simp [vscale]

theorem vadd_len : ∀ (a b : List Int), a.length = b.length →
    (vadd a b).length = a.length := by
  intro a
  induction a with
  | nil => intro b _; simp [vadd]
  | cons ha ta ih =>
      intro b hb
      cases b with
      | nil => simp at hb
      | cons hb' tb => simp only [vadd, List.length_cons]; simp at hb; rw [ih tb hb]

theorem comb_len (n : Nat) : ∀ (cs : List LinConstraint) (ms : List Int),
    allLen n cs = true → ms.length = cs.length →
    (combCoeffs n cs ms).length = n := by
  intro cs
  induction cs with
  | nil => intro ms _ hm; cases ms with
           | nil => simpa [combCoeffs] using zeros_len n
           | cons _ _ => simp at hm
  | cons c cs ih =>
      intro ms hall hm
      cases ms with
      | nil => simp at hm
      | cons m ms =>
          simp only [allLen, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          simp only [List.length_cons, Nat.succ_inj] at hm
          have hrest : (combCoeffs n cs ms).length = n := ih ms (by
            simpa [allLen] using hall.2) hm
          have hsc : (vscale m c.coeffs).length = n := by
            rw [vscale_len]; exact hall.1
          simp only [combCoeffs]
          rw [vadd_len _ _ (by rw [hsc, hrest]), hsc]

/-! ### Dot-product linearity -/

theorem linDot_zeros : ∀ (n : Nat) (x : List Int), linDot (zeros n) x = 0 := by
  intro n
  induction n with
  | zero => intro x; simp [zeros, linDot]
  | succ k ih =>
      intro x
      cases x with
      | nil => simp [zeros, linDot]
      | cons xh xt => simp only [zeros, linDot, ih xt]; simp

theorem linDot_vscale : ∀ (m : Int) (v x : List Int),
    linDot (vscale m v) x = m * linDot v x := by
  intro m v
  induction v with
  | nil => intro x; simp [vscale, linDot]
  | cons vh vt ih =>
      intro x
      cases x with
      | nil => simp [vscale, linDot]
      | cons xh xt =>
          simp only [vscale, List.map_cons, linDot]
          rw [show (List.map (fun x => m * x) vt) = vscale m vt from rfl, ih xt,
              Int.mul_add, Int.mul_assoc]

theorem linDot_vadd : ∀ (a b x : List Int), a.length = b.length →
    linDot (vadd a b) x = linDot a x + linDot b x := by
  intro a
  induction a with
  | nil => intro b x hb
           cases b with
           | nil => simp [vadd, linDot]
           | cons _ _ => simp at hb
  | cons ah ta ih =>
      intro b x hb
      cases b with
      | nil => simp at hb
      | cons bh tb =>
          cases x with
          | nil => simp [vadd, linDot]
          | cons xh xt =>
              simp at hb
              simp only [vadd, linDot, ih tb xt hb, Int.add_mul]
              generalize ah * xh = A
              generalize bh * xh = B
              omega

theorem comb_dot (n : Nat) : ∀ (cs : List LinConstraint) (ms : List Int) (x : List Int),
    allLen n cs = true → ms.length = cs.length →
    linDot (combCoeffs n cs ms) x = weightedLhs cs ms x := by
  intro cs
  induction cs with
  | nil => intro ms x _ hm; cases ms with
           | nil => simpa [combCoeffs, weightedLhs] using linDot_zeros n x
           | cons _ _ => simp at hm
  | cons c cs ih =>
      intro ms x hall hm
      cases ms with
      | nil => simp at hm
      | cons m ms =>
          simp only [allLen, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          simp only [List.length_cons, Nat.succ_inj] at hm
          have hsc : (vscale m c.coeffs).length = n := by
            rw [vscale_len]; exact hall.1
          have hrest : (combCoeffs n cs ms).length = n :=
            comb_len n cs ms (by simpa [allLen] using hall.2) hm
          simp only [combCoeffs, weightedLhs]
          rw [linDot_vadd _ _ _ (by rw [hsc, hrest]), linDot_vscale,
              ih ms x (by simpa [allLen] using hall.2) hm]

/-! ### Satisfied constraints plus valid multipliers give LHS ≥ RHS -/

theorem weighted_ge : ∀ (cs : List LinConstraint) (ms : List Int) (x : List Int),
    linSat cs x = true → validMults cs ms = true →
    weightedLhs cs ms x ≥ weightedRhs cs ms := by
  intro cs
  induction cs with
  | nil => intro ms x _ hv
           cases ms with
           | nil => simp [weightedLhs, weightedRhs]
           | cons _ _ => simp [validMults] at hv
  | cons c cs ih =>
      intro ms x hsat hv
      cases ms with
      | nil => simp [validMults] at hv
      | cons m ms =>
          simp only [validMults, Bool.and_eq_true] at hv
          simp only [linSat, List.all_cons, Bool.and_eq_true] at hsat
          have hrest := ih ms x (by simpa [linSat] using hsat.2) hv.2
          have hhead : m * c.rhs ≤ m * linDot c.coeffs x := by
            cases he : c.isEq with
            | true =>
                have h1 : linDot c.coeffs x = c.rhs := by
                  have h := hsat.1; simp [linSat1, he] at h; exact h
                rw [h1]
                exact Int.le_refl _
            | false =>
                have hm : (0 : Int) ≤ m := by
                  have h := hv.1; simp [he] at h; exact h
                have hc : c.rhs ≤ linDot c.coeffs x := by
                  have h := hsat.1; simp [linSat1, he] at h; exact h
                exact Int.mul_le_mul_of_nonneg_left hc hm
          simp only [weightedLhs, weightedRhs]
          generalize m * linDot c.coeffs x = A at hhead ⊢
          generalize m * c.rhs = B at hhead ⊢
          omega

/-- The validator: accept when every row has length `n`, the multipliers
line up and respect the sign rule, the combined coefficient vector is
zero, and the combined right-hand side is strictly positive. -/
def farkasCheck (n : Nat) (cs : List LinConstraint) (ms : List Int) : Bool :=
  allLen n cs && ms.length == cs.length && validMults cs ms
    && combCoeffs n cs ms == zeros n && weightedRhs cs ms > 0

/-- **Soundness.** An accepted certificate proves the system has NO
integer solution. The combined coefficient vector is zero, so the
combined left-hand side is `0` for every `x`, yet the combined
right-hand side is positive and a satisfied system would force
LHS ≥ RHS. -/
theorem farkasSound (n : Nat) (cs : List LinConstraint) (ms : List Int)
    (x : List Int) (hchk : farkasCheck n cs ms = true) : linSat cs x = false := by
  cases hsat' : linSat cs x with
  | false => rfl
  | true =>
      exfalso
      simp only [farkasCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨hall, hlen⟩, hvm⟩, hzero⟩, hpos⟩ := hchk
      have hge := weighted_ge cs ms x hsat' hvm
      have hdot := comb_dot n cs ms x hall hlen
      rw [hzero, linDot_zeros] at hdot
      omega

/-! ## 10. The class-size linear system, built from a graph

Mirrors §8's SMT emission through the SAME readers, so the two describe
one system. Every coefficient row is built to length `N` by `mkRow`, so
`allLen N` holds by construction. -/

def sumAt (pos : Nat) (entries : List (Nat × Int)) : Int :=
  (entries.filterMap (fun (i, v) => if i == pos then some v else none)).foldl (· + ·) 0

def mkRow (n : Nat) (entries : List (Nat × Int)) : List Int :=
  (List.range n).map (fun i => sumAt i entries)

theorem mkRow_len (n : Nat) (entries : List (Nat × Int)) :
    (mkRow n entries).length = n := by simp [mkRow]

def cidx (classes : List WfIri) (c : WfIri) : Nat := indexOfIri classes c

/-- FIBER: `|D| = k·|X|` as `(+1 at D) + (−k at X) = 0`. -/
def lcFiberAll (g : Graph) (n : Nat) (classes ps : List WfIri) :
    List LinConstraint :=
  ps.filterMap (fun p =>
    match fiberOf g p with
    | some (d, x, k) =>
        some { coeffs := mkRow n [(cidx classes d, 1), (cidx classes x, -(k : Int))]
             , rhs := 0, isEq := true }
    | none => none)

/-- BIJECTION: `|D| = |Y|` as `(+1 at D) + (−1 at Y) = 0`. -/
def lcBijAll (g : Graph) (n : Nat) (classes ps : List WfIri) : List LinConstraint :=
  ps.flatMap (fun p =>
    match findInv g p with
    | some ip => classes.filterMap (fun d =>
        match bijOf g p ip d with
        | some (_, y) =>
            some { coeffs := mkRow n [(cidx classes d, 1), (cidx classes y, -1)]
                 , rhs := 0, isEq := true }
        | none => none)
    | none => [])

/-- DISJOINT UNION: `|Z| = |m1| + |m2|`. -/
def lcUnionAll (g : Graph) (n : Nat) (classes : List WfIri) : List LinConstraint :=
  g.filterMap (fun t =>
    match unionPairOf g t with
    | some (z, m1, m2) =>
        some { coeffs := mkRow n [(cidx classes z, 1), (cidx classes m1, -1),
                                  (cidx classes m2, -1)]
             , rhs := 0, isEq := true }
    | none => none)

/-- ONEOF nonemptiness: `|C| ≥ 1`. -/
def lcOneofAll (g : Graph) (n : Nat) (classes cs : List WfIri) : List LinConstraint :=
  cs.filterMap (fun c =>
    if classHasOneOf g c then
      some { coeffs := mkRow n [(cidx classes c, 1)], rhs := 1, isEq := false }
    else none)

/-! ### Finite-pinned classes, and the member rows

An integer class-size variable is model-meaningful only for a class
whose extension is FINITE in every model. The member row below is
therefore gated on a PROVABLE finiteness pin:

* DIRECT — the class carries or is equivalent to an `owl:oneOf`
  enumeration, or has a `subClassOf` / `equivalentClass` bound that is
  an `owl:oneOf` list, or a `unionOf` list ALL of whose members carry
  `owl:oneOf` lists. Its extension is then inside a finite union of
  finite enumerations.
* PROPAGATION — finiteness transfers along exactly the relations the row
  builders read. A bijection row `|A| = |B|` transfers it either way; a
  fiber row `|D| = k·|X|` with `k ≥ 1` either way; a disjoint-union row
  `|Z| = |B| + |C|` both up (parts finite gives Z finite) and down
  (parts are subclasses of Z).

MEMBER row: an asserted `x rdf:type C` denotes SOME element of `C` in
every model, so `|C| ≥ 1` — emitted only for a finite-pinned `C`, so
every row is about an integer that exists. WITHHOLDING a row is always
sound, which is why the propagation search below is fuel-bounded without
a caveat: running out of fuel yields fewer rows, never wrong ones. -/

def listMembersAllOneOf (g : Graph) (ms : List Term) : Bool :=
  ms.all (fun m =>
    match termAsSubject m with
    | some s => (firstObjectOf g s owlOneOf).isSome
    | none => false)

def enumBoundObject (g : Graph) (o : Term) : Bool :=
  match termAsSubject o with
  | none => false
  | some s =>
      (firstObjectOf g s owlOneOf).isSome ||
        (match firstObjectOf g s owlUnionOf with
         | some l => listMembersAllOneOf g (walkList g l g.length)
         | none => false)

def directlyPinned (g : Graph) (c : WfIri) : Bool :=
  classHasOneOf g c || (restrOf g c).any (enumBoundObject g)

/-- The finiteness-transfer edges, read through the SAME functions the
row builders use. -/
def finiteEdges (g : Graph) (classes fprops bprops : List WfIri) :
    List (WfIri × WfIri) :=
  fprops.filterMap (fun p =>
    match fiberOf g p with
    | some (d, x, k) => if k ≥ 1 then some (d, x) else none
    | none => none)
  ++ bprops.flatMap (fun p =>
       match findInv g p with
       | some ip => classes.filterMap (fun d =>
           match bijOf g p ip d with
           | some (_, y) => some (d, y)
           | none => none)
       | none => [])
  ++ g.flatMap (fun t =>
       match unionPairOf g t with
       | some (z, m1, m2) => [(z, m1), (z, m2)]
       | none => [])

def edgeStep (edges : List (WfIri × WfIri)) (c : WfIri) : List WfIri :=
  edges.filterMap (fun (a, b) =>
    if a == c then some b else if b == c then some a else none)

/-- Undirected breadth-first search, fuel-bounded. Running out of fuel
only WITHHOLDS finiteness, which is the sound direction. -/
def finiteBfs (edges : List (WfIri × WfIri)) :
    List WfIri → List WfIri → Nat → List WfIri
  | _, visited, 0 => visited
  | [], visited, _ => visited
  | frontier, visited, fuel + 1 =>
      let fresh := dedupIris ((frontier.flatMap (edgeStep edges)).filter
                                (fun c => !visited.contains c))
      if fresh.isEmpty then visited
      else finiteBfs edges fresh (visited ++ fresh) fuel

def finiteClasses (g : Graph) (classes fprops bprops : List WfIri) : List WfIri :=
  let pinned := classes.filter (directlyPinned g)
  let edges := finiteEdges g classes fprops bprops
  finiteBfs edges pinned pinned (edges.length + 1)

def classHasMember (g : Graph) (c : WfIri) : Bool :=
  g.any (fun t =>
    t.p == rdfType && (match t.o with | .iri x => x == c | _ => false))

def lcMemberAll (g : Graph) (n : Nat) (classes finite cs : List WfIri) :
    List LinConstraint :=
  cs.filterMap (fun c =>
    if finite.contains c && classHasMember g c then
      some { coeffs := mkRow n [(cidx classes c, 1)], rhs := 1, isEq := false }
    else none)

/-- `(N, classes, equality rows, bound rows)`. Equality rows come first
so the searcher and the validator share the ordering. -/
def buildLinSystem (g : Graph) :
    Nat × List WfIri × List LinConstraint × List LinConstraint :=
  let classes := dedupIris (allIris g)
  let n := classes.length
  let fprops := propsTyped g owlFunctionalProperty
  let bprops := bijProps g
  let eqs := lcFiberAll g n classes fprops ++ lcBijAll g n classes bprops
             ++ lcUnionAll g n classes
  let finite := finiteClasses g classes fprops bprops
  let bounds := lcOneofAll g n classes classes
                ++ lcMemberAll g n classes finite classes
  (n, classes, eqs, bounds)

theorem allLen_of_mkRow (n : Nat) (cs : List LinConstraint)
    (h : ∀ c ∈ cs, ∃ e, c.coeffs = mkRow n e) : allLen n cs = true := by
  simp only [allLen, List.all_eq_true]
  intro c hc
  obtain ⟨e, he⟩ := h c hc
  simp [he, mkRow_len]

/-! ## 11. The certificate searcher, and the verdict

The searcher is UNVERIFIED and needs no proof: it only ever proposes a
candidate, and `farkasCheck` decides whether the candidate is accepted.
Integer Gaussian elimination over the equality rows, carrying a
multiplier vector per row, pivoting only on ±1 coefficients so the
arithmetic stays fraction-free. -/

structure ERow where
  coeffs : List Int
  cert   : List Int
deriving Repr, Inhabited

def lidx : List Int → Nat → Int
  | [], _ => 0
  | h :: _, 0 => h
  | _ :: tl, i + 1 => lidx tl i

def vsub : List Int → List Int → List Int
  | ha :: ta, hb :: tb => (ha - hb) :: vsub ta tb
  | a, _ => a

def vneg (a : List Int) : List Int := a.map (-·)

def unitBasis (len i : Nat) : List Int :=
  (List.range len).map (fun p => if p == i then 1 else 0)

def erowsOf (eqs : List LinConstraint) : List ERow :=
  eqs.zipIdx.map (fun (c, i) =>
    { coeffs := c.coeffs, cert := unitBasis eqs.length i })

def elimRow (j : Nat) (piv r : ERow) : ERow :=
  let a := lidx r.coeffs j
  if a == 0 then r
  else { coeffs := vsub r.coeffs (vscale a piv.coeffs)
       , cert := vsub r.cert (vscale a piv.cert) }

/-- The first row with a ±1 coefficient at column `j`, normalised to
`+1`, plus the rest. -/
def findUnitPivot (j : Nat) : List ERow → Option (ERow × List ERow)
  | [] => none
  | r :: tl =>
      let a := lidx r.coeffs j
      if a == 1 then some (r, tl)
      else if a == -1 then some ({ coeffs := vneg r.coeffs, cert := vneg r.cert }, tl)
      else match findUnitPivot j tl with
           | some (p, rest) => some (p, r :: rest)
           | none => none

def elimCols : Nat → Nat → List ERow → List ERow → List ERow
  | 0, _, active, solved => solved ++ active
  | colsLeft + 1, j, active, solved =>
      match findUnitPivot j active with
      | none => elimCols colsLeft (j + 1) active solved
      | some (piv, rest) =>
          elimCols colsLeft (j + 1) (rest.map (elimRow j piv))
            (piv :: solved.map (elimRow j piv))

/-- Is this a single nonzero entry `a·e_v`? -/
def singleNonzero (coeffs : List Int) : Option (Nat × Int) :=
  match coeffs.zipIdx.filter (fun (c, _) => c != 0) with
  | [(a, v)] => some (v, a)
  | _ => none

/-- A lower bound on variable `v` among the bound rows, with the row's
position. -/
def boundOfVar (bounds : List LinConstraint) (v : Nat) : Option (Nat × Int) :=
  bounds.zipIdx.findSome? (fun (b, pos) =>
    match singleNonzero b.coeffs with
    | some (bv, bc) => if bv == v && bc == 1 && b.rhs ≥ 1 then some (pos, b.rhs)
                       else none
    | none => none)

def iabs (a : Int) : Int := if a ≥ 0 then a else -a

def assembleMults (cert : List Int) (a : Int) (numBounds bpos : Nat) : List Int :=
  let t : Int := if a > 0 then -1 else 1
  vscale t cert ++ (List.range numBounds).map (fun i => if i == bpos then iabs a else 0)

def scanRows (bounds : List LinConstraint) (numBounds : Nat) :
    List ERow → Option (List Int)
  | [] => none
  | r :: tl =>
      match singleNonzero r.coeffs with
      | some (v, a) =>
          if a == 0 then scanRows bounds numBounds tl
          else match boundOfVar bounds v with
               | some (bpos, _) => some (assembleMults r.cert a numBounds bpos)
               | none => scanRows bounds numBounds tl
      | none => scanRows bounds numBounds tl

def findLinCert (n : Nat) (eqs bounds : List LinConstraint) : Option (List Int) :=
  scanRows bounds bounds.length (elimCols n 0 (erowsOf eqs) [])

/-- The verdict. Gated by `inCountingFragment` to mirror the oracle's
scope; the validator is what makes it sound, not the gate. -/
def classSizeUnsat (g : Graph) : Bool :=
  if !inCountingFragment g then false
  else
    let (n, _, eqs, bounds) := buildLinSystem g
    match findLinCert n eqs bounds with
    | none => false
    | some ms => farkasCheck n (eqs ++ bounds) ms

/-- **What an accepted verdict means.** The linear system built from `g`
has no integer solution — proved, not delegated.

It does NOT say `g` is inconsistent: that step needs the FIBER /
BIJECTION / DISJOINT-UNION / ONEOF soundness arguments, which are prose
in both trees. The module header says so too, because a reader who took
this theorem for a consistency result would be taking prose for a
proof. -/
theorem classSizeUnsat_sound (g : Graph) (x : List Int)
    (h : classSizeUnsat g = true) :
    linSat ((buildLinSystem g).2.2.1 ++ (buildLinSystem g).2.2.2) x = false := by
  simp only [classSizeUnsat] at h
  split at h
  · simp at h
  · rename_i hfrag
    split at h
    · simp at h
    · rename_i ms hms
      exact farkasSound _ _ ms x h

/-! ## Pinned behaviour -/

section Pins

private def exI (s : String) : WfIri := mkIri ("http://example/" ++ s)

/-- The bound's DATATYPE is not read — `axiomOf` reads the lexical form
and nothing else — so a plain string literal exercises the same path a
typed one would. -/
private def lit (s : String) : Term := .literal (Literal.string s)

/-! A restriction with a min-2 and a max-1 bound on the same property:
the classic single-subject clash the restriction encoder is faithful
for. -/
private def clashGraph : Graph :=
  [ { s := .bnode "r", p := owlOnProperty, o := .iri (exI "p") }
  , { s := .bnode "r", p := owlMinCardinality, o := lit "2" }
  , { s := .bnode "r", p := owlMaxCardinality, o := lit "1" } ]

/-! Two axioms extracted, both on the same subject and role. Without
this the encoder pins below would be about an empty AST. -/
#guard (extractCountingFragment clashGraph).axioms.length == 2

/-! They share ONE count variable, which is what makes `min 2` above
`max 1` unsatisfiable rather than two unrelated bounds. -/
#guard
  let ast := extractCountingFragment clashGraph
  let roles := dedupIris (ast.axioms.map CountAxiom.role)
  let fillers := dedupIris (ast.axioms.filterMap CountAxiom.filler)
  (dedupStrings (ast.axioms.map (varName ast.individuals roles fillers))).length == 1

/-! The graph IS in the fragment, and the encoder emits both bounds. -/
#guard inCountingFragment clashGraph
#guard ((encodeCountingFragment (extractCountingFragment clashGraph)).splitOn
          "(assert ").length == 4

/-! A multi-digit bound is read. The tableau's own reader stops at 9;
dl-910's bounds are 20 / 30 / 601. -/
#guard parseNat "601" == some 601
#guard parseNat "" == none
#guard parseNat "6a1" == none

/-! REJECTED: a datatype facet takes the graph out of the fragment, so
the oracle is never consulted about a data-range inconsistency. -/
#guard !(inCountingFragment
          (clashGraph ++ [{ s := .bnode "d", p := xsdMinInclusive, o := lit "0" }]))

/-! REJECTED: an AUTHORED complement is general boolean structure. -/
#guard !(inCountingFragment
          (clashGraph ++ [{ s := .iri (exI "C"), p := owlComplementOf,
                            o := .iri (exI "D") }]))

/-! ACCEPTED: an engine-generated complement is not authored structure.
Rejecting it would drop legitimate disjoint-union counting problems, so
this pin is the one that stops the reject scan from over-reaching. -/
#guard inCountingFragment
        (clashGraph ++ [{ s := .bnode "__rl_comp__x", p := owlComplementOf,
                          o := .iri (exI "D") }])

/-! A graph with NO counting construct is not a counting problem. -/
#guard !(inCountingFragment
          [{ s := .iri (exI "a"), p := rdfType, o := .iri (exI "C") }])

/-! ### The Farkas validator

`x ≥ 1` together with `x = 0`, as a two-row system. Multipliers `1`
on the equality (negated) and `1` on the bound combine to `0 ≥ 1`. -/

private def rowEq0 : LinConstraint := { coeffs := [1], rhs := 0, isEq := true }
private def rowGe1 : LinConstraint := { coeffs := [1], rhs := 1, isEq := false }

#guard farkasCheck 1 [rowEq0, rowGe1] [-1, 1]

/-! Non-vacuity: the system really is satisfiable without the equality,
so the certificate is doing work. -/
#guard linSat [rowGe1] [1]
#guard !(linSat [rowEq0, rowGe1] [1])
#guard !(linSat [rowEq0, rowGe1] [0])

/-! The validator REFUSES a certificate with a negative multiplier on a
`≥` row — the sign rule is what keeps it sound. -/
#guard !(farkasCheck 1 [rowEq0, rowGe1] [1, -1])

/-! And refuses one whose combined coefficients are not zero. -/
#guard !(farkasCheck 1 [rowEq0, rowGe1] [0, 1])

/-! A satisfiable system has no accepted certificate from the searcher.
`x ≥ 1` alone is satisfiable, so nothing is found. -/
#guard (findLinCert 1 [] [rowGe1]).isNone

/-! The searcher finds the certificate for the unsatisfiable pair, and
the validator accepts it. This is the end-to-end path. -/
#guard match findLinCert 1 [rowEq0] [rowGe1] with
       | some ms => farkasCheck 1 ([rowEq0] ++ [rowGe1]) ms
       | none    => false

/-! The oracle seam: the Phase-0 stub consults nothing. -/
#guard noOracle "(check-sat)" 1000 == Verdict.unknown

end Pins

end L4Factoidal.OWL.CountingOracle
