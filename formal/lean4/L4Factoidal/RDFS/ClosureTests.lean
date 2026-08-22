/-
L4Factoidal.RDFS.ClosureTests — build-time tests for the rho-df
closure, and the axiom audit for its theorems.

`#guard` runs during elaboration, so a wrong answer is a BUILD ERROR:
`lake build` is the test run. Every fixture below checks BOTH
directions — a triple the rules must derive, and a triple they must
NOT derive. A closure test that only shows derived triples cannot tell
a working engine from one that adds everything, and a test that only
shows absences cannot tell it from one that derives nothing
(`skills/measuring-inference/SKILL.md`).

Fixtures are hand-written Lean values, not W3C manifest files. No
conformance claim attaches to them: the Lean side scores nothing until
it reads the same manifests `bin/w3c-runner` does (the F* tree's iron
rule #6, ladder rung 3 of issue #466).
-/
import L4Factoidal.RDFS.ClosureTheorems

namespace L4Factoidal.RDFS.Tests

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-- Short test IRI: the well-formedness side condition is discharged by
kernel evaluation, so a malformed constant is a build error. -/
private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def A : WfIri := iri! "ex:A"
private def B : WfIri := iri! "ex:B"
private def C : WfIri := iri! "ex:C"
private def D : WfIri := iri! "ex:D"
private def R : WfIri := iri! "ex:R"
private def p : WfIri := iri! "ex:p"
private def q : WfIri := iri! "ex:q"
private def r : WfIri := iri! "ex:r"
private def x : WfIri := iri! "ex:x"
private def y : WfIri := iri! "ex:y"
private def z : WfIri := iri! "ex:z"

/-- `s pred o`, all three IRIs. -/
private def tr (s : WfIri) (pred : WfIri) (o : WfIri) : Triple :=
  ⟨Subject.iri s, pred, Term.iri o⟩

/-! ## Fixture 1 — a three-class chain (rdfs11 + rdfs9)

    ex:A rdfs:subClassOf ex:B .
    ex:B rdfs:subClassOf ex:C .
    ex:x  rdf:type        ex:A .

Derivable: `A subClassOf C` (rdfs11), `x type B` and `x type C`
(rdfs9, the second only after rdfs11 or after the first rdfs9 — so
this fixture also exercises the fixpoint loop, not just one round).
Not derivable: `x type D`, `D subClassOf C`. -/

private def classChain : Graph :=
  [ tr A rdfsSubClassOf B,
    tr B rdfsSubClassOf C,
    tr x rdfType A ]

private def classChainClosed : Graph := closureFix classChain

-- Derived: transitive subClassOf edge (rdfs11).
#guard Graph.mem (tr A rdfsSubClassOf C) classChainClosed
-- Derived: type propagation up one level (rdfs9).
#guard Graph.mem (tr x rdfType B) classChainClosed
-- Derived: type propagation up two levels (needs a second round).
#guard Graph.mem (tr x rdfType C) classChainClosed
-- NOT derived: an unrelated class.
#guard !Graph.mem (tr x rdfType D) classChainClosed
-- NOT derived: subClassOf is not symmetric, and D is not in the chain.
#guard !Graph.mem (tr D rdfsSubClassOf C) classChainClosed
#guard !Graph.mem (tr C rdfsSubClassOf A) classChainClosed
-- The input survives (T1, checked by evaluation as well as proved).
#guard Graph.mem (tr x rdfType A) classChainClosed

/-! ## Fixture 2 — domain and range (rdfs2 + rdfs3)

    ex:p rdfs:domain ex:D .
    ex:p rdfs:range  ex:R .
    ex:y ex:p        ex:z .
    ex:x ex:q        ex:y .

Derivable: `y type D` (rdfs2), `z type R` (rdfs3).
Not derivable: anything about the `ex:q` triple — `ex:q` has no domain
or range declaration, so `x type D` and `y type R` must be absent.
That is the negative test the skill calls for: a type from the range
of an UNRELATED predicate. -/

private def domRange : Graph :=
  [ tr p rdfsDomain D,
    tr p rdfsRange R,
    tr y p z,
    tr x q y ]

private def domRangeClosed : Graph := closureFix domRange

-- Derived: subject typed by the domain (rdfs2).
#guard Graph.mem (tr y rdfType D) domRangeClosed
-- Derived: object typed by the range (rdfs3).
#guard Graph.mem (tr z rdfType R) domRangeClosed
-- NOT derived: ex:q carries no domain declaration.
#guard !Graph.mem (tr x rdfType D) domRangeClosed
-- NOT derived: ex:q carries no range declaration.
#guard !Graph.mem (tr y rdfType R) domRangeClosed
-- NOT derived: domain does not type the object, range does not type
-- the subject.
#guard !Graph.mem (tr z rdfType D) domRangeClosed
#guard !Graph.mem (tr y rdfType R) domRangeClosed

/-! ## Fixture 3 — the property hierarchy (rdfs5 + rdfs7)

    ex:p rdfs:subPropertyOf ex:q .
    ex:q rdfs:subPropertyOf ex:r .
    ex:x ex:p               ex:y .

Derivable: `p subPropertyOf r` (rdfs5), `x q y` (rdfs7), `x r y`
(rdfs7 again, second round).
Not derivable: the converse edges. -/

private def propChain : Graph :=
  [ tr p rdfsSubPropertyOf q,
    tr q rdfsSubPropertyOf r,
    tr x p y ]

private def propChainClosed : Graph := closureFix propChain

-- Derived: transitive subPropertyOf edge (rdfs5).
#guard Graph.mem (tr p rdfsSubPropertyOf r) propChainClosed
-- Derived: the assertion re-stated under the super-property (rdfs7).
#guard Graph.mem (tr x q y) propChainClosed
-- Derived: and under the super-super-property.
#guard Graph.mem (tr x r y) propChainClosed
-- NOT derived: rdfs7 does not run downwards.
#guard !Graph.mem (tr x rdfType q) propChainClosed
#guard !Graph.mem (tr r rdfsSubPropertyOf p) propChainClosed

/-! ## Fixture 4 — a literal object survives rdfs7, and rdfs3 skips it

    ex:p rdfs:subPropertyOf ex:q .
    ex:p rdfs:range         ex:R .
    ex:x ex:p               "hello" .

Derivable: `x q "hello"` (rdfs7 copies the object unexamined).
Not derivable: any `rdf:type ex:R` triple — rdfs3's conclusion needs
the object in a SUBJECT position, and a literal cannot be a subject
(RDF 1.1 Concepts §3.1). This is the `Term.toSubject?` guard, checked
by evaluation. -/

private def litLexical : Triple :=
  ⟨Subject.iri x, p, Term.literal (Literal.string "hello")⟩

private def litGraph : Graph :=
  [ tr p rdfsSubPropertyOf q,
    tr p rdfsRange R,
    litLexical ]

private def litClosed : Graph := closureFix litGraph

-- Derived: rdfs7 carries the literal object across.
#guard Graph.mem (⟨Subject.iri x, q, Term.literal (Literal.string "hello")⟩ : Triple)
  litClosed
-- NOT derived: rdfs3 cannot type a literal.
#guard !Graph.mem (tr R rdfType R) litClosed
#guard litClosed.length = 4

/-! ## Fixture 5 — idempotence

Re-closing a closed graph changes nothing. (Proved in general only as
"saturation is a fixpoint of `step`"; here it is checked by
evaluation on every fixture.) -/

#guard closure (closure classChain 10) 10 == closure classChain 10
#guard closure (closure domRange 10) 10 == closure domRange 10
#guard closure (closure propChain 10) 10 == closure propChain 10
#guard closure (closure litGraph 10) 10 == closure litGraph 10

/-! ## Fixture 6 — the fixpoint really is reached inside the fuel bound

`closureFix` uses `closureFuelBound`; these check that the loop stops
because the length test fired, not because the fuel ran out — i.e.
that `step` is the identity on the result, which is exactly the
hypothesis T4 takes. -/

#guard step classChainClosed == classChainClosed
#guard step domRangeClosed == domRangeClosed
#guard step propChainClosed == propChainClosed
#guard step litClosed == litClosed

/-! ## Empty and rule-free graphs -/

#guard closureFix [] == ([] : Graph)
#guard closureFix [tr x p y] == [tr x p y]

/-! ## Axiom audit

Acceptable base is exactly `propext`, `Classical.choice`, `Quot.sound`
— Lean's standard foundations. No `sorry`, no user axiom, no
`native_decide` anywhere in this port. -/

#print axioms L4Factoidal.RDFS.closure_extensive
#print axioms L4Factoidal.RDFS.closure_sound
#print axioms L4Factoidal.RDFS.complete_of_saturated
#print axioms L4Factoidal.RDFS.closure_complete_of_saturated
#print axioms L4Factoidal.RDFS.closure_mono_of_saturated
#print axioms L4Factoidal.RDFS.closure_saturated_or_underfueled

end L4Factoidal.RDFS.Tests
