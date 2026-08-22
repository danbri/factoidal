/-
L4Factoidal.Tests — compile-time executable checks.

Every `#guard` below is evaluated during `lake build`: a wrong answer
is a BUILD FAILURE, so these are unit tests with no separate runner.
The scenario mirrors the running example of the F* tree's hub posts
(people with names/ages) plus RDF 1.2 and literal-equality edge
cases the F* source treats specially.
-/
import L4Factoidal.SPARQL.Invariants
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.RDFS.FullClosureTheorems

namespace L4Factoidal.Tests

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ### Fixture graph -/

/-- Build a well-formed IRI from a literal; the well-formedness check
runs at elaboration time by kernel evaluation (`rfl`) — the Lean
counterpart of the F* `assert_norm` witnesses. -/
def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def exName   : WfIri := iri! "http://example.org/name"
def exAge    : WfIri := iri! "http://example.org/age"
def exClaims : WfIri := iri! "http://example.org/claims"
def exSays   : WfIri := iri! "http://example.org/says"
def exIs     : WfIri := iri! "http://example.org/is"

def alice : Subject := .iri (iri! "http://example.org/alice")
def bob   : Subject := .iri (iri! "http://example.org/bob")

def tAliceName : Triple :=
  { s := alice, p := exName, o := .literal (Literal.string "Alice") }
def tAliceAge : Triple :=
  { s := alice, p := exAge, o := .literal (Literal.string "30") }
def tBobName : Triple :=
  { s := bob, p := exName, o := .literal (Literal.string "Bob") }
def tBobAge : Triple :=
  { s := bob, p := exAge, o := .literal (Literal.string "7") }

def g : Graph := [tAliceName, tAliceAge, tBobName, tBobAge]

/-! ### Graph operations behave as a set -/

#guard (Graph.add tAliceName g).length == 4  -- duplicate not re-added
#guard (Graph.union g g).length == 4         -- union is idempotent here
#guard Graph.mem tBobName g == true

/-! ### Single-pattern BGP: ?s name ?n gives two rows -/

def qNames : Bgp :=
  [{ s := .var "s", p := .iri exName, o := .var "n" }]

#guard (evalBgp qNames g).length == 2
#guard ((evalBgp qNames g).map (·.lookup "n")) ==
  [some (.literal (Literal.string "Alice")),
   some (.literal (Literal.string "Bob"))]

/-! ### A repeated variable in the OBJECT position constrains the match

Added 2026-08-22 after a sabotage that made `tryBindTerm` ignore an
existing binding passed every guard and theorem in the library and
was caught only by the differential harness (`l4diff`, 97 of 500
generated cases). `?x :name ?x` matches no triple of the fixture (no
subject is its own name), and `?s :name ?n . ?s :age ?n` matches none
(nobody's age equals their name). -/

#guard (evalBgp [{ s := .var "x", p := .iri exName, o := .var "x" }] g).length == 0
#guard (evalBgp [{ s := .var "s", p := .iri exName, o := .var "n" },
                 { s := .var "s", p := .iri exAge,  o := .var "n" }] g).length == 0

/-! ### Two-pattern BGP: shared ?s correlates name and age -/

def qNameAge : Bgp :=
  [{ s := .var "s", p := .iri exName, o := .var "n" },
   { s := .var "s", p := .iri exAge,  o := .var "a" }]

#guard (evalBgp qNameAge g).length == 2
#guard ((evalBgp qNameAge g).map
    (fun mu => (mu.lookup "n", mu.lookup "a"))) ==
  [(some (.literal (Literal.string "Alice")), some (.literal (Literal.string "30"))),
   (some (.literal (Literal.string "Bob")),   some (.literal (Literal.string "7")))]

/-! ### Algebra operators through `GraphPattern.eval` -/

def isAdult (mu : Binding) : Bool :=
  match mu.lookup "a" with
  | some (.literal l) => (l.val.lexicalForm.toNat?.getD 0) >= 18
  | _ => false

-- FILTER keeps only Alice's row.
-- (The condition also receives the active graph — for EXISTS — which
-- a plain row predicate ignores.)
#guard ((GraphPattern.filter (fun _ => isAdult) (.bgp qNameAge)).eval g).length == 1

-- UNION doubles the rows.
#guard ((GraphPattern.union (.bgp qNames) (.bgp qNames)).eval g).length == 4

-- MINUS with a compatible overlapping pattern removes everything...
#guard ((GraphPattern.minus (.bgp qNames) (.bgp qNames)).eval g).length == 0
-- ...but MINUS against a domain-disjoint pattern keeps every row
-- (§18.5's disjointness clause; the classic MINUS surprise).
def qAges : Bgp := [{ s := .var "x", p := .iri exAge, o := .var "y" }]
#guard ((GraphPattern.minus (.bgp qNames) (.bgp qAges)).eval g).length == 2

-- LEFT JOIN: every left row survives; Alice extends, Bob's extension
-- fails the adult filter so Bob stays unextended.
#guard (((GraphPattern.leftJoin (.bgp qNames)
    (.bgp [{ s := .var "s", p := .iri exAge, o := .var "a" }])
    (fun _ => isAdult))).eval g |>.map (fun mu => (mu.lookup "n").isSome && (mu.lookup "a").isSome))
  == [true, false]

/-! ### RDF 1.2 triple terms match recursively -/

def gClaims : Graph := [
  { s := alice, p := exClaims,
    o := .tripleTerm bob exAge (.literal (Literal.string "7")) }
]

def qClaim : Bgp :=
  [{ s := .var "who", p := .iri exClaims,
     o := .tripleTerm (.var "subj") (.var "pred") (.var "val") }]

#guard ((evalBgp qClaim gClaims).map
    (fun mu => (mu.lookup "who", mu.lookup "subj"))) ==
  [(some (.iri (iri! "http://example.org/alice")), some (.iri (iri! "http://example.org/bob")))]

/-! ### Literal-equality edge cases the F* source pins -/

-- Language tags compare case-insensitively under engine equality...
def lEN   : Literal := (Literal.langString "chat" "EN").val
def lEnLc : Literal := (Literal.langString "chat" "en").val
#guard lEN.eqb lEnLc == true
-- ...but strict TERM equality (RDF 1.1 Concepts §3.3) distinguishes them.
#guard lEN.termEq lEnLc == false

-- rdf:XMLLiteral: attribute order is c14n-insignificant, so these are
-- the SAME value under engine equality (WebOnt-miscellaneous-202)...
def xml1 : Literal :=
  { lexicalForm := "<a x=\"1\" y=\"2\"/>", datatype := rdfXMLLiteral,
    langTag := none, direction := none }
def xml2 : Literal :=
  { lexicalForm := "<a y=\"2\" x=\"1\"></a>", datatype := rdfXMLLiteral,
    langTag := none, direction := none }
#guard xml1.eqb xml2 == true
-- ...while genuinely different markup stays different.
def xml3 : Literal :=
  { lexicalForm := "<a x=\"9\"/>", datatype := rdfXMLLiteral,
    langTag := none, direction := none }
#guard xml1.eqb xml3 == false

/-! ### Blank-node renaming reaches inside triple terms -/

def gBn : Graph :=
  [{ s := .bnode "b0", p := exSays,
     o := .tripleTerm (.bnode "b0") exIs (.bnode "b1") }]
#guard (gBn.prefixBnodes "d1_") ==
  [{ s := .bnode "d1_b0", p := exSays,
     o := .tripleTerm (.bnode "d1_b0") exIs (.bnode "d1_b1") }]

/-! ### Axiom audit: the headline theorems use no extra axioms

`#print axioms` lists everything a proof depends on; the expected
output for each is at most Lean's own `propext` / `Quot.sound` /
`Classical.choice` foundations — no `sorryAx`, nothing user-declared.
(Inspect the build log to read them.) -/

#print axioms L4Factoidal.SPARQL.evalBgp_mono
#print axioms L4Factoidal.SPARQL.Binding.lookup_merge
#print axioms L4Factoidal.RDF.Literal.termEq_iff_eq
#print axioms L4Factoidal.OWL.RL.indexedClosure_eq
#print axioms L4Factoidal.OWL.RL.detectClashI_closureI
#print axioms L4Factoidal.RDFS.fullComplete_of_saturated
#print axioms L4Factoidal.RDFS.fullClosure_complete_of_saturated
#print axioms L4Factoidal.RDFS.fullClosure_mono_of_saturated
#print axioms L4Factoidal.RDFS.graphMem_fullClosure_of_mem_closure

end L4Factoidal.Tests
