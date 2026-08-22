/-
L4Factoidal.RDF.IsomorphismTests — build-time tests for graph and
dataset isomorphism (RDF 1.1 Concepts §3.6).

`#guard` evaluates during elaboration, so a wrong answer is a BUILD
ERROR, not a report someone has to read. Every case below is a claim
about the decision procedure that `lake build` re-checks.

No `native_decide`: every `#guard` here reduces in the kernel.
-/
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.RDF.IsoTests

open L4Factoidal.RDF

/-! ## Fixtures -/

private def iA : WfIri := ⟨"http://example.org/a", rfl⟩
private def iB : WfIri := ⟨"http://example.org/b", rfl⟩
private def iC : WfIri := ⟨"http://example.org/c", rfl⟩
private def iP : WfIri := ⟨"http://example.org/p", rfl⟩
private def iQ : WfIri := ⟨"http://example.org/q", rfl⟩

/-- Triple with an IRI subject. -/
private def ti (s : WfIri) (p : WfIri) (o : Term) : Triple := ⟨.iri s, p, o⟩
/-- Triple with a blank-node subject. -/
private def tb (s : BNodeId) (p : WfIri) (o : Term) : Triple := ⟨.bnode s, p, o⟩

private def oi (i : WfIri) : Term := .iri i
private def ob (b : BNodeId) : Term := .bnode b
private def ol (s : String) : Term := .literal (Literal.string s)

/-! ## 1. Blank-node relabelling — the point of the whole exercise -/

/-- `_:x p a . _:x q _:y .` -/
private def relabelled1 : Graph :=
  [ tb "x" iP (oi iA), tb "x" iQ (ob "y") ]
/-- The same graph with the labels `x`,`y` renamed to `b0`,`b1`. -/
private def relabelled2 : Graph :=
  [ tb "b0" iP (oi iA), tb "b0" iQ (ob "b1") ]

#guard Graph.isomorphic? relabelled1 relabelled2 = true
#guard Graph.isomorphic? relabelled2 relabelled1 = true   -- symmetry
#guard Graph.isomorphicOutcome relabelled1 relabelled2 = IsoOutcome.equal

/- The witness really is a mapping of `relabelled1`'s labels onto
`relabelled2`'s (and it is NOT the identity — the search ran). -/
#guard Graph.isomorphismMap? relabelled1 relabelled2
         = some [("y", "b1"), ("x", "b0")]

/-! ## 2. Same triple count, different blank-node structure

A chain `_:a → _:b → _:c` against a fork `_:a → _:b`, `_:a → _:c`.
Both have two triples and three blank nodes and no ground triples, so
every counting heuristic passes them; only the structure separates
them. -/

private def chain : Graph :=
  [ tb "a" iP (ob "b"), tb "b" iP (ob "c") ]
private def fork : Graph :=
  [ tb "a" iP (ob "b"), tb "a" iP (ob "c") ]

#guard chain.length = fork.length
#guard (Graph.bnodes chain).length = (Graph.bnodes fork).length
#guard Graph.isomorphic? chain fork = false
#guard Graph.isomorphic? fork chain = false
#guard Graph.isomorphicOutcome chain fork = IsoOutcome.notEqual

/-! ## 3. Ground graphs compare as SETS -/

private def ground1 : Graph := [ ti iA iP (oi iB), ti iB iQ (oi iA) ]
/-- Same set, written in the other order. -/
private def ground2 : Graph := [ ti iB iQ (oi iA), ti iA iP (oi iB) ]
/-- Same subjects and objects, different predicate. -/
private def ground3 : Graph := [ ti iA iQ (oi iB), ti iB iQ (oi iA) ]

#guard Graph.isomorphic? ground1 ground2 = true    -- order-insensitive
#guard Graph.isomorphic? ground2 ground1 = true
#guard Graph.isomorphic? ground1 ground3 = false
#guard Graph.isomorphic? ground3 ground1 = false

/- Ground triples must match EXACTLY: no bijection can move an IRI. -/
#guard Graph.isomorphic? [ ti iA iP (oi iB) ] [ ti iA iP (oi iC) ] = false

/- Literals likewise. -/
#guard Graph.isomorphic? [ ti iA iP (ol "hello") ] [ ti iA iP (ol "hello") ] = true
#guard Graph.isomorphic? [ ti iA iP (ol "hello") ] [ ti iA iP (ol "goodbye") ] = false

/- Language tags fold case (RDF 1.1 §3.3; the F* module's
`normalize_literal` pass, here inside `Literal.eqb`). -/
#guard Graph.isomorphic?
         [ ti iA iP (.literal (Literal.langString "x" "en-GB")) ]
         [ ti iA iP (.literal (Literal.langString "x" "en-gb")) ] = true

/-! ## 4. Duplicate triples are invisible (a graph is a set) -/

#guard Graph.isomorphic? [ ti iA iP (oi iB), ti iA iP (oi iB) ]
                         [ ti iA iP (oi iB) ] = true
#guard Graph.isomorphic? [ ti iA iP (oi iB) ]
                         [ ti iA iP (oi iB), ti iA iP (oi iB) ] = true
/- With blank nodes too, and relabelled at the same time. -/
#guard Graph.isomorphic? [ tb "x" iP (oi iA), tb "x" iP (oi iA) ]
                         [ tb "n" iP (oi iA) ] = true

/-! ## 5. The adversarial pair: a two-blank-node cycle against two
self-loops.

`_:a p _:b . _:b p _:a .`  versus  `_:a p _:a . _:b p _:b .`

Identical triple counts, identical blank-node counts, identical
predicate multisets, identical in- and out-degrees for every blank
node (one each, both ways). Only the SELF-reference distinguishes
them, which is exactly what the signature key's `S` marker records. If
the pruning over-approximated — treating "an edge to some blank node"
as interchangeable with "an edge to myself" — this pair would come
back `true`. It does not, and the certificate would refuse it even if
the pruning had let it through. -/

private def cycle2 : Graph := [ tb "a" iP (ob "b"), tb "b" iP (ob "a") ]
private def loops2 : Graph := [ tb "a" iP (ob "a"), tb "b" iP (ob "b") ]

#guard cycle2.length = loops2.length
#guard (Graph.bnodes cycle2).length = (Graph.bnodes loops2).length
#guard Graph.isomorphic? cycle2 loops2 = false
#guard Graph.isomorphic? loops2 cycle2 = false

/- The cycle IS isomorphic to a relabelled copy of itself, including
under the swap — so the `false` above is discrimination, not a search
that always fails on this shape. -/
#guard Graph.isomorphic? cycle2 [ tb "u" iP (ob "v"), tb "v" iP (ob "u") ] = true
#guard Graph.isomorphic? loops2 [ tb "u" iP (ob "u"), tb "v" iP (ob "v") ] = true

/-! ## 6. A case the identity mapping cannot solve

The two graphs use the same labels but attached to different ground
neighbours, so the answer needs the non-identity swap `x ↦ y`,
`y ↦ x`. -/

private def swapNeeded1 : Graph := [ tb "x" iP (oi iA), tb "y" iP (oi iB) ]
private def swapNeeded2 : Graph := [ tb "x" iP (oi iB), tb "y" iP (oi iA) ]

#guard Graph.isomorphic? swapNeeded1 swapNeeded2 = true
#guard Graph.isomorphismMap? swapNeeded1 swapNeeded2 = some [("y", "x"), ("x", "y")]

/-! ## 7. RDF 1.2: a blank node inside a triple term

`<a> p <<( _:x q <b> )>> .` — the blank node is nested, so an
isomorphism has to rename it inside the triple term (`Term.bnodes` and
`Term.renameBnodes` both recurse there). -/

private def ttBnode (b : BNodeId) : Graph :=
  [ ti iA iP (.tripleTerm (.bnode b) iQ (oi iB)) ]
private def ttIri : Graph :=
  [ ti iA iP (.tripleTerm (.iri iC) iQ (oi iB)) ]

#guard Term.bnodes (.tripleTerm (.bnode "x") iQ (oi iB)) = ["x"]
#guard Graph.isomorphic? (ttBnode "x") (ttBnode "z") = true
#guard Graph.isomorphic? (ttBnode "x") ttIri = false
#guard Graph.isomorphic? ttIri (ttBnode "x") = false
/- Nested blank nodes in BOTH slots of the triple term. -/
#guard Graph.isomorphic?
         [ ti iA iP (.tripleTerm (.bnode "x") iQ (ob "y")) ]
         [ ti iA iP (.tripleTerm (.bnode "m") iQ (ob "n")) ] = true
/- …and they must not be conflated: one blank node used twice is a
different graph from two distinct ones. -/
#guard Graph.isomorphic?
         [ ti iA iP (.tripleTerm (.bnode "x") iQ (ob "x")) ]
         [ ti iA iP (.tripleTerm (.bnode "m") iQ (ob "n")) ] = false

/-! ## 8. Datasets: named graphs matched by IRI name, blank nodes
scoped to the whole dataset -/

private def dsA : Dataset :=
  { default := [ ti iA iP (ob "s") ],
    named   := [ { name := "http://example.org/g1", graph := [ tb "s" iP (oi iB) ] },
                 { name := "http://example.org/g2", graph := [ ti iC iQ (ob "t") ] } ] }

/-- Same dataset, blank nodes relabelled `s,t ↦ n0,n1`. -/
private def dsB : Dataset :=
  { default := [ ti iA iP (ob "n0") ],
    named   := [ { name := "http://example.org/g1", graph := [ tb "n0" iP (oi iB) ] },
                 { name := "http://example.org/g2", graph := [ ti iC iQ (ob "n1") ] } ] }

/-- The two named graphs SWAPPED between their names. -/
private def dsSwapped : Dataset :=
  { default := [ ti iA iP (ob "n0") ],
    named   := [ { name := "http://example.org/g1", graph := [ ti iC iQ (ob "n1") ] },
                 { name := "http://example.org/g2", graph := [ tb "n0" iP (oi iB) ] } ] }

/-- One named graph missing. -/
private def dsShort : Dataset :=
  { default := [ ti iA iP (ob "n0") ],
    named   := [ { name := "http://example.org/g1", graph := [ tb "n0" iP (oi iB) ] } ] }

#guard Dataset.isomorphic? dsA dsB = true
#guard Dataset.isomorphic? dsB dsA = true
#guard Dataset.isomorphicOutcome dsA dsB = IsoOutcome.equal
#guard Dataset.isomorphic? dsA dsSwapped = false   -- names are matched, not guessed
#guard Dataset.isomorphic? dsA dsShort = false
#guard Dataset.isomorphic? dsShort dsA = false

/-- Dataset-wide scoping: the blank node `_:s` shared between the
default graph and `g1` must map to ONE label on the other side. Break
that link — give `g1` a blank node the default graph never mentions —
and the datasets stop being isomorphic even though each graph, taken
alone, still is. -/
private def dsBroken : Dataset :=
  { default := [ ti iA iP (ob "n0") ],
    named   := [ { name := "http://example.org/g1", graph := [ tb "n9" iP (oi iB) ] },
                 { name := "http://example.org/g2", graph := [ ti iC iQ (ob "n1") ] } ] }

#guard Graph.isomorphic? [ ti iA iP (ob "s") ] [ ti iA iP (ob "n0") ] = true
#guard Graph.isomorphic? [ tb "s" iP (oi iB) ] [ tb "n9" iP (oi iB) ] = true
#guard Dataset.isomorphic? dsA dsBroken = false

/- The empty dataset and the empty graph. -/
#guard Graph.isomorphic? [] [] = true
#guard Dataset.isomorphic? Dataset.empty Dataset.empty = true
#guard Graph.isomorphic? [] [ ti iA iP (oi iB) ] = false
#guard Graph.isomorphic? [ ti iA iP (oi iB) ] [] = false

/-! ## 9. Helper-level guards -/

#guard Graph.bnodes chain = ["a", "b", "c"]
#guard Graph.bnodes ground1 = []
#guard Graph.ground [ ti iA iP (oi iB), tb "x" iP (oi iB) ] = [ ti iA iP (oi iB) ]
#guard noDupLabels ["a", "b", "a"] = false
#guard noDupLabels ["a", "b", "c"] = true
#guard dedupLabels ["a", "b", "a", "c", "b"] = ["a", "c", "b"]
#guard noDupLabels (dedupLabels ["a", "b", "a", "c", "b"]) = true
#guard keyMultisetEq ["p", "q", "p"] ["p", "p", "q"] = true
#guard keyMultisetEq ["p", "q"] ["p", "p"] = false
#guard mapWith [("x", "u"), ("y", "v")] "y" = "v"
#guard mapWith [("x", "u")] "z" = "z"      -- identity off the domain
#guard Graph.setEqB ground1 ground2 = true
#guard Graph.setEqB ground1 ground3 = false

/- The signature key marks a self-reference distinctly from a
reference to another blank node — the property section 5 leans on. -/
#guard Triple.sigKey "a" (tb "a" iP (ob "a"))
         = "S I<http://example.org/p> S"
#guard Triple.sigKey "a" (tb "a" iP (ob "b"))
         = "S I<http://example.org/p> B"

end L4Factoidal.RDF.IsoTests
