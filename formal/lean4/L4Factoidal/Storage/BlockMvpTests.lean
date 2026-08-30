/-
L4Factoidal.Storage.BlockMvpTests — executable pins for the first block scan.

The guards run during `lake build`. They cover a bound predicate scan and a
repeated-variable pattern, then the theorem audit records the allowed Lean
foundations of the refinement result.
-/
import L4Factoidal.Storage.BlockMvp

namespace L4Factoidal.Storage.BlockMvpTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.BlockMvp

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def alice : Subject := .iri (iri! "http://example.org/alice")
private def bob : Subject := .iri (iri! "http://example.org/bob")
private def name : WfIri := iri! "http://example.org/name"
private def knows : WfIri := iri! "http://example.org/knows"

private def block : Block :=
  { rows :=
      [ { s := alice, p := name, o := .literal (Literal.langString "Alice" "en") }
      , { s := bob, p := name, o := .literal (Literal.langString "Bob" "en") }
      , { s := alice, p := knows, o := bob.toTerm }
      ] }

private def names : TriplePattern :=
  { s := .var "person", p := .iri name, o := .var "label" }

private def selfKnows : TriplePattern :=
  { s := .var "same", p := .iri knows, o := .var "same" }

#guard (scan names block Binding.empty).length == 2
#guard (scan names block Binding.empty).map (fun mu => mu.lookup "label") ==
  [some (.literal (Literal.langString "Alice" "en")),
   some (.literal (Literal.langString "Bob" "en"))]
#guard (scan selfKnows block Binding.empty).isEmpty
#guard scanBound { p := some name } block ==
  [ { s := alice, p := name, o := .literal (Literal.langString "Alice" "en") }
  , { s := bob, p := name, o := .literal (Literal.langString "Bob" "en") }
  ]

#print axioms scan_eq_evalTP
#print axioms scanBound_eq_tripleMatchesBound

end L4Factoidal.Storage.BlockMvpTests
