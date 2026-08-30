/- Build-time pins for the first block byte boundary. -/
import L4Factoidal.Storage.BlockWireV0

namespace L4Factoidal.Storage.BlockWireV0Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.BlockMvp
open L4Factoidal.Storage.BlockWireV0

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def alice : Subject := .iri (iri! "http://example.org/alice")
private def name : WfIri := iri! "http://example.org/name"

private def block : Block :=
  { rows := [{ s := alice, p := name, o := .literal (Literal.langString "Alice" "en") }] }

private def names : TriplePattern :=
  { s := .var "person", p := .iri name, o := .var "label" }

private def bytes : ByteArray := (encode? block).getD ByteArray.empty

#guard blockSupported block
#guard decode bytes == some block
#guard (scanDecoded names bytes Binding.empty).length == 1
#guard (scanBoundDecoded { p := some name } bytes).length == 1
#guard decode ByteArray.empty == none

#print axioms scanDecoded_eq_evalTP
#print axioms scanBoundDecoded_eq_tripleMatchesBound

end L4Factoidal.Storage.BlockWireV0Tests
