import L4Factoidal.Storage.IndexedBlock

namespace L4Factoidal.Storage.IndexedBlockTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlock

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def pKnows : WfIri := ⟨"http://example.org/knows", by simp [isIri]⟩
private def graph : Graph :=
  [{ s := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
   , p := pName, o := .iri ⟨"http://example.org/a", by simp [isIri]⟩ },
   { s := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
   , p := pKnows, o := .iri ⟨"http://example.org/a", by simp [isIri]⟩ },
   { s := .iri ⟨"http://example.org/carol", by simp [isIri]⟩
   , p := pName, o := .iri ⟨"http://example.org/c", by simp [isIri]⟩ }]
private def block := fromGraph graph

#guard block.rows.size == 3
#guard block.dict.size == 7
#guard (candidateRows { p := some pName } block).length == 2
#guard (scanBound { p := some pName } block).length == 2
#guard scanBound { p := some pName } block == tripleMatchesBound { p := some pName } graph
#guard scanBound {} block == tripleMatchesBound {} graph
#guard (predicateSegment 1 block).map (fun entry => entry.position) == [0, 2]
#guard (predicateSegment 1 block).map (fun entry => entry.row) ==
  candidateRows { p := some pName } block

end L4Factoidal.Storage.IndexedBlockTests
