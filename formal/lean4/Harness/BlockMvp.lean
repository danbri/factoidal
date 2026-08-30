/-
Harness.BlockMvp — native executable for the first block-engine vertical.

This is an in-memory fixture, not a SPARQL protocol endpoint. It parses a
query and routes it through the existing backend SPARQL evaluator. The block
supplies candidate triples through its physical bound scan; it does not add a
second query evaluator.
-/
import L4Factoidal.Storage.BlockWireV0
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.BlockMvp

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.BlockMvp
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def alice : Subject := .iri (iri! "http://example.org/alice")
private def bob : Subject := .iri (iri! "http://example.org/bob")
private def name : WfIri := iri! "http://example.org/name"

private def block : Block :=
  { rows :=
      [ { s := alice, p := name, o := .literal (Literal.langString "Alice" "en") }
      , { s := bob, p := name, o := .literal (Literal.langString "Bob" "en") }
      ] }

/-- The backend fixture consumes the versioned byte representation, not the
    construction-time block value. The empty fallback is unreachable for this
    supported fixture and makes the refusal boundary explicit. -/
private def blockBytes : ByteArray := (encode? block).getD ByteArray.empty

private def blockReadOps : BackendReadOps :=
  { search := fun bound => scanBoundDecoded bound blockBytes
  , estimate := fun bound => (scanBoundDecoded bound blockBytes).length
  , predicatePresent := fun pred => !(scanBoundDecoded { p := some pred } blockBytes).isEmpty }

/-- `BackendReadOps` is the existing backend extension seam. Its `search`
    field is the proved physical block candidate scan. -/
private def blockBackend : GraphBackend := .hdt blockReadOps

private def blockDataset : DatasetBackend :=
  { default := blockBackend, named := [] }

private def defaultQuery : String :=
  "SELECT ?person ?label WHERE { ?person <http://example.org/name> ?label } ORDER BY ?person"

private def renderRows (rows : SolutionSeq) : String :=
  String.intercalate "\n" (rows.map (fun row => toString (repr row)))

private def runSelect (expectedRows : Option Nat) (q : Query) : IO UInt32 := do
  match runSelectQueryBackendDataset emptyEnv q blockDataset with
  | none =>
      IO.eprintln "l4block-mvp failed: query is not a SELECT query"
      return 1
  | some rows =>
      IO.println s!"l4block-mvp sse={q.toSse}"
      IO.println s!"l4block-mvp block-bytes={blockBytes.size} decoded={(decode blockBytes).isSome}"
      IO.println s!"l4block-mvp rows={rows.length}"
      IO.println (renderRows rows)
      match expectedRows with
      | none => return 0
      | some expected =>
          if rows.length == expected then return 0
          else
            IO.eprintln s!"l4block-mvp failed: expected {expected} rows"
            return 1

def main (args : List String) : IO UInt32 := do
  let expectedRows := if args.isEmpty then some 2 else none
  let text := if args.isEmpty then defaultQuery else String.intercalate " " args
  match parseSparql text with
  | .error e =>
      IO.eprintln s!"l4block-mvp parse error at {e.pos}: {e.msg}"
      return 1
  | .ok q => runSelect expectedRows q

end Harness.BlockMvp

def main (args : List String) : IO UInt32 := Harness.BlockMvp.main args
