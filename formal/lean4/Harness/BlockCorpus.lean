/-
Harness.BlockCorpus — real-corpus probe for the BLK0 transition format.

This executable reads Turtle with the existing Lean parser, encodes the
resulting direct-term graph as BLK0 bytes, and runs a parsed COUNT query through
the decoded-byte backend. It is a corpus probe, not a storage benchmark or a
claim that BLK0 is the final persistent format.
-/
import L4Factoidal.Storage.BlockWireV0
import L4Factoidal.Syntax.Turtle
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.BlockCorpus

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Syntax
open L4Factoidal.Storage.BlockMvp
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset

private def countPredicateQuery (predicate : String) : String :=
  "SELECT (COUNT(*) AS ?count) WHERE { ?subject <" ++ predicate ++ "> ?object }"

private def readOps (bytes : ByteArray) : BackendReadOps :=
  { search := fun bound => scanBoundDecoded bound bytes
  , estimate := fun bound => (scanBoundDecoded bound bytes).length
  , predicatePresent := fun pred => !(scanBoundDecoded { p := some pred } bytes).isEmpty }

private def runGraph (path predicate : String) (graph : Graph) : IO UInt32 := do
  let block : Block := { rows := graph }
  match encode? block with
  | none =>
      IO.eprintln "l4block-corpus refused: BLK0 does not support one or more RDF terms"
      return 1
  | some bytes =>
      let dataset : DatasetBackend := { default := .hdt (readOps bytes), named := [] }
      match parseSparql (countPredicateQuery predicate) with
      | .error e =>
          IO.eprintln s!"l4block-corpus internal query parse error at {e.pos}: {e.msg}"
          return 1
      | .ok q =>
          match runSelectQueryBackendDataset emptyEnv q dataset with
          | none =>
              IO.eprintln "l4block-corpus failed: COUNT query was not evaluated"
              return 1
          | some rows =>
              IO.println s!"l4block-corpus path={path} triples={graph.length} bytes={bytes.size} decoded={(decode bytes).isSome}"
              IO.println s!"l4block-corpus sse={q.toSse}"
              IO.println s!"l4block-corpus result={toString (repr rows)}"
              return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: l4block-corpus PATH.ttl [PREDICATE-IRI]"
      return 2
  | path :: rest =>
      let predicate := rest.head?.getD "http://example.com/demo/capital"
      try
        let text ← IO.FS.readFile path
        match parseTurtle text (some ("file://" ++ path)) with
        | .error e =>
            IO.eprintln s!"l4block-corpus Turtle parse error at {e.pos}: {e.msg}"
            return 1
        | .ok graph => runGraph path predicate graph
      catch e =>
        IO.eprintln s!"l4block-corpus read failure: {e}"
        return 1

end Harness.BlockCorpus

def main (args : List String) : IO UInt32 := Harness.BlockCorpus.main args
