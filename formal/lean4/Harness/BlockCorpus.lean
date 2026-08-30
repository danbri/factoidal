/-
Harness.BlockCorpus — real-corpus probe for the indexed block format.

This executable reads Turtle with the existing Lean parser, builds a shared
TermId dictionary and predicate partitions, then runs parsed SPARQL through the
existing backend evaluator. It is a corpus probe, not a storage benchmark or a
claim that the in-memory representation is the final persistent format.
-/
import L4Factoidal.Storage.IndexedBlock
import L4Factoidal.Syntax.Turtle
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.BlockCorpus

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Syntax
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset

private def countPredicateQuery (predicate : String) : String :=
  "SELECT (COUNT(*) AS ?count) WHERE { ?subject <" ++ predicate ++ "> ?object }"

private def runGraph (path queryText : String) (graph : Graph) : IO UInt32 := do
  let block := fromGraph graph
  let dataset : DatasetBackend := { default := .hdt (readOps block), named := [] }
  match parseSparql queryText with
  | .error e =>
      IO.eprintln s!"l4block-corpus query parse error at {e.pos}: {e.msg}"
      return 1
  | .ok q =>
      match runSelectQueryBackendDataset emptyEnv q dataset with
      | none =>
          IO.eprintln "l4block-corpus failed: query was not evaluated as SELECT"
          return 1
      | some rows =>
          IO.println s!"l4block-corpus path={path} triples={graph.length} terms={block.dict.size} id-rows={block.rows.size} predicate-partitions={block.byPredicate.toList.length}"
          IO.println s!"l4block-corpus sse={q.toSse}"
          IO.println s!"l4block-corpus rows={rows.length} result={toString (repr rows)}"
          return 0

private def defaultQuery : String :=
  countPredicateQuery "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: l4block-corpus PATH.ttl [PREDICATE-IRI] | PATH.ttl --query SELECT..."
      return 2
  | path :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-corpus requires a query after --query"
        return 2
      else try
        let text ← IO.FS.readFile path
        match parseTurtle text (some ("file://" ++ path)) with
        | .error e =>
            IO.eprintln s!"l4block-corpus Turtle parse error at {e.pos}: {e.msg}"
            return 1
        | .ok graph => runGraph path (String.intercalate " " queryParts) graph
      catch e =>
        IO.eprintln s!"l4block-corpus read failure: {e}"
        return 1
  | path :: predicate :: [] =>
      try
        let text ← IO.FS.readFile path
        match parseTurtle text (some ("file://" ++ path)) with
        | .error e =>
            IO.eprintln s!"l4block-corpus Turtle parse error at {e.pos}: {e.msg}"
            return 1
        | .ok graph => runGraph path (countPredicateQuery predicate) graph
      catch e =>
        IO.eprintln s!"l4block-corpus read failure: {e}"
        return 1
  | [path] =>
      try
        let text ← IO.FS.readFile path
        match parseTurtle text (some ("file://" ++ path)) with
        | .error e =>
            IO.eprintln s!"l4block-corpus Turtle parse error at {e.pos}: {e.msg}"
            return 1
        | .ok graph => runGraph path defaultQuery graph
      catch e =>
        IO.eprintln s!"l4block-corpus read failure: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: l4block-corpus PATH.ttl [PREDICATE-IRI] | PATH.ttl --query SELECT..."
      return 2

end Harness.BlockCorpus

def main (args : List String) : IO UInt32 := Harness.BlockCorpus.main args
