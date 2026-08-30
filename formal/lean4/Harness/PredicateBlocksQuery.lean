/- Execute SELECT through a collection of predicate-local indexed blocks. -/
import L4Factoidal.Storage.PredicateBlocks
import L4Factoidal.Syntax.Turtle
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset

namespace Harness.PredicateBlocksQuery

open L4Factoidal.Syntax
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.PredicateBlocks

private def run (input queryText : String) : IO UInt32 := do
  try
    let text ← IO.FS.readFile input
    match parseTurtle text (some ("file://" ++ input)), parseSparql queryText with
    | .error e, _ =>
        IO.eprintln s!"l4block-predicate-query Turtle parse error at {e.pos}: {e.msg}"; return 1
    | _, .error e =>
        IO.eprintln s!"l4block-predicate-query query parse error at {e.pos}: {e.msg}"; return 1
    | .ok graph, .ok query =>
        let store := fromGraph graph
        let dataset : DatasetBackend := { default := .hdt (readOps store), named := [] }
        match runSelectQueryBackendDataset emptyEnv query dataset with
        | none => IO.eprintln "l4block-predicate-query failed: query was not SELECT"; return 1
        | some rows =>
            IO.println s!"l4block-predicate-query input={input} triples={graph.length} predicate-blocks={store.blocks.length}"
            IO.println s!"l4block-predicate-query sse={query.toSse}"
            IO.println s!"l4block-predicate-query rows={rows.length} result={repr rows}"
            return 0
  catch e => IO.eprintln s!"l4block-predicate-query failure: {e}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | input :: "--query" :: queryParts =>
      if queryParts.isEmpty then
        IO.eprintln "l4block-predicate-query requires a query after --query"; return 2
      else run input (String.intercalate " " queryParts)
  | _ =>
      IO.eprintln "usage: l4block-predicate-query INPUT.ttl --query SELECT..."; return 2

end Harness.PredicateBlocksQuery

def main (args : List String) : IO UInt32 := Harness.PredicateBlocksQuery.main args
