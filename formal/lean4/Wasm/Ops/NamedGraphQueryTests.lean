/-
Wasm.Ops.NamedGraphQueryTests — compile-time correctness checks for the
named-graph query path of the store ABI.

Every `#guard` below is evaluated during `lake build`: a wrong answer is a
BUILD FAILURE. They exercise `queryDataset` (the real string-in / string-out
ABI op: N-Quads in, SPARQL, SPARQL-Results-JSON out), which builds the same
`Dataset` and the same `indexedDatasetBackend` that `storeQuery`
(`Wasm/Ops/Store.lean`) builds from decoded IBK4/IBK5 quad blocks, and
evaluates through the same `queryParsedDatasetWith`. So these pin the exact
named-graph answers the store returns, without needing block bytes on disk.

The fixture has an EMPTY default graph and two named graphs, with the SAME
subject (`ex:alice`) present in BOTH — the shape that a full skosall
generation has at scale (every triple in a named graph, none in the default
graph). See `docs/designissues/2026-09-08-named-graph-scale.md`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import Wasm.Ops.Query

namespace L4Wasm.Ops.NamedGraphQueryTests

open L4Wasm.Ops

/-! ## Fixture: empty default graph, `ex:alice` in both `g1` and `g2` -/

/-- Four quads, no default-graph triple:
    * g1: `alice name "Alice"`, `alice knows bob`
    * g2: `alice name "Alice"`, `bob name "Bob"`
    `alice` appears in both g1 and g2 (the two-graph subject case);
    `knows` appears only in g1; `"Bob"` appears only in g2. -/
def nqNamed : String :=
  "<http://example.org/alice> <http://example.org/name> \"Alice\" <http://example.org/g1> .\n" ++
  "<http://example.org/alice> <http://example.org/knows> <http://example.org/bob> <http://example.org/g1> .\n" ++
  "<http://example.org/alice> <http://example.org/name> \"Alice\" <http://example.org/g2> .\n" ++
  "<http://example.org/bob> <http://example.org/name> \"Bob\" <http://example.org/g2> .\n"

private def g1 : String := "http://example.org/g1"
private def g2 : String := "http://example.org/g2"
private def bobLit : String := "\"value\":\"Bob\""
private def countIs (n : String) : String := "\"value\":\"" ++ n ++ "\""

/-! ### 1. `GRAPH <g1> { ?s ?p ?o }` reads only g1's quads -/

-- Two quads in g1.
#guard (queryDataset nqNamed
  "SELECT (COUNT(*) AS ?n) WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }").contains
    (countIs "2")
-- g1 carries `alice knows bob`, so the object `ex:bob` is present …
#guard (queryDataset nqNamed
  "SELECT ?s ?p ?o WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }").contains
    "http://example.org/knows"
-- … but the g2-only literal "Bob" (bob's name, which lives in g2) must not leak in.
#guard !(queryDataset nqNamed
  "SELECT ?s ?p ?o WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }").contains bobLit

/-! ### 2. `GRAPH ?g { ?s ?p ?o }` reads every quad, with its graph bound -/

-- Four quads across both named graphs.
#guard (queryDataset nqNamed
  "SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }").contains (countIs "4")
-- Both graph names are bound to `?g`.
#guard (queryDataset nqNamed
  "SELECT ?g ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }").contains g1
#guard (queryDataset nqNamed
  "SELECT ?g ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }").contains g2
-- A sample row is present: `alice knows bob` in g1.
#guard (queryDataset nqNamed
  "SELECT ?g ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }").contains "http://example.org/knows"

/-! ### 3. `{ ?s ?p ?o }` over the empty default graph is zero rows -/

-- The correct SPARQL answer when data lives only in named graphs and there is
-- no FROM clause: the active graph is the (empty) default graph.
#guard (queryDataset nqNamed "SELECT ?s WHERE { ?s ?p ?o }").contains "\"bindings\":[]"
#guard (queryDataset nqNamed "ASK { ?s ?p ?o }").contains "\"boolean\":false"

/-! ### 4. `FROM NAMED <g1> … GRAPH ?g` sees only g1 -/

-- FROM NAMED restricts the named graphs of the dataset to g1.
#guard (queryDataset nqNamed
  "SELECT (COUNT(*) AS ?n) FROM NAMED <http://example.org/g1> WHERE { GRAPH ?g { ?s ?p ?o } }").contains
    (countIs "2")
#guard (queryDataset nqNamed
  "SELECT ?g ?s FROM NAMED <http://example.org/g1> WHERE { GRAPH ?g { ?s ?p ?o } }").contains g1
#guard !(queryDataset nqNamed
  "SELECT ?g ?s FROM NAMED <http://example.org/g1> WHERE { GRAPH ?g { ?s ?p ?o } }").contains g2

/-! ### 5. A subject in two graphs binds distinctly per graph, no leakage -/

-- `alice name "Alice"` is in g1 AND g2: two rows, one per graph.
#guard (queryDataset nqNamed
  "SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { <http://example.org/alice> <http://example.org/name> ?o } }").contains
    (countIs "2")
#guard (queryDataset nqNamed
  "SELECT ?g WHERE { GRAPH ?g { <http://example.org/alice> <http://example.org/name> ?o } }").contains g1
#guard (queryDataset nqNamed
  "SELECT ?g WHERE { GRAPH ?g { <http://example.org/alice> <http://example.org/name> ?o } }").contains g2
-- `knows` lives only in g1, so a `GRAPH ?g` query over it binds g1 alone.
#guard (queryDataset nqNamed
  "SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s <http://example.org/knows> ?o } }").contains
    (countIs "1")
#guard (queryDataset nqNamed
  "SELECT ?g WHERE { GRAPH ?g { ?s <http://example.org/knows> ?o } }").contains g1
#guard !(queryDataset nqNamed
  "SELECT ?g WHERE { GRAPH ?g { ?s <http://example.org/knows> ?o } }").contains g2

end L4Wasm.Ops.NamedGraphQueryTests
