/-
L4Factoidal.Testing.GenTests — build-time `#guard`s pinning the
generators' DETERMINISM (same seed → same case) and the invariants on
a few fixed seeds. A wrong answer is a build error.

Concrete-input facts are `#guard`s (compiler evaluation), never
`decide`/`rfl` — pitfall 10 of `skills/factoidal-lean-basics`.
-/
import L4Factoidal.Testing.Props

namespace L4Factoidal.Testing.Tests

open L4Factoidal.Testing L4Factoidal.RDF

/-! ## splitmix64 — the published reference output for seed 0 -/

#guard (Rng.seed 0).next.1 == 0xE220A8397B1DCDAF
#guard (Rng.seed 0).next.2.next.1 == 0x6E789E6AA1B965F4

/-! ## Determinism: same seed, same case; different seed, different case -/

#guard (genCase 1).graph == (genCase 1).graph
#guard (genCase 1).queryText == (genCase 1).queryText
#guard (genCase 7).graphText == (genCase 7).graphText
#guard (genCase 1).queryText != (genCase 2).queryText
#guard (genCase 3).graph != (genCase 4).graph

-- The exact rendering of two seeds — a change in the generator, the
-- query printer or the N-Triples serialiser moves these strings, which
-- is the point.
#guard (genCase 1).queryText ==
  "SELECT DISTINCT ?x ?y WHERE { <http://example.org/s2> <http://example.org/p> ?z . ?x ?x ?y . MINUS { ?x <http://example.org/p> ?y . ?y <http://example.org/r> \"2\"^^<http://www.w3.org/2001/XMLSchema#integer> . } OPTIONAL { ?z <http://example.org/q> ?x . <http://example.org/s3> <http://example.org/p> ?y . } } ORDER BY ?x DESC(?y) DESC(?z) LIMIT 3"
#guard (genCase 2).graphText ==
  "<http://example.org/s1> <http://example.org/p> \"10\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n" ++
  "<http://example.org/s3> <http://example.org/p> \"b\" .\n" ++
  "<http://example.org/s3> <http://example.org/p> \"2.5E1\"^^<http://www.w3.org/2001/XMLSchema#double> .\n" ++
  "<http://example.org/s1> <http://example.org/r> \"b\"@fr .\n" ++
  "<http://example.org/s1> <http://example.org/r> \"2.5E1\"^^<http://www.w3.org/2001/XMLSchema#double> .\n" ++
  "<http://example.org/s1> <http://example.org/p> \"b\" .\n" ++
  "_:b2 <http://example.org/p> <http://example.org/s1> .\n" ++
  "<http://example.org/s1> <http://example.org/q> \"10\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"

/-! ## The generated vocabulary is non-trivial (no vacuous properties) -/

-- Over the first 32 seeds, BGP A has at least one answer on some
-- seed, and the graph has blank nodes on some seed.
#guard (List.range 32).any (fun s => !(genCase s).omegaA.isEmpty)
#guard (List.range 32).any (fun s => !(Graph.bnodes (genCase s).graph).isEmpty)

/-! ## The invariants on fixed seeds -/

#guard allProps.all (fun (_, p) => (p (genCase 1)).isNone)
#guard allProps.all (fun (_, p) => (p (genCase 2)).isNone)
#guard allProps.all (fun (_, p) => (p (genCase 3)).isNone)

end L4Factoidal.Testing.Tests
