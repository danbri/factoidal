# L4Factoidal — the Factoidal RDF/SPARQL core, in Lean 4

A Lean 4 formalisation of the RDF 1.1/1.2 data model and the SPARQL
1.1 algebra core, ported from this repository's F\* development
(`formal/fstar/`). The design goal, in one line: **readable by the
people who wrote the specs**. Every definition cites the W3C
document and section it implements, files read top-to-bottom as
concept walks, and the proofs are ordinary tactic scripts a reviewer
can step through — no SMT solver in the loop.

## Reading order (for RDF/SPARQL reviewers)

1. [`L4Factoidal/RDF/Core.lean`](L4Factoidal/RDF/Core.lean) — what a
   term is: IRIs (with the well-formedness gate as a subtype), blank
   nodes, literals (RDF 1.1 §3.3 + RDF 1.2 base direction), RDF 1.2
   triple terms; and the three literal-equality relations RDF
   actually has (strict term equality, engine equality with
   language-tag folding + XMLLiteral c14n, value equality) — kept
   distinct, with the theorem that strict equality is identity.
2. [`L4Factoidal/RDF/Graph.lean`](L4Factoidal/RDF/Graph.lean) — a
   graph is a set of triples (§3); datasets (§4); blank-node renaming
   (§3.4's document scoping, the thing that makes MERGE ≠ union).
3. [`L4Factoidal/SPARQL/Algebra.lean`](L4Factoidal/SPARQL/Algebra.lean)
   — solution mappings (§18.1.8), compatibility and merge (§18.3),
   triple patterns and BGP matching, and the §18.5 operators (Join,
   LeftJoin, Union, Minus, Filter) in their specification form:
   nested loops over lists, nothing clever.
4. [`L4Factoidal/SPARQL/Invariants.lean`](L4Factoidal/SPARQL/Invariants.lean)
   — what is PROVED: the empty-pattern laws, the observational
   meaning of merge, filter/minus safety, and BGP monotonicity
   (growing the graph never loses answers). `lake build` re-checks
   every proof; the axiom audit in the build log shows only Lean's
   standard foundations.
5. [`L4Factoidal/Tests.lean`](L4Factoidal/Tests.lean) — executable
   `#guard` examples, checked during the build: correlated BGPs, the
   MINUS domain-disjointness surprise, OPTIONAL keeping unmatched
   rows, RDF 1.2 triple-term matching, the language-tag and
   XMLLiteral equality edge cases.

6. [`L4Factoidal/SPARQL/Expr.lean`](L4Factoidal/SPARQL/Expr.lean) — the §17 expression language: effective boolean value (§17.2.2), scaled-decimal numerics, the three-valued logic table, the builtins; every host dependency (NOW, EXISTS, extension functions, SERVICE) is an explicit `EvalEnv` parameter, not an assumption.
7. [`L4Factoidal/SPARQL/Query.lean`](L4Factoidal/SPARQL/Query.lean) + [`PropertyPath.lean`](L4Factoidal/SPARQL/PropertyPath.lean) — the query layer: GRAPH, BIND, VALUES, sub-SELECT, LATERAL, SERVICE, property paths (§18.4), solution modifiers, aggregates (§18.5.1), SELECT/ASK/CONSTRUCT; [`QueryTheorems.lean`](L4Factoidal/SPARQL/QueryTheorems.lean) proves ORDER BY is a permutation and the DISTINCT laws.
7a. [`L4Factoidal/SPARQL/Parser.lean`](L4Factoidal/SPARQL/Parser.lean) + [`Tokenizer.lean`](L4Factoidal/SPARQL/Tokenizer.lean) — the SPARQL 1.1 query grammar (§19) as a fuelled recursive-descent parser with the 17 well-formedness rejections; `lake exe l4sparql-probe` (from the repo root): 403 of 403 manifest-listed sparql11 query files parse/reject as the manifests say.
8. [`L4Factoidal/SPARQL/Results.lean`](L4Factoidal/SPARQL/Results.lean) and siblings — the four results formats (XML/JSON/CSV/TSV), with the SRJ N-row shape theorem.
9. [`L4Factoidal/RDFS/RdfsCore.lean`](L4Factoidal/RDFS/RdfsCore.lean) — the six-rule core-RDFS fragment as a derivation relation (the spec), [`Closure.lean`](L4Factoidal/RDFS/Closure.lean) (the engine), [`ClosureTheorems.lean`](L4Factoidal/RDFS/ClosureTheorems.lean) (extensive, sound, complete at saturation).
10. [`L4Factoidal/Syntax/`](L4Factoidal/Syntax/) — N-Triples, N-Quads, Turtle, TriG, RDF/XML ([`RdfXml.lean`](L4Factoidal/Syntax/RdfXml.lean): blank-node label spaces disjoint by construction, proved), RFC 3986 IRI resolution; [`Harness/`](Harness/) runs the real W3C manifests (`lake exe l4w3c <manifest.ttl>`; `lake exe l4rdfxml-probe` walks the rdf-xml directory).
11. [`L4Factoidal/RDF/Isomorphism.lean`](L4Factoidal/RDF/Isomorphism.lean) and [`RDF/Canonical.lean`](L4Factoidal/RDF/Canonical.lean) — blank-node isomorphism (witness-returning, soundness proved) and RDFC-1.0 (hash-algorithm-agile; 86 of 86 on the W3C suite) over [`Crypto/SHA2.lean`](L4Factoidal/Crypto/SHA2.lean).
12. [`L4Factoidal/XML/`](L4Factoidal/XML/) and [`JSON/`](L4Factoidal/JSON/) — the generic parsers the RDF syntaxes and results formats build on.
12a. [`L4Factoidal/JSONLD/`](L4Factoidal/JSONLD/) — JSON-LD 1.1 context processing, expansion and toRdf (`Context.lean`, `Expand.lean`, `ToRdf.lean`); the remote document loader is an explicit parameter and the no-empty-context-fallback rule is a theorem. `lake exe l4jsonld-probe` (from the repo root): toRdf 467 of 467, matching the F\* runner.
13. [`Wasm/`](Wasm/) — the C ABI and build for the WebAssembly export; skill `lean4-wasm-export` has the pipeline.

`PORT_NOTES.md` records the F\* correspondence, the translation
decisions, and the assumption report against the originals.

## Building

```
elan default stable          # or let lean-toolchain pin it
cd formal/lean4
lake build                   # library + proofs + #guard tests
```

No dependencies beyond the pinned Lean toolchain — no mathlib, no
batteries; everything is core Lean 4.

## Relation to the F\* development

The F\* tree remains the production engine (extracted to
OCaml/JS/wasm/C, measured against the W3C suites). This Lean port is
the specification made maximally reviewable, and the platform for the
proof program where tactic-driven structural induction is the right
tool. The two share vocabulary and test scenarios on purpose; where
they must not be confused (engine equality vs term equality; spec
evaluator vs indexed engine), both trees say so at the definition
site.
