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
7b. [`L4Factoidal/Regex/`](L4Factoidal/Regex/) — the XPath/XSD regular-expression engine behind REGEX, REPLACE and the XSD `pattern` facet: Brzozowski derivatives with the F\* correctness lemmas re-proved (`RegexTheorems.lean`, 54 theorems, 183 guards). With it, every sparql11 query-type entry passes.
7c. [`L4Factoidal/SPARQL/Update.lean`](L4Factoidal/SPARQL/Update.lean) + [`UpdateParser.lean`](L4Factoidal/SPARQL/UpdateParser.lean) — SPARQL 1.1 Update (§3 per operation; deletes before inserts; SILENT as an error channel, stricter than the F\*), with the identity / round-trip / CLEAR ALL theorems in [`UpdateTheorems.lean`](L4Factoidal/SPARQL/UpdateTheorems.lean). All 149 UPDATE entries of sparql11 pass.
7d. [`L4Factoidal/SPARQL/Protocol.lean`](L4Factoidal/SPARQL/Protocol.lean), [`GraphStore.lean`](L4Factoidal/SPARQL/GraphStore.lean), [`ServiceDescription.lean`](L4Factoidal/SPARQL/ServiceDescription.lean) — SPARQL 1.1 Protocol request decoding (percent-decoding proved to invert encoding on ASCII), the Graph Store HTTP Protocol state machine, and the service description graph; sparql11 protocol 34 of 34, http-rdf-update 19 of 19, service-description 3 of 3.
8. [`L4Factoidal/SPARQL/Results.lean`](L4Factoidal/SPARQL/Results.lean) and siblings — the four results formats (XML/JSON/CSV/TSV), with the SRJ N-row shape theorem.
9. [`L4Factoidal/RDFS/RdfsCore.lean`](L4Factoidal/RDFS/RdfsCore.lean) — the six-rule core-RDFS fragment as a derivation relation (the spec), [`Closure.lean`](L4Factoidal/RDFS/Closure.lean) (the engine), [`ClosureTheorems.lean`](L4Factoidal/RDFS/ClosureTheorems.lean) (extensive, sound, complete at saturation).
9a. [`L4Factoidal/OWL/RLRules.lean`](L4Factoidal/OWL/RLRules.lean) — OWL 2 RL (Profiles §4.3) as a 55-constructor derivation relation over 50 rule rows + 13 clash rows; [`RLClosure.lean`](L4Factoidal/OWL/RLClosure.lean) the saturating engine; [`RLTheorems.lean`](L4Factoidal/OWL/RLTheorems.lean) 47 of 47 per-row soundness lemmas, clash soundness, completeness at saturation. Two F\* specification errors were found by these proofs (module header).
9b. [`L4Factoidal/RDFS/FullClosure.lean`](L4Factoidal/RDFS/FullClosure.lean), [`RDF/Datatypes.lean`](L4Factoidal/RDF/Datatypes.lean), [`RDF/Entailment.lean`](L4Factoidal/RDF/Entailment.lean) — RDF 1.1 Semantics: the full RDFS rule set (rdfs1–13, rdfD2, the axiomatic triples) over rdfs-core (theorem: every rdfs-core derivation is a full-RDFS derivation), the datatype map, simple entailment as an instance search with a checked certificate, and the simple/D/RDF/RDFS regimes. rdf-mt: 39 of 39; sparql11 entailment: 40 of 40 regime-supported entries (30 OWL/RIF entries named unsupported).
10. [`L4Factoidal/Syntax/`](L4Factoidal/Syntax/) — N-Triples, N-Quads, Turtle, TriG, RDF/XML ([`RdfXml.lean`](L4Factoidal/Syntax/RdfXml.lean): blank-node label spaces disjoint by construction, proved), RFC 3986 IRI resolution; [`Harness/`](Harness/) runs the real W3C manifests (`lake exe l4w3c <manifest.ttl>...`): the seven RDF suites (turtle, n-triples, n-quads, trig, xml, mt, canon) score 1117 pass, 0 fail (out of 1117); sparql11 `manifest-all.ttl` scores 601 pass, 0 fail, 30 unsupported (out of 631; the 30 are OWL-Direct/OWL-RDF-Based/RIF entailment-regime entries) — the F\* runner's denominators throughout.
11. [`L4Factoidal/RDF/Isomorphism.lean`](L4Factoidal/RDF/Isomorphism.lean) and [`RDF/Canonical.lean`](L4Factoidal/RDF/Canonical.lean) — blank-node isomorphism (witness-returning, soundness proved) and RDFC-1.0 (hash-algorithm-agile; 86 of 86 on the W3C suite) over [`Crypto/SHA2.lean`](L4Factoidal/Crypto/SHA2.lean).
11a. [`L4Factoidal/VC/DataIntegrity.lean`](L4Factoidal/VC/DataIntegrity.lean), [`VC/Multibase.lean`](L4Factoidal/VC/Multibase.lean), [`VC/DidKey.lean`](L4Factoidal/VC/DidKey.lean), [`VC/Context.lean`](L4Factoidal/VC/Context.lean) — Verifiable Credentials Data Integrity, cryptosuite `eddsa-rdfc-2022`: RDFC-1.0 transform, SHA-256 hash data, Ed25519 proof creation and verification over canonical forms, datasets, and JSON-LD documents (signing/verifying primitives are parameters); base58btc/multibase with the decode-of-encode theorem the F\* declines to state, and did:key resolution both ways. The Ed25519 primitive is [`Crypto/Ed25519.lean`](L4Factoidal/Crypto/Ed25519.lean) — the tree's ONE `@[extern]` family, HACL\* C linked by Lake (`lakefile.lean` `extern_lib`, `ffi/hacl_ed25519.c`), with its trust statement in the module header. `lake exe l4vc-probe`: RFC 8032 vectors through the extern 22 of 22, did:key 8 of 8 (the F\* runner's 8), the `vc_runner --crypto` roundtrip 8 of 8, and the W3C vc-di-eddsa specification test vectors end to end 20 of 20.
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

No Lean dependencies beyond the pinned toolchain — no mathlib, no
batteries; everything is core Lean 4. The one C dependency is the
vendored HACL\* Ed25519 under `third_party/hacl/` (Apache-2.0), which
`lakefile.lean` compiles with the system `cc` into `libl4hacl.a`; see
`Crypto/Ed25519.lean` for why it is the only extern.

## Relation to the F\* development

The F\* tree remains the production engine (extracted to
OCaml/JS/wasm/C, measured against the W3C suites). This Lean port is
the specification made maximally reviewable, and the platform for the
proof program where tactic-driven structural induction is the right
tool. The two share vocabulary and test scenarios on purpose; where
they must not be confused (engine equality vs term equality; spec
evaluator vs indexed engine), both trees say so at the definition
site.
