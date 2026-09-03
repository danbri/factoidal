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
9a. [`L4Factoidal/OWL/RLRules.lean`](L4Factoidal/OWL/RLRules.lean) — OWL 2 RL (Profiles §4.3) as a 55-constructor derivation relation over 50 rule rows + 13 clash rows; [`RLClosure.lean`](L4Factoidal/OWL/RLClosure.lean) the saturating engine; [`RLTheorems.lean`](L4Factoidal/OWL/RLTheorems.lean) 47 of 47 per-row soundness lemmas, clash soundness, completeness at saturation. Two F\* specification errors were found by these proofs (module header). [`RLClosureIndexed.lean`](L4Factoidal/OWL/RLClosureIndexed.lean) is the hash-indexed engine with the theorem `indexedClosure g fuel = closure g fuel` (list equality, every fuel), so every theorem about the spec engine transfers; it runs the 931-case W3C OWL corpus in ~11 s with no cap hits (`lake exe l4owl-probe` from `formal/lean4`: 1060 pass, 354 fail, 41 unsupported out of 1457 units — the fails are named scoped-out rule rows and tableau-only DL cases).
9b. [`L4Factoidal/RDFS/FullClosure.lean`](L4Factoidal/RDFS/FullClosure.lean), [`RDF/Datatypes.lean`](L4Factoidal/RDF/Datatypes.lean), [`RDF/Entailment.lean`](L4Factoidal/RDF/Entailment.lean) — RDF 1.1 Semantics: the full RDFS rule set (rdfs1–13, rdfD2, the axiomatic triples) over rdfs-core (theorem: every rdfs-core derivation is a full-RDFS derivation), the datatype map, simple entailment as an instance search with a checked certificate, and the simple/D/RDF/RDFS regimes. rdf-mt: 39 of 39; sparql11 entailment: 40 of 40 regime-supported entries (30 OWL/RIF entries named unsupported).
9c. [`L4Factoidal/SHACL/Shapes.lean`](L4Factoidal/SHACL/Shapes.lean), [`SHACL/Validation.lean`](L4Factoidal/SHACL/Validation.lean), [`SHACL/Report.lean`](L4Factoidal/SHACL/Report.lean) — SHACL Core: shapes-graph decoding into a typed `Shape` (targets, paths, the Core components), `Spec.Conforms` (§3.4 as a relation) beside `validate` (the engine), the report as a graph; [`ShaclTheorems.lean`](L4Factoidal/SHACL/ShaclTheorems.lean) proves `validate` conforms iff `Spec.GraphConforms`, component by component. Then SHACL Part 2 in [`SHACL/Sparql.lean`](L4Factoidal/SHACL/Sparql.lean) — `sh:sparql` constraints (§5.1), the SPARQL-based constraint components (§6), pre-binding of `$this` / `$value` / `$currentShape` / `$shapesGraph` / `$PATH` (§5.3) by substitution into the parsed query AST, and the §5.3.2 restrictions that make a query ill-formed (the suite's `sht:Failure`); [`SparqlTheorems.lean`](L4Factoidal/SHACL/SparqlTheorems.lean) relates each judgment to its specification and states what it does not cover. `lake exe l4shacl` on the W3C data-shapes suite: core 98 pass, 0 fail (out of 98); sparql 22 pass, 0 fail (out of 22).
10. [`L4Factoidal/Syntax/`](L4Factoidal/Syntax/) — N-Triples, N-Quads, Turtle, TriG, RDF/XML ([`RdfXml.lean`](L4Factoidal/Syntax/RdfXml.lean): blank-node label spaces disjoint by construction, proved), RFC 3986 IRI resolution, and the RDF 1.2 additions (triple terms `<<( s p o )>>`, reifiers `<< >>` / `~`, annotation blocks `{| |}`, the `VERSION` directive, base direction `@en--ltr`, canonical N-Triples/N-Quads, and RDF/XML's `rdf:version` / `its:dir` / `rdf:parseType="Triple"` / `rdf:annotation`); the parsing layers and their proofs are recorded in [`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](../../docs/designissues/2026-09-03-rdf-parsing-strategy.md); [`Harness/`](Harness/) runs the real W3C manifests (`lake exe l4w3c <manifest.ttl>...`): the seven RDF 1.1 suites (turtle, n-triples, n-quads, trig, xml, mt, canon) score 1117 pass, 0 fail (out of 1117); the RDF 1.2 suites (n-triples/syntax, n-quads/syntax, turtle/syntax, turtle/eval, trig/syntax, trig/eval, xml/eval, n-triples/c14n, n-quads/c14n) score 324 pass, 0 fail (out of 324), matching the F* runner suite by suite — the tenth rdf12 manifest, rdf-semantics, loads since 2026-08-25 through the lenient-with-report manifest parse (its upstream undeclared `test:` prefix is recovered with a printed `MANIFEST-RECOVERY` warning — [issue 602](https://github.com/danbri/factoidal/issues/602)) and scores 19 pass, 11 fail, 0 skip, 17 unsupported (out of 47) on first reading (the 17 are xsd:float/xsd:double/rdf:JSON value models this tree does not carry; 2 of the 11 fails are the upstream suite's own tension between `malformed-literal` `mf:result false` and the two NegativeEntailmentTests sharing its D-inconsistent premise); sparql11 `manifest-all.ttl` scores 631 pass, 0 fail (out of 631; re-measured 2026-08-25) — the F* runner's denominators throughout.
11. [`L4Factoidal/RDF/Isomorphism.lean`](L4Factoidal/RDF/Isomorphism.lean) and [`RDF/Canonical.lean`](L4Factoidal/RDF/Canonical.lean) — blank-node isomorphism (witness-returning, soundness proved) and RDFC-1.0 (hash-algorithm-agile; 86 of 86 on the W3C suite) over [`Crypto/SHA2.lean`](L4Factoidal/Crypto/SHA2.lean).
11a. [`L4Factoidal/VC/DataIntegrity.lean`](L4Factoidal/VC/DataIntegrity.lean), [`VC/Multibase.lean`](L4Factoidal/VC/Multibase.lean), [`VC/DidKey.lean`](L4Factoidal/VC/DidKey.lean), [`VC/Context.lean`](L4Factoidal/VC/Context.lean) — Verifiable Credentials Data Integrity, cryptosuite `eddsa-rdfc-2022`: RDFC-1.0 transform, SHA-256 hash data, Ed25519 proof creation and verification over canonical forms, datasets, and JSON-LD documents (signing/verifying primitives are parameters); base58btc/multibase with the decode-of-encode theorem the F\* declines to state, and did:key resolution both ways. The Ed25519 primitive is [`Crypto/Ed25519.lean`](L4Factoidal/Crypto/Ed25519.lean) — the tree's ONE `@[extern]` family, HACL\* C linked by Lake (`lakefile.lean` `extern_lib`, `ffi/hacl_ed25519.c`), with its trust statement in the module header. `lake exe l4vc-probe`: RFC 8032 vectors through the extern 22 of 22, did:key 8 of 8 (the F\* runner's 8), the `vc_runner --crypto` roundtrip 8 of 8, and the W3C vc-di-eddsa specification test vectors end to end 20 of 20.
12. [`L4Factoidal/XML/`](L4Factoidal/XML/) and [`JSON/`](L4Factoidal/JSON/) — the generic parsers the RDF syntaxes and results formats build on.
12a. [`L4Factoidal/JSONLD/`](L4Factoidal/JSONLD/) — JSON-LD 1.1, now the whole API surface the W3C json-ld-api suite tests. Context processing, expansion and toRdf ([`Context.lean`](L4Factoidal/JSONLD/Context.lean), [`Expand.lean`](L4Factoidal/JSONLD/Expand.lean), [`ToRdf.lean`](L4Factoidal/JSONLD/ToRdf.lean)); then Compaction §6 with Inverse Context Creation, IRI Compaction, Term Selection and Value Compaction ([`Compact.lean`](L4Factoidal/JSONLD/Compact.lean)), Flattening §7 with Node Map Generation and the §7.2 blank-node issuer ([`Flatten.lean`](L4Factoidal/JSONLD/Flatten.lean)), Serialize RDF as JSON-LD §8.5-8.7 including `useNativeTypes` / `useRdfType` / both `rdfDirection` modes and the RDF-collection-to-`@list` conversion ([`FromRdf.lean`](L4Factoidal/JSONLD/FromRdf.lean)), and the HTML Content Algorithms' script extraction ([`Html.lean`](L4Factoidal/JSONLD/Html.lean)). The remote document loader is an explicit parameter throughout and the no-empty-context-fallback rule is a theorem; framing stays out of scope (a separate specification with its own suite). Two probes, both run from the REPO ROOT: `lake exe l4jsonld-probe` scores toRdf 467 pass, 0 fail, 0 skip (out of 467), and `lake exe l4jsonld-api` scores expand 385 pass, 0 fail (out of 385), compact 245 pass, 0 fail, 1 local-override (out of 246), flatten 58 pass, 0 fail (out of 58), fromRdf 53 pass, 0 fail, 1 local-override (out of 54), html 50 pass, 0 fail (out of 50) — TOTAL 791 pass, 0 fail, 2 local-override (out of 793), matching the F\* runners manifest for manifest, including which two fixtures are local-overrides.
13. [`Wasm/`](Wasm/) — the C ABI and build for the WebAssembly export; skill `lean4-wasm-export` has the pipeline.
13a. [`L4Factoidal/Testing/Gen.lean`](L4Factoidal/Testing/Gen.lean) + [`Props.lean`](L4Factoidal/Testing/Props.lean) and [`Harness/Differential.lean`](Harness/Differential.lean) / [`Harness/PropProbe.lean`](Harness/PropProbe.lean) — tests that exercise the implementation beyond the W3C files: pure seeded generators (graphs, BGPs, a small query grammar) with 18 invariants checked by `lake exe l4prop` (500 cases, 0 failures), and the differential harness `l4diff` that runs the same (data, query) pairs through `bin/<platform>/factoidal` and the Lean evaluator (sparql11 query tests: 215 agree, 15 disagree, 6 fstar-error, 0 lean-error, 395 skipped, out of 631; 500 generated: 497 agree, 3 disagree) — every disagreement attributed in `docs/designissues/2026-08-22-lean4-w3c-harness.md`.

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
