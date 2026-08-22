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
