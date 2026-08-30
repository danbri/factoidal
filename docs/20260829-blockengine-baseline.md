# Block engine repository baseline

Date: 2026-08-29

Commit: `73209342c23212dca31d7f9ef7dbc37cbbdab814`

Branch: `claude/main`, equal to `origin/claude/main` at the time of this audit

Workstream: [Lean 4 port issue](https://github.com/danbri/factoidal/issues/466)

## Owner direction

The owner said on 2026-08-29:

> "The Lean port is only a week old, but improved quickly enough that I am
> inclined to make the switch. It hasn't yet been applied to the full scope of
> Factoidal but that is my intent."

Lean 4 is the intended target implementation for the full Factoidal scope.
This decision does not claim current parity with the older F* product path.
Keep F* as executable lineage, a source of algorithms, and a differential
oracle until each corresponding Lean path has its own gates.

## Result

The refreshed Lean tree is a viable starting point for the block engine. No
fundamental Lean language or toolchain barrier was found.

The remaining work has three classes:

1. Landed implementation to generalize: indexed SPARQL evaluation, Cottas
   on-disk algorithms, HDT reading, backend capabilities, and query-shape fast
   paths.
2. Migration and integration volume: the older F* path still has wider product
   wiring and some broader refinement and conformance history.
3. Structural work: RDF-version-specific term identity, one cross-position ID
   domain, a backend-neutral block denotation, and laws that connect real I/O
   adapters to the pure Lean model.

The third class needs design and proofs. It is bounded and visible. The first
two classes contain most of the work.

## Checkout and build evidence

- `HEAD` and `origin/claude/main` were both `73209342c232`.
- The full command `/Users/danbri/.elan/bin/lake build` passed in
  `formal/lean4/`.
- Result: `Build completed successfully (719 jobs).`
- Lean: 4.33.1.
- Lake: 5.0.0.
- The local Lean build has native C output and the repository has a WASM route.
- The installed Lean toolchain was built without LLVM support. LLVM remains an
  optional later toolchain experiment.
- `stash@{0}` is `pre-73209342 tracked changes`. It remains intact. Do not pop
  it as one unit: it contains generated OCaml artifacts and two stale document
  edits.
- Existing untracked owner files were preserved.

## Corrected Lean map

The library and harness contain 452 Lean files in this audit. Selected areas:

| Area | Files | Current content |
|---|---:|---|
| RDF | 35 | term model, graphs, datasets, canonicalization, isomorphism, loaders |
| SPARQL | 59 | algebra, expressions, query forms, indexed evaluation, backend planning, refinement |
| Cottas | 33 | readers, writers, dictionaries, on-disk search, planning, pruning, indexes, counts |
| HDT | 5 | container, theorems, dictionary, triples, static store |
| Storage | 4 | storage support including delta log |
| RDFS | 18 | vocabulary, closure, derivations, refinement work |
| OWL | 35 | syntax, RL and wider OWL functions and proofs |
| SHACL | 10 | shapes, evaluation, SPARQL bridge, theorems |
| Syntax | 27 | RDF and XML-related syntax implementations |
| Testing | 4 | generated and enumerated test support |

### SPARQL implementation and proof base

`SPARQL/Algebra.lean` keeps a simple list evaluator and also contains faster
hash and indexed BGP operations.

`SPARQL/IndexedEvalRefinement.lean` proves exact list equality:

```text
hashJoin o1 o2 = join o1 o2
evalBgpIdx b g = evalBgp b g
```

This is stronger than result-set agreement. It preserves rows, duplicates,
and list order.

`SPARQL/StoreBackend.lean`, `StorePlan.lean`, `StoreFastPath.lean`, and
`StoreDataset.lean` provide:

- one capability dispatch for list, indexed, HDT, Cottas, union, and virtual
  RML backends;
- storage-aware triple-pattern ordering and cardinality estimates;
- conservative COUNT, LIMIT, and grouped-count paths;
- dataset and named-graph handling.

The tree therefore has a physical planning seam. It does not yet have the
general Block model, Physical Plan IR, or PushIR proposed by the design docs.
Part Three now specifies the proposed typed symbolic, dataflow, and portable
execution layers: [`2026-08-blockengine_part3.md`](2026-08-blockengine_part3.md).

`SPARQL/AlgebraRefinement.lean` is a partial proof port. It covers UNION,
FILTER, MINUS at its stated layers, and the compatibility bridge. JOIN,
LEFTJOIN, EXTEND, PROJECT, DISTINCT, and the full BGP-to-declarative-spec
vertical remain outside that module's current proof coverage.

### Cottas and HDT

The Lean Cottas port is substantial and total. It includes:

- base writer and byte-format code;
- per-role dictionaries and reverse maps;
- on-disk search, filter, walk, limit, count, and exact-count paths;
- row-group planning and selective column decode;
- presence and compound-presence bitmaps;
- offset and subject-offset indexes;
- access-path and pruning theorems.

The Lean HDT port has a static store. It reads the container, dictionary, and
triples data and then runs pure search over the loaded value.

These modules are the first source for the new work. F* remains useful for
comparison and for functionality that has not moved.

## Why the current Cottas store is not yet the common Block layer

The current Cottas design uses separate subject, predicate, object, and graph
dictionaries. A term can therefore have different numeric IDs in different
quad positions. Its row-group and file contracts are also specific to the
Cottas/Parquet representation.

The proposed common layer needs:

- one RDF-version-specific term identity contract;
- a cross-position `TermId` relation;
- a tagged default or named `GraphId`;
- one backend-neutral immutable block denotation;
- laws shared by Cottas, PostgreSQL, and TiKV realizations.

This is a generalization and representation change. It can reuse Cottas scan,
pruning, access-path, and fallback proofs. There are no external users whose
stored IDs require compatibility.

## Structural questions to settle

### RDF term identity

The current tree has two relevant literal relations:

- `Literal.eqb` folds language-tag case and canonicalizes XMLLiteral lexical
  forms;
- `Literal.termEq` compares every stored field.

[RDF 1.2 Concepts](https://www.w3.org/TR/rdf12-concepts/#section-Graph-Literal)
requires case-insensitive language-tag comparison and exact lexical-form
comparison for literal term equality. RDF 1.1 treated tag case differently.
Thus neither current relation is the complete RDF 1.2 physical identity
contract: `Literal.eqb` is too coarse for XMLLiteral, while structural equality
is too fine for tag case.

Define a version-explicit RDF 1.2 term identity decision and prove it sound and
complete before assigning stable `TermId` values. Keep SPARQL value equality,
join keys, and collation as separate relations.

### Backend laws and I/O

`GraphBackend` and `StoreCaps` express the correct seam. Some lawfulness
results require hypotheses such as estimate correctness, predicate-presence
soundness, token-table agreement, or pruning soundness. These hypotheses make
the boundary visible. They do not prove that a PostgreSQL query, TiKV range
read, or external file reader satisfies the law.

Each adapter therefore needs one of:

- a total Lean implementation over returned bytes plus a proved decoder;
- a narrow external primitive with an explicit contract and interoperable
  tests;
- a recorded conditional assurance level.

### Full algebra refinement and product routing

The indexed BGP proof is complete for its stated functions. The independent
algebra refinement is still incomplete. The full product also needs routing
and conformance gates that show a query reached the Lean backend being
claimed. This is proof and integration work, rather than a limit of the Lean
implementation model.

## Two meanings of partial

Do not conflate these:

1. A partial port has incomplete feature or proof coverage.
2. A Lean `partial def` is executable through the interpreter and compiler but
   opaque to kernel reduction. It cannot directly support the same equation
   proofs as a total definition.

At this commit, the library has 212 `partial def` declarations across 35
files. The harness adds 14 across 9 files. The concentration is:

```text
XPath 44   ShEx 50   OWL 37   XSLT 27   RIF 15
Math 11    Geo 6     MathML 5  Testing 4
```

The remaining library declarations are small groups in GRDDL, XForms,
JSONSchema, CSVW, XSD, Storage, Schematron, and HTTP. RDF, SPARQL, Cottas,
HDT, RDFS, SHACL, JSON-LD, and Unified have no live `partial def`
declarations. The block-engine source should remain total.

The live foreign family is the declared HACL* Ed25519 boundary. No new block
primitive should become external without a measured need and an explicit
agreement method.

## Roaring bitmap position

[`roaring_in_lean4.md`](roaring_in_lean4.md) is relevant after the first
simple block and scan exist. Roaring32 is a good fit for block-local row IDs,
candidate sets, postings, and intersections. It is not the global `TermId`
domain and does not replace sorted quad blocks.

Start with a pure Lean set meaning and a portable codec. Reuse the current
Cottas presence-bitmaps as a behavioral and proof comparison. Add native word
operations only after profiles show a need. The current absence of packed
wide-integer arrays makes dense bitmap speed a known toolchain concern; a
`ByteArray` representation keeps the first implementation executable.

## Revised first implementation unit

1. Define RDF 1.2 term identity and its decision theorem.
2. Define cross-position `TermId` and tagged `GraphId` relations.
3. Generalize one landed Cottas access shape into one uncompressed immutable
   block and one permutation.
4. Define `Block.denotes` as logical quads.
5. Implement one bounded scan.
6. Prove decoded scan results equal the existing semantic triple-pattern
   result for the supported fragment.
7. Expose it through the native Lean path.
8. Persist the same bytes in PostgreSQL and compare all three paths.

Roaring compression, PushIR, all permutations, and TiKV follow this vertical.

## Resume and measurement rules

1. Verify `HEAD` and the intended upstream reference before reporting a module
   absent.
2. Read this note, Part One, Part Two, and `skills/blockengine/SKILL.md`.
3. Re-measure declarations and build jobs; never copy these counts forward.
4. Run full `lake build`, with no target, before a green-build claim.
5. Record the next session in `docs/YYYYMMDD-blockengine-*.md`.
6. Keep dated observations in worknotes and stable rules in the skill.

The stale-checkout error in the first 2026-08-29 audit falsely classified
landed Cottas, HDT, and SPARQL refinement modules as absent. The old text was
replaced. This process error remains here so later agents check the commit
before they infer repository scope.
