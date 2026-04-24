# F* Readability Refactor Migration Plan

## Status

The draft readability refactor started under `tmp/fstar-readability-refactor/`
and introduces three buckets:

- `corespecs/` for standards-facing RDF/SPARQL/OWL material
- `midzone/` for explicit project policy choices where standards leave room
- `practical/` for executable representation, storage, indexing, and other
  implementation details

The first tracked step has been migrated into `formal/fstar/`:

- `formal/fstar/corespecs/`
- `formal/fstar/midzone/`
- `formal/fstar/practical/`
- `formal/fstar/practical/RDF.IndexedMemory.fst`

These modules are passive: they verify, but they are not yet wired into the
existing executable evaluator or generated runtime.

## Migration Rule

Do not merge the draft fork wholesale.

Move it in small, reviewable slices. Each slice should either be:

1. passive specification/readability structure with no executable behavior
   change, or
2. one executable behavior change with explicit parity tests against the current
   implementation.

`formal/fstar/` is the only canonical build and verification location. The
`tmp/fstar-readability-refactor/` tree is scratch history only and must not be
used by CI, release builds, or normal verification. If a useful draft module
from `tmp/` is promoted, copy it into `formal/fstar/`, wire that tracked copy
into `formal/fstar/Makefile`, and leave the `tmp/` copy out of all commands.

## Phase 1: Tracked Passive Structure

Goal: make the new conceptual structure reviewable without changing behavior.

Already done:

- added tracked `corespecs/`, `midzone/`, and `practical/` directories
- added the indexed in-memory graph sketch as a practical module
- updated `formal/fstar/Makefile` so the new modules participate in
  verification

Gate:

```sh
cd formal/fstar
opam exec --switch=fstar -- make -B verify
```

This must pass before any further migration.

## Phase 2: Keep Source Drift Boring

Goal: prevent the fork from silently reintroducing stale executable code.

Before copying any draft file over an existing executable file, compare against
main and classify the diff:

- comment-only: safe candidate
- path/module movement only: needs build/extraction review
- parser/query/runtime behavior change: needs tests first

Known stale divergence to avoid:

- draft `Parser.Turtle.fst` had an older local `resolve_iri`; main now delegates
  to `Parser.IRI.resolve_iri_v2`

Do not overwrite main's parser, algebra, protocol, or backend modules with
draft versions unless the behavioral diff is intentional and tested.

## Phase 3: Indexed Memory Parity

Goal: prove the indexed in-memory backend returns the same triples as list
search before it is used by SPARQL evaluation.

Add focused F* or OCaml-level tests that compare:

- graph with no triples
- graph with duplicate triples
- subject-bound lookup
- predicate-bound lookup
- object-bound lookup
- subject+predicate, predicate+object, and subject+object lookup
- fully bound lookup
- lookup for absent terms
- blank nodes
- plain IRIs and literals

Expected property:

```text
indexed_search (build_indexed_graph_store g) pattern
==
list_store_search g pattern
```

The comparison should account for RDF graph set semantics. If result ordering
differs, compare after stable sorting or as sets.

## Phase 4: Backend Integration Behind a Flag

Goal: use the indexed backend without changing the default path.

Add an indexed graph backend constructor to the store layer, but keep the list
backend as the default.

Required behavior:

- `backend_search` delegates to `indexed_search`
- `backend_estimate` delegates to `indexed_estimate`
- `backend_predicate_present` delegates to `indexed_predicate_present`
- existing list, HDT, COTTAS, and union backends continue to verify

Gate:

```sh
cd formal/fstar
opam exec --switch=fstar -- make -B verify
./build-ocaml.sh compile
```

Then run local backend parity tests.

## Phase 5: Query-Level Parity

Goal: show SPARQL results are unchanged when the same graph is evaluated through
the indexed backend.

Compare list and indexed backends for:

- simple BGPs
- joins with shared variables
- joins with no shared variables
- filters over matched variables
- named graph queries where applicable
- duplicate-sensitive SPARQL bag behavior
- existing local regression queries under `tests/local/sparql/`

Results must be compared after stable output ordering. The parity check should
distinguish RDF graph duplicate elimination from SPARQL solution multiset
semantics.

## Phase 6: Default Switch

Goal: make indexed memory the ordinary ephemeral backend for parsed data.

Only switch the default after:

- full F* verification passes
- extracted native build passes
- existing local regression scripts pass
- W3C RDF/SPARQL runner results are unchanged or any differences are explained
  and accepted
- at least one representative benchmark shows a useful improvement

The switch should be one small change: parsed graph data builds an indexed
backend by default, with a list-backed fallback retained for debugging and
parity checks.

## Risks

- **Semantic drift**: a readable spec module can look authoritative while the
  executable semantics still live elsewhere.
- **Stale fork code**: files under `tmp/` may lag behind main, especially parser
  fixes.
- **Bag semantics mistakes**: RDF graph deduplication is correct, but SPARQL
  solution duplicates can still be significant.
- **Blank-node identity**: indexed stores must preserve the same scoped blank
  node identity as the list-backed path.
- **Build tooling**: module moves can break extraction, JS/Wasm packaging, or
  generated OCaml ordering even if F* verification passes.

## Current Recommendation

Proceed incrementally.

Treat the new directories as a tracked design scaffold. Keep the current
executable modules as the product source of truth until a specific module has
parity tests and a narrow migration PR. The indexed memory backend should be
the first executable candidate, but only after list-vs-index parity is in place.
