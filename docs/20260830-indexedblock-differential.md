# Block engine worknote: indexed-block differential gate

Date: 2026-08-30

## Purpose

`l4block-id-diff` is an executable end-to-end regression gate for the current
Lean vertical.  Given Turtle and a parsed `SELECT`, it evaluates the same query
through two independently wired inputs:

```text
Turtle graph -> existing list-backed dataset evaluator

Turtle graph -> IndexedBlock -> IBK1 bytes -> decode -> IndexedBlock.readOps
             -> existing SPARQL backend evaluator
```

It compares the resulting solution sequences exactly.  It is intentionally not
a theorem: it protects the integration boundary while the general codec and
refinement theorems are extended.

## Evidence

The executable was built with:

```text
lake build l4block-id-diff
```

It passed on the 486-triple Wikidata active-site Schema.org-adjacent source
with an ordered, predicate-and-object-bound SPARQL query:

```sparql
SELECT ?item WHERE {
  ?item <http://www.wikidata.org/prop/direct/P31>
        <http://www.wikidata.org/entity/Q423026>
} ORDER BY ?item
```

The result contained 132 rows after the `IBK1` encode/decode path.  This checks
more than an SSE wrapper: the SPARQL evaluator receives only the decoded
indexed block's `BackendReadOps`, whose bound-predicate branch reads a physical
predicate posting partition.

The same gate also passed on the 9,227-triple `chromosome.ttl` corpus with a
parsed aggregate query over a predicate-bound triple pattern.  It produced one
`COUNT(*)` solution after a 526,057-byte `IBK1` round trip.  The end-to-end
differential run took 25.2 seconds on the development laptop; that includes
Turtle parsing, index construction, encoding, decoding, and both evaluator
routes, so it is not a query-only performance claim.

## Boundary

This is a real Lean storage/query vertical, but it is still an in-process
memory/file implementation.  PostgreSQL `bytea`, mmap, TiKV, range partitions,
and a canonical cross-input graph identity remain separate next milestones.
The PostgreSQL acceptance criteria are tracked in GitHub issue #635.
