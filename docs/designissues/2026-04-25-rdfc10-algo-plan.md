# RDFC-1.0 algorithm — scratch plan (Sade, 2026-04-25)

Companion to `2026-04-24-rdfc10-plan.md`. That doc scoped the test
corpus and design intent. This doc is the per-session worklog as the
algorithm itself lands in F\*.

## Goal

Flip the rdfc10_runner from "13/64 PASS (accidental — no-op
canonicalisation matches when there are no bnodes)" to a substantial
fraction passing. Realistic target: 30–45 of 64 eval tests.

## Approach

W3C RDFC-1.0 spec: <https://www.w3.org/TR/rdf-canon/>. Algorithm
phases:

1. **Hash First Degree Quads (HFDQ)** — for each blank node, render
   each quad it appears in, replacing its own occurrences with `_:a`
   and other bnodes with `_:z`. Sort the rendered quads
   lexicographically, concatenate, SHA-256.
2. **Canonical Identifier Issuer** — a stateful counter that hands out
   sequential `_:c14n0`, `_:c14n1`, … in deterministic order.
3. **Iterative assignment** — group bnodes by HFDQ; bnodes with a
   unique HFDQ get a canonical id immediately (in HFDQ-sort order).
4. **Hash N-Degree Quads (HNDQ)** — for each remaining HFDQ
   collision class, recursively hash neighbouring bnodes (using
   issuer state) with bounded permutation enumeration.
5. **Re-serialise** — replace every bnode label in the dataset with
   its canonical id; sort the resulting N-Quads lines lexicographically.

## Phase 1 (this session): HFDQ + simple issuer

Land in F\* (`RDF.Canon.fst`):

- `nquad_render_for_hash` — render a single quad in canonical form
  (per spec §4.7.3 Canonical N-Quads: IRIs `<…>`, bnodes `_:label`,
  literals `"lex"^^<dt>` or `"lex"@lang` or `"lex"`, escaping per
  N-Triples).
- `compute_hfdq` — for a given bnode, gather quads it appears in,
  rewrite its own label to `_:a`, others to `_:z`, sort, concat,
  SHA-256.
- `assign_canonical_simple` — initial pass: bnodes with unique
  HFDQ get `_:c14nN` in HFDQ-sort order.
- `canonicalize` — top-level entry: HFDQ pass, simple assignment,
  rewrite, sort.

Phase 1 is **HFDQ-only**: it solves all eval tests where every bnode
has a unique HFDQ (i.e. no symmetry / no isomorphic sub-graphs). On
the 64 eval tests, that includes:

- All zero-bnode tests (~20 tests already passing accidentally — now
  passing for the right reason since we sort+rewrite intentionally).
- All single-bnode tests (~10 — `_:e0` → `_:c14n0`).
- Many multi-bnode tests where each bnode has a distinct local
  neighbourhood (e.g. test005, test016, test017).

Tests where Phase 1 alone is insufficient: symmetric structures
(test019: two bnodes each only related to themselves, both have HFDQ
hash of `_:a <…> _:a`). Those need Phase 2 (HNDQ).

## Phase 2 (deferred — flag as STUB or FAIL): HNDQ

If HFDQ leaves collisions, run HNDQ recursively. Bounded by:

- Permutation enumeration of collision-class members → factorial
  blow-up. The spec says implementations "should" set a limit;
  practical implementations bail with an error past ~6 colliding
  bnodes. Acceptable for tests; real-world cases hit poorly.
- Recursion depth via fuel parameter (F\* termination).

For session scope: do simplest correct partial — when HFDQ
collisions remain, fall back to deterministic-but-maybe-wrong
(label by HFDQ then lexicographic original-label tiebreak).
This will fail a few tests (those with true symmetric collisions
needing HNDQ), but won't regress anything Phase 1 catches.

## Verification status

F\* verifies the module without `--lax`. `--admit_smt_queries true`
acceptable for the recursion-with-fuel patterns where total
correctness is not the immediate target. Tail-recursive helpers,
list-based hash maps (no Hashtbl in F\*).

## Out of scope this session

- Map tests (`RDFC10MapTest`) — would also need to emit the
  issued-identifier map JSON; deferred.
- Negative tests — none exist in the current upstream manifest.
- SHA-384 variant — runs on `rdfc:hashAlgorithm rdfc:SHA384`; only
  one or two tests use it; default SHA-256 fine for now.
- Verification proofs (functional correctness vs. spec). The module
  type-checks and extracts cleanly; semantic correctness validated
  by passing W3C tests, not (yet) by F\* lemmas.

## File layout

```
formal/fstar/RDF.Canonical.fst      // new — core algorithm (~350 LoC)
formal/fstar/ocaml-output/
  rdfc10_runner.ml                  // updated — call RDF_Canonical.canonicalize
build-ocaml.sh                      // updated — extraction list +
                                    // RDF_Canonical.ml in COMMON_MODULES
```

## Status

- [x] Plan doc committed
- [ ] RDF.Canonical.fst lands HFDQ
- [ ] rdfc10_runner.ml wired to F\* canonicalize
- [ ] Build + test, count pass/fail delta
