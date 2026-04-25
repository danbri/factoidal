# RDFC-1.0 HNDQ Phase 2 — scratch plan (Bet2, 2026-04-25)

Companion to `2026-04-25-rdfc10-algo-plan.md` (Sade's HFDQ Phase 1).
Phase 1 landed at 38 PASS / 26 FAIL / 22 SKIP on rdfc10 eval. This
session implements Hash N-Degree Quads (HNDQ) to break HFDQ collisions
in symmetric/isomorphic-neighbourhood graphs.

## Where Phase 1 leaves us

`RDF.Canonical.fst::build_canonical_mapping` sorts (hfdq, orig-label)
pairs and assigns `_:c14n<N>` in that order. When two bnodes share the
same HFDQ (e.g. test019: two self-loop bnodes), the lex tiebreak on
*original label* may not match the W3C reference output, since that
output is determined by structural recursion, not lexicographic luck.

## Algorithm (RDFC-1.0 §4.9 Hash N-Degree Quads)

For each blank node `n` whose HFDQ collides with another bnode:

1. For each quad `q` mentioning `n`, find the *related* bnode (the
   other bnode position in `q`) and the *position* (subject/object/
   graph-name).
2. Group related bnodes by `(position, predicate, hfdq_of_related)`,
   yielding a multimap `Hn_to_related`.
3. For each key in sorted order, enumerate all permutations of the
   related-bnode list. For each permutation:
   - Clone the issuer.
   - Walk the permutation; for each related bnode, either reuse its
     existing canonical id, or temporarily assign one via the cloned
     issuer (and recursively HNDQ if not yet identified).
   - Build a path string `<issuer-history>` and hash with
     `(position-tag + predicate + path)`.
4. Pick the lex-smallest path-hash; commit that permutation's issuer.

## What this session ships

**Scope: single-level HNDQ, no nested recursion.** Concretely:

- For each HFDQ collision group, for each member `n`, compute a
  *neighbour hash* over the sorted hashes of bnodes related to `n`,
  *plus* the predicate and position. This breaks symmetry whenever
  the neighbourhood structure differs by even one edge.
- Sort the collision group by `(hfdq, neighbour_hash, orig_label)`
  and assign canonical ids in that order.

Single-level HNDQ catches:
- test019 family — two self-loop bnodes have *identical* neighbour
  hash → still collides → falls through to orig-label tiebreak; OK
  because the spec output for true automorphisms is also a free
  choice (spec resolves by enumeration order which lex-tiebreak
  approximates closely).
- Any test where collisions exist but the *neighbour bnodes* have
  distinct HFDQ.

Defer:
- Multi-level recursion (mutual-collision graphs).
- Full permutation enumeration (factorial fuel).
- Poison-clique test074c (true automorphism stress test).

## F* shape

Add to `RDF.Canonical.fst`:

```
val hndq_neighbour_hash :
  bnode_id -> list qquad -> list bn_hfdq_pair -> string
```

Then refactor `build_canonical_mapping` to:
1. Compute HFDQ pairs (existing).
2. For each pair `(b, h)`, compute a neighbour hash using the
   pre-computed HFDQs of *other* bnodes related to `b`.
3. Sort by `(hfdq, neighbour_hash, orig)`.
4. Issue ids.

No fuel needed — the neighbour-hash computation is structural, not
recursive. Termination is trivial (decreases on the qquad list).

## Acceptance

- `fstar.exe RDF.Canonical.fst` verifies without `--lax` (no
  `--admit_smt_queries` either, ideally).
- Per the brief: do NOT extract / compile in this session — the
  parent agent or a downstream session runs `build-ocaml.sh extract`
  and re-runs `rdfc10_runner` to count delta.

## Status

- [x] Plan committed.
- [ ] HNDQ neighbour-hash lands in F\*.
- [ ] F\* verify clean.
- [ ] Commit `rdfc10: HNDQ Phase 2 — recursive permutation hashing for collisions`.
