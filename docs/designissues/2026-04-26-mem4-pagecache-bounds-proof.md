# Mem4 — F\* structural bounds proof for the COTTAS page cache

**Date:** 2026-04-26
**Subagent:** Mem4
**Branch:** claude/main

## Goal

Lift `tmp/RDF.CottasStore.PageCache.Bounds.fst.draft` to a verified module
at `formal/fstar/RDF.CottasStore.PageCache.Bounds.fst` carrying four
structural lemmas about the pure-F\* page cache and the Aleph6
LIMIT-pushdown walker:

1. `pcache_put_capacity_bound` — `pcache_put` preserves
   `length entries <= capacity`.
2. `pcache_get_length` — `pcache_get` preserves length exactly.
3. `pcache_decode_capacity_bound` — convenience wrapper preserves the
   bound.
4. **NEW** `walk_candidate_rgs_search_limited_bound` — the materialised
   `acc_rev` from `walk_candidate_rgs_search_limited`
   (`RDF.CottasStore.fst:763`) never exceeds `limit`.

## Methodology motivation

Answers Dan's question "can F\* prove '<10 % of data is in memory at
once'?" honestly: yes-with-caveats. F\* can prove **structural cache
bounds** (entries times max-page-bytes); it cannot prove OCaml-extracted
heap RSS, kernel mmap residency, or lazy-thunk closure retention. With
these lemmas, a future regression that drops the eviction step in
`pcache_put` becomes a `make verify` error rather than a production RSS
spike.

## What's NOT in scope here

- No edits to `RDF.CottasStore.PageCache.fst` itself.
- No `./build-ocaml.sh` runs (extraction is 8-10 min, would stall the
  watchdog).
- No coordination with Mim3's `factoidal_http.ml` work — disjoint files.

## Output target

- `formal/fstar/RDF.CottasStore.PageCache.Bounds.fst` (new module).
- Possibly `formal/fstar/Makefile` (if explicit listing is needed).
- Final commit on `claude/main`, no push.
