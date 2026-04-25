# Issue #100 Phase 1 — Compound (S,P)/(P,O)/(S,O) indexes

Date: 2026-04-25
Agent: Het
Status: in-flight scratch (commit-on-write per CLAUDE.md rule on doc discipline)

## Goal

Extend `indexed_graph` (Phase 0, commit `be27bf9`) with the classic
triple-store trinity of compound indexes — keyed by `(S,P)`, `(P,O)`,
`(S,O)`. Wire `ig_search` / `ig_estimate` to prefer compound buckets
when both keys are bound, falling back to single-key buckets, falling
back to the full triple list. Make the BGP reorder selectivity-aware
through `choose_best_tp`.

(Note: `choose_best_tp` already does selectivity-aware reorder in
Phase 0 via `estimate_tp_store_mu`. No change needed there. With the
compound indexes, the same code path will see much tighter estimates
on `(S,P,?)` / `(?,P,O)` / `(S,?,O)` shapes.)

## Files touched

- `formal/fstar/RDF.Graph.Executable.fst` — three new bucket maps in
  `indexed_graph`, three new key-builder helpers (`sp_key`, `po_key`,
  `so_key`), updated `add_triple_to_indexes` and `empty_indexed`.
- `formal/fstar/SPARQL11.Algebra.fst` — `ig_search` / `ig_estimate`
  inspect compound buckets first when both keys are bound, fall back
  to single-key buckets next, then to full triple list.

## Key shape

Composite keys use ASCII unit separator `\x1f` (codepoint 0x1F) as the
delimiter. This codepoint cannot legally appear inside an IRI (RFC
3987 forbids U+0000–U+001F in IRI references) or in our blank-node
keys (which themselves are formed by prefixing `B_`/`I_`). Subject and
object keys reuse the existing `subject_to_key` / `term_to_key_opt`.

```
sp_key s p   = subject_to_key s ^ "\x1f" ^ p          : string
po_key p o   = p ^ "\x1f" ^ k    when term_to_key_opt o = Some k    : option string
so_key s o   = subject_to_key s ^ "\x1f" ^ k    when ... = Some k   : option string
```

Literals (whose `term_to_key_opt = None`) are not indexed in compound
maps that involve the object — same rationale as Phase 0: literal
matching has datatype/lang-tag normalisation we don't want to bake
into the key.

## ig_search bucket priority

Smallest qualifying bucket wins (we already have
`pick_smaller_bucket`). New priority order:

```
binding shape  →  buckets considered (smallest wins)
(S, P, _)      →  ig_sp[s|p]   (else falls through to single-key)
(_, P, O)      →  ig_po[p|o]
(S, _, O)      →  ig_so[s|o]
(S, P, O)      →  pick smallest of all three compound keys present
```

Single-key buckets (`ig_pred`, `ig_subj`, `ig_obj`) are still
considered, so a compound key with a None lookup degrades to single-
key gracefully.

## Memory cost

3 extra bucket maps per graph. Same insert path as Phase 0 — each
`bucket_push` is O(K) in the current bucket map size. Build cost
stays O(N · K_max). Memory roughly doubles vs Phase 0 (3 → 6 maps).

## Acceptance plan

- F* verifies clean (`make verify`).
- Sweep delta = 0 (physical layer only; no semantic change).
- Optional smoke: a Wikidata-shaped `?s wdt:P31 :Human` BGP should
  have `bs = Some _; bp = Some _; bo = None` and hit `ig_sp` instead
  of the larger `ig_pred` bucket.

## Out of scope

- Promoting compound indexes to a hashtable (Phase 2 territory; the
  cost-of-extraction stays the same with assoc-list buckets).
- mmap'd / on-disk indexes (Bet4 / Bet5).
- Named-graph G-keyed index (gap §2 in indexing-audit).
