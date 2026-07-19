# 2026-07-19 — Bet7 Step B: retiring the predicate/graph lazy-populate into verified F\*

## Status
Design. Perf-review-gated. NOT yet executed. This is the sole remaining
`VIOLATION-SEM` in the COTTAS layer after Step A completed
(`9f482943` + `04c466c2` deleted the entire dead id-based decode chain).

## The problem in one sentence
`sc_predicate_present : wf_iri -> Tot bool` (`RDF.Store.Capabilities.fst:151`)
is declared **`Tot`** but its COTTAS realisation
(`cottas_ondisk_predicate_present`, wired at `RDF.Store.Capabilities.Cottas.fst:93`)
runs a **Hashtbl-mutating lazy populate** (`predicate_present_fast` →
`ensure_predicates_loaded`, inserted by
`experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh`). The type says pure;
the body has a side effect. Same for `cottas_ondisk_named_graphs` (its
`#261` `ensure_graphs_loaded` override lives in `cottas_ondisk_runtime.sh`).
This is the effect-lie that keeps two glue patches alive and the "qualified
verified" footnote on rule #11.

## Why this is NOT a quick effect-signature change (the trap)
The naive fix — change `sc_predicate_present`'s effect to `ML` — ripples
across **every `store_caps` builder** that sets the field:
`RDF.Store.Capabilities.fst:151` (the record + in-memory default),
`:389`/`:422` (union/dispatch combinators, `union_predicate_present`),
`RDF.Store.Capabilities.Cottas.fst:93`, `RDF.Store.Capabilities.Delta.fst`,
`RML.VirtualSource.fst`, `SPARQL11.Store.fst` — plus every planner/pruning
consumer that calls `.sc_predicate_present` expecting `Tot`
(`SPARQL.Plan.*`, `factoidal_explain.ml:304`). Making the whole store
interface `ML` to accommodate one backend's lazy cache is the wrong
direction — it would infect the pure query planner with an effect it
does not need.

## Why it needs a human perf checkpoint (cannot self-gate)
The lazy populate exists to buy the documented open-time win
(`docs/designissues/2026-04-26-bet7-open-time-speedup.md`): deferring all
four column dictionaries drops COTTAS open from **106s → 0.023s** and RSS
**1.42 GB → 73 MB** on the UK-Parliament corpus (millions of quads), at the
cost of a one-time **~14s first-predicate-query** populate. **None of this
is observable on the vendored test fixtures** (the largest is 818 quads).
So any change here MUST be benchmarked before/after on a large corpus,
which this autonomous environment does not carry — hence the checkpoint.

## Recommended safe path — answer predicate-presence from the `.presence`
## companion, not from a dictionary populate

The elegant fix sidesteps the effect entirely. Predicate-presence does
**not** require the term dictionary at all — it is a set-membership question
that the already-F\*-verified **`.presence` companion file** answers
(`RDF.CottasStore.PresenceWriter.fst` defines its byte format;
`serialize_compound_presence`/`parse_compound_presence` are the
Option-B-realised, hash-witness-CI-gated readers). Reading a presence
bitmap is a **`Tot` byte read** — no populate, no side effect.

Proposed sequencing:

1. **Presence-backed `sc_predicate_present`.** Add/confirm a `Tot` F\*
   reader `presence_contains_predicate : presence -> wf_iri -> Tot bool`
   over the parsed `.presence` structure, and route
   `cottas_ondisk_predicate_present` through it instead of
   `predicate_present_fast`/`ensure_predicates_loaded`. `sc_predicate_present`
   stays genuinely `Tot`. **This removes the predicate half of the effect
   lie with zero dictionary populate** — and should be *faster* than the
   14s first-query populate, not slower (a presence bitmap read is the
   whole point of the companion). Benchmark to confirm.

2. **Named-graphs.** `cottas_ondisk_named_graphs` enumerates distinct graph
   tokens. If the graph column has its own presence/offset companion (or a
   small distinct-graph sidecar), answer from it as a `Tot` read. If not,
   the honest option is a narrow `ML` seam **local to the named-graphs
   enumeration only** (not the whole `store_caps` interface) — enumerating
   named graphs is a dataset-construction step (`SPARQL11.Store.fst:154,202`),
   not on the pure per-pattern planner path, so an `ML` effect there does
   not ripple into the planner.

3. **Load-mode decision → `SPARQL.Plan.Loader.fst`.** Move the eager-vs-lazy
   "which columns to populate at open" policy (today hard-coded in the Bet7
   patch's `new_build`, which defers all four) into a verified F\* decision
   in `SPARQL.Plan.Loader.fst`. The actual populate stays an `ML`
   realisation behind `RDF.CottasStore.LazyDict.fst`'s existing
   `assume val mk_lazy_dict : ... -> ML (lazy_dict a)` seam (already honest
   about its effect) — but it is now *invoked from* a verified decision,
   not baked into an OCaml patch.

4. **Delete the glue.** Once (1)–(3) land, `cottas_ondisk_z_lazy_open.sh`
   (predicate/graph half) and the `#261` `named_graphs` override in
   `cottas_ondisk_runtime.sh` have no live role → delete them. Retires the
   last COTTAS `VIOLATION-SEM`; the rule #11 "qualified verified" footnote
   can then be dropped for the on-disk backend (recovery-plan Phase 9).

## Benchmark protocol (the gate)
Run `docs/designissues/2026-04-26-bet7-open-time-speedup.md`'s own protocol,
before and after, on the UK-Parliament COTTAS store:
- **Open time** (`factoidal cottas-info` / the smoketest open path): must
  stay ≈0.023s, RSS ≈73 MB (i.e. the eager-populate regression must NOT
  return).
- **First predicate query**: presence-backed `sc_predicate_present` should
  be **≤** the current ~14s first-query populate cost (expected: much less —
  a bitmap read, not a full dictionary build).
- **Named-graph enumeration**: unchanged or better.
- **Correctness**: unit tests 47/47, COTTAS smoketest, SPARQL 1.1 631/0,
  GSP 19/0, all store-backed regime suites — green.

## What's out of scope
- Changing `sc_predicate_present`'s effect to `ML` across the store
  interface (the trap above). Do not.
- Any change to the `_tok` production search path (already verified + live).
- The `.presence`/`.offsets` byte formats themselves (already F\*-spec'd +
  CI-gated; this reuses them, does not redefine them).

## Verification of the premises in this doc
Field type + ripple set confirmed against the tree 2026-07-19:
`sc_predicate_present : wf_iri -> Tot bool` at `RDF.Store.Capabilities.fst:151`;
Cottas realisation at `RDF.Store.Capabilities.Cottas.fst:93`; `lazy_dict`'s
`ML` populate seam at `RDF.CottasStore.LazyDict.fst:31-39`; named-graphs
consumers at `SPARQL11.Store.fst:154,202`. Perf numbers quoted from
`2026-04-26-bet7-open-time-speedup.md`.
