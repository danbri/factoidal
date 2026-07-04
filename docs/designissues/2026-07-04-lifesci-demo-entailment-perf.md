# 2026-07-04 — lifesci demo: entailment ("Logic") hangs, diagnosis + consumer-side fix

**Status:** consumer-side UX fix landed (this session, no `.fst` touched);
engine-side root cause filed below as follow-on work. Trigger: owner report
that `https://danbri.github.io/factoidal/fstar-extracted/demo-lifesci.html`
is very slow and hangs, especially with RDFS or OWL-RL entailment enabled.

## 1. Summary

- **Reproduced outside the browser, measured.** The hang is real and has
  nothing to do with tonight's #262 (sameAs closure) or #272 (serializer
  scaling) fixes — neither applies to this dataset. Root cause is closure
  **fixed overhead at this data scale, recomputed from scratch on every
  query, on 3 separate named graphs, synchronously on the browser's main
  thread with no caching and no progress feedback**.
- The three lifesci KGX Turtle files (`docs/fstar-extracted/lifesci/`,
  9,227 + 6,455 + 27,421 = 43,103 triples) contain **zero** `owl:sameAs`,
  `rdfs:subClassOf`, `rdfs:subPropertyOf`, `rdfs:domain`, or `rdfs:range`
  triples. There is no schema to entail from. RDFS closure adds a flat
  **+16 triples per named graph** regardless of graph size (reflexivity /
  container-membership axioms over the small set of vocabulary IRIs used
  as `rdf:type` objects) — i.e. the entailment payoff on this dataset is
  close to zero, yet costs tens of seconds to a minute-plus per query.
- `factoidal_cli.ml`'s `apply_entail` (bin/factoidal-cli/factoidal_cli.ml:1146-1160)
  runs the full closure — unconditionally — on the default graph **and on
  each named graph separately**, every time the CLI process starts. In the
  browser, one CLI process = one query "Run" click (see §2). So a 3-graph
  demo pays the closure cost **3 times per click**, and again on the next
  click, forever — nothing is cached across queries in the same page
  session.
- The #262 sameAs-cluster fix (`4812c3d`) and the #272 serializer fix
  (`ef58037`) are real fixes for their own workloads but **do not touch
  this bottleneck**: this dataset has no sameAs triples (so the O(k⁶)→O(k³)
  rewrite never fires) and the JSON result payloads here are 10-25 rows
  (so serializer throughput is irrelevant). The dominant cost is the
  RDFS/OWL-RL closure's **per-step index-build + rule-chain + dedup-sort
  overhead at N ≈ 27K**, which is a distinct cost center from both landed
  fixes.

## 2. How the demo invokes the engine (confirms "hang" mechanism)

`docs/fstar-extracted/demo-lifesci.html` embeds one
`<factoidal-sparql-client>` web component (`docs/fstar-extracted/factoidal-sparql-client.js`)
with `engines="js,wasm"` and no `default-logic`/`entail` attribute, so the
Logic radio defaults to **`none`** — the demo is already safe out of the
box. The owner's report is about what happens once a user manually selects
RDFS or OWL-RL.

For the `js` engine path (`_onRunClick`, factoidal-sparql-client.js:1433+):

1. One `await new Promise(r => requestAnimationFrame(r))` yields exactly
   one frame so the "Running…" status paints (line ~1462).
2. Then `(new Function(bundleSrc))()` executes **the entire compiled
   OCaml CLI program synchronously**, with `process.argv` set to
   `['node', 'factoidal', '--named', ..., '-e', '<query>', '-o', 'json']`
   plus `--entail RDFS|OWL-RL` when the Logic radio isn't `none`
   (factoidal-sparql-client.js:1627-1650). This one synchronous call does
   file-load, parse, **closure**, query eval, and JSON serialize, with
   zero yields in between. There is no web worker, no chunking, no
   incremental progress — the single rAF yield in step 1 is the entire
   extent of "responsiveness" the page gets.
3. Because the CLI reloads and re-closes all data on every invocation
   (there is no persistent in-page dataset/closure cache), every click of
   Run repeats the full cost, RDFS or OWL-RL, regardless of whether the
   previous click already computed the same closure.

This matches the owner's description exactly: pick RDFS or OWL-RL, click
Run, the tab freezes for the durations in §3 with no indication of
progress or expected duration, which reads as a hang rather than a slow
operation.

## 3. Measured: query × engine × entailment → wall time

Native runs: `bin/linux-x86_64/factoidal`, committed binary, this commit.
`node` runs: `docs/fstar-extracted/factoidal.js` (the same bundle the
browser loads), driven the same way `tests/web-demos/lifesci_parity.sh`
does. All three named graphs loaded every time
(`urn:kgx:chromosome`, `urn:kgx:sequence_variant`, `urn:kgx:disease`,
43,103 triples total). Queries from
`examples/wikidata/subsets/lifesci-kgx/queries/`.

| query | engine | entail | wall time |
|---|---|---|---:|
| 01 count-per-graph | native | none | 1.22 s |
| 04 top-diseases | native | none | 2.04 s |
| 01 count-per-graph | native | RDFS | 55.54 s |
| 02 top-types | native | RDFS | 43.13 s |
| 03 variant-chrom | native | RDFS | 41.03 s |
| 04 top-diseases | native | RDFS | 40.84 s |
| 05 disease-causes | native | RDFS | 45.77 s |
| 01 count-per-graph | native | OWL-RL | **> 590 s (cap trip, see §3.1)** |
| 01 count-per-graph | node/js | none | 6.11 s |
| 01 count-per-graph | node/js | RDFS | 133.53 s |

Observations:

- **RDFS cost is flat across queries** (≈ 41-56 s regardless of which of
  the 5 demo queries runs) — confirms the cost is dominated by closure
  computation, which runs identically before every query regardless of
  what the query actually needs, not by query evaluation itself.
- **RDFS closure output is negligible**: chromosome 9,227→9,243 (+16),
  sequence_variant 6,455→6,471 (+16), disease 27,421→27,437 (+16) triples.
  Forty-plus seconds of wall time buys 48 new triples total across three
  graphs with no schema-shaped data to entail.
- **jsoo/node overhead compounds the base cost**: baseline (no
  entailment) native→node is a ~5× slowdown (1.22 s → 6.11 s); under RDFS
  it's a ~2.4× slowdown (55.54 s → 133.53 s) — smaller *relative*
  multiplier but a much larger *absolute* one (+78 s). The browser build
  (`docs/fstar-extracted/factoidal.js`) is the same bundle used here, so
  133 s (over two minutes) is the realistic per-click RDFS cost in the
  actual demo for the heaviest query, before accounting for the browser's
  own event-loop/GC pressure being worse than Node's.
- **OWL-RL did not complete within a 590 s (~10 min) cap** on the native
  binary for the cheapest query in the set (count-per-graph, which does
  not even touch entailment-derived triples). See §3.1 for the cap-trip
  detail. In the browser this presents as an indefinite hang with no
  feedback — exactly the report.

### 3.1 OWL-RL cap trip

`timeout 590 bin/linux-x86_64/factoidal --named ... --entail OWL-RL -q
01_count_per_graph.rq -o json` was run to the 590 s cap (rule #17
discipline: never let an ad-hoc run exceed 10 minutes) and did not
return; the process was still consuming 100% CPU with RSS climbing
(~55 MB → ~72 MB and rising) up to the cap. OWL-RL applies 28 rules per
closure step (vs. RDFS's 7) via `owl_rl_closure_step`
([`RDF.Graph.Executable.fst:3661`](../../formal/fstar/RDF.Graph.Executable.fst))
on top of the RDFS closure, across the same 3 named graphs, once per
query invocation — so it inherits the RDFS flat overhead documented in
§4 four times over (28/7) at minimum, before any rule-chain effects. This
dataset has zero `owl:sameAs` triples, so the #262 O(k⁶) sameAs-cluster
bug (fixed in `4812c3d`) is not implicated; whatever is consuming the CPU
here is a **different** cost center — most likely the same per-step
`build_indexed` (6 full-graph sorts) + `graph_dedup_sort` overhead as
RDFS (§4) multiplied by 4× the rule count and probably more fixpoint
iterations, since OWL-RL's rule set includes rules (e.g. `prp-*`,
`cls-*`) that can each independently extend the live list before the
end-of-step dedup. This needs instrumented per-rule timing to localise
precisely — flagged as follow-on work in §6, not solved here.

## 4. Root cause: closure step fixed overhead is too high for zero-payoff data, and it's recomputed with no caching

Two independent causes, both real, neither the same as #262 or #272:

**(a) Per-step overhead, not rule-driven cost.** `rdfs_closure_step`
([`RDF.Graph.Executable.fst:1139`](../../formal/fstar/RDF.Graph.Executable.fst))
calls `build_indexed` (six full-graph sorts: pred/subj/obj/sp/po/so
buckets, each `List.Tot.sortWith` over the whole graph) once per step,
then chains 7 rules, then `graph_dedup_sort` once more. Even when *every*
rule is a no-op (this dataset has no subClassOf/subPropertyOf/domain/range
triples to match), the step still pays for building all six indexes and
the final sort over N ≈ 27K elements. `rdfs_closure_with_reflexivity`
([`RDF.Graph.Executable.fst:1293`](../../formal/fstar/RDF.Graph.Executable.fst))
runs this twice (a closure pass, then a second closure pass after adding
reflexivity axioms) — so minimum 2 full index-builds per graph even at
the true fixed point. §262's diagnosis already established the O(k⁶)
per-step blow-up mechanism for the sameAs cluster; this is the same
per-step-overhead family of bug but showing up as **flat cost at rest**
rather than **superlinear growth with a sameAs clique** — a fixed constant
that is simply too large for interactive use at N in the tens of
thousands, independent of what data is in the graph.

**(b) No caching, applied 3× redundantly, unconditionally.**
`apply_entail` in `factoidal_cli.ml:1146` runs closure on the default
graph *and* each named graph *separately*, every CLI invocation,
regardless of query shape — `01_count_per_graph.rq` needs no entailed
triples at all (it's `COUNT(*) GROUP BY ?g`) but still pays full closure
on all 3 named graphs before evaluating. Because the browser demo
launches one full CLI process per "Run" click (§2), this multiplies to:
**(closure cost) × 3 graphs × every click**, with zero reuse even when
back-to-back clicks use the identical dataset and Logic setting.

## 5. What's fixed here (consumer-side, no `.fst` touched)

`docs/fstar-extracted/factoidal-sparql-client.js` (hand-written web
component glue, not extraction output — safe to edit directly, unlike
anything under the verified-library boundary):

- **Perf notice under the Logic radios.** Selecting RDFS or OWL-RL now
  shows a persistent warning that states the actual behaviour
  (`_updateLogicWarning`, wired to a delegated `change` listener on the
  Logic radio group): the closure recomputes from scratch on every Run
  with no caching, runs synchronously on the main thread, and — for this
  dataset — measures tens of seconds (RDFS) to minutes (OWL-RL), and an
  unresponsive page during that window is expected, not a crash.
- **Updated Logic radio tooltips** with the same cost/behaviour
  description (previously just named the entailment regime with no perf
  caveat).
- **Updated in-flight progress message.** The "Running…" panel's
  sub-line now names the active entailment regime and repeats the
  "page will not respond until this completes" caveat while a local
  (non-remote) engine run with RDFS/OWL-RL is in flight — previously it
  said only "Fetching data, parsing, evaluating…" regardless of Logic
  setting, giving no signal that a multi-minute wait was normal.
- The default Logic setting was **already** `none` in
  `demo-lifesci.html`/`demo-lifesci-v2.html` (no `default-logic`/`entail`
  attribute set) — no change needed there; the risk was entirely in what
  happens after the user opts in to RDFS/OWL-RL, which is what these
  changes address.

This is a UX fix, not a performance fix: the closure is still slow and
still uncached. It converts "the demo is broken" into "the demo told me
this would take a while."

## 6. Ranked fix plan (not implemented here — filed for follow-on work)

Consumer-side (`bin/`, `docs/fstar-extracted/*.js` — no `.fst`):

1. **Cache the closure across queries in one page session (highest
   value, moderate effort).** Once a user picks RDFS/OWL-RL, compute the
   closure once per (dataset, regime) pair and reuse it for subsequent
   queries in the same session, instead of recomputing on every Run. This
   alone would turn "N clicks × 45 s" into "1 × 45 s + N × ~1-2 s" for
   this demo. Needs either: a CLI mode that accepts a pre-closed dataset,
   or client-side detection of "same 3 files + same regime as last run,
   reuse in-memory result" — the latter requires the jsoo bundle to
   expose the closed dataset back to JS, which it currently doesn't (the
   whole pipeline is one opaque `argv`-in / stdout-out call). Estimate:
   commit-sized if a "closure cache" mode is added to `factoidal_cli.ml`;
   larger if it requires bundle API changes.
2. **Move the local-engine run off the main thread (Web Worker).**
   Doesn't reduce the cost, but stops the tab from freezing and would let
   real progress/cancel UX exist. Non-trivial: the bundle currently
   depends on `globalThis.jsoo_fs_tmp`, `globalThis.process`, and
   `console.log`/`console.error` monkey-patching happening in the same
   realm as the `Function` eval; porting that to a worker means
   re-plumbing the FS shim and message-passing the captured stdout back.
   Not "small and safe" — estimate multi-commit.
3. **Only close the graphs the query actually touches.** For
   `01_count_per_graph.rq` (no entailment-sensitive predicates at all),
   closure work is pure waste. A cheap static check — "does this query's
   BGP reference any predicate/class the closure could add facts about"
   — could skip closure entirely for queries like this one. Consumer-side
   only if implemented as a pre-check in `factoidal_cli.ml`; judgement
   call on whether that belongs in the CLI (pragmatics) or needs an F*
   predicate for soundness (probably the latter, since "could add facts
   about" needs to reason about the full rule set, not a string grep).

Engine-side (`.fst`, out of scope for this task, filed as the actual
performance fix):

4. **Cut the fixed per-step overhead in `rdfs_closure_step` /
   `owl_rl_closure_step`.** §4(a): six full-graph sorts via
   `build_indexed` plus a final `graph_dedup_sort`, run at least twice
   (RDFS) or more (OWL-RL, more rules + reflexivity pass), even when zero
   rules fire. Candidates: skip the second `rdfs_closure` pass in
   `rdfs_closure_with_reflexivity` when `rdfs_reflexivity_axioms` yields
   no new axioms (cheap early-exit, since `add_triples_if_new` already
   computes membership); investigate whether `build_indexed`'s six
   separate `List.Tot.sortWith` passes can share a single sort (sort once
   by the full quad, derive the other five bucket orderings from slices)
   rather than re-sorting the same N elements six independent times.
   Needs its own instrumented before/after measurement — do not claim a
   fix here without re-running §3's table.
5. **Localise the OWL-RL cap-trip from §3.1.** Per-rule timing inside
   `owl_rl_closure_step` (the same technique the #262 diagnosis doc used
   for the sameAs cluster) to find which of the 28 rules is dominant on
   this data, since it isn't the sameAs cluster (zero `owl:sameAs`
   triples present). Prerequisite for any OWL-RL perf claim on
   data-scale (not synthetic-clique) graphs.
6. **Stop closing 3 named graphs independently when the CLI only needs
   one dataset-wide closure.** `apply_entail` in `factoidal_cli.ml:1146`
   runs closure per-graph; combining the default graph + all named graphs
   into one closure pass (respecting graph provenance in the output)
   would cut the ×3(or ×4 with the default graph) multiplier to ×1 and
   also fix a latent correctness gap — entailment that should span graphs
   (e.g. a `rdfs:subClassOf` declared in one named graph, applied to
   `rdf:type` triples in another) is currently invisible, since each
   graph is closed in isolation. This is a CLI/pragmatics change
   (`bin/factoidal-cli/factoidal_cli.ml`), not a `.fst` change, but is
   grouped here because it changes entailment *semantics* (cross-graph
   visibility) and needs its own conformance check before landing.

### Gates for any engine-side fix from this list

- Re-run §3's table (native + node/js) on the same lifesci fixtures;
  report labelled before/after wall times, not raw deltas.
- W3C SPARQL 1.1 entailment-regime suite (70/70) and full RDF/SPARQL
  suites unchanged (per the #262 diagnosis's own gate list, which
  applies here too since both touch the same closure code paths).
- If item 6 (cross-graph closure) lands, re-verify OWL-RL/RDFS
  profile-RL scores explicitly, since combining graphs before closure is
  a semantics change, not just a perf change — a query's entailed answer
  set can differ (this is the fix, not a regression, but must be stated
  as such in the commit message).

## 7. Files referenced

- `docs/fstar-extracted/demo-lifesci.html`,
  `docs/fstar-extracted/demo-lifesci-v2.html` — demo pages (unchanged;
  Logic already defaults to `none`).
- `docs/fstar-extracted/factoidal-sparql-client.js` — consumer-side fix
  landed here (§5).
- `bin/factoidal-cli/factoidal_cli.ml:1143-1160` — `apply_entail`,
  the per-graph unconditional closure call.
- `formal/fstar/RDF.Graph.Executable.fst:1139` (`rdfs_closure_step`),
  `:1293` (`rdfs_closure_with_reflexivity`), `:3661`
  (`owl_rl_closure_step`), `:500` (`build_indexed`), `:980`
  (`graph_dedup_sort`) — closure engine, root cause location for the
  engine-side follow-on.
- `docs/designissues/2026-07-03-owl-rl-sameas-blowup-diagnosis.md` — the
  #262 diagnosis this doc builds on and distinguishes from (sameAs
  clique blow-up vs. flat per-step overhead at data scale).
- `docs/fstar-extracted/lifesci/{chromosome,sequence_variant,disease}.ttl`
  — the fixture data (43,103 triples total, zero sameAs/subClassOf/
  subPropertyOf/domain/range triples).
- `tests/web-demos/lifesci_parity.sh`,
  `tests/web-demos/lifesci_queries.json` — how the queries were driven
  for the node/js measurements in §3.
