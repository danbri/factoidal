# Fable notes — 2026-07-06

Written by the Claude Fable 5 session that ran the docs-hub, database,
and virtual-sources programs, for the models that continue this
collaboration. Access to this model tier is expected to lapse for an
unknown period. Everything below is either measured, observed in this
repo, or clearly marked as judgement. Read CLAUDE.md first; this doc
sits underneath it — strategy and texture, not rules.

## 1. Where the project actually stands

The one-sentence position: a formally verified RDF/SPARQL engine that
is now also a real database, with conformance at or near the top of
the field and performance mid-pack and climbing.

Measured, as of commit a23ea27 (2026-07-06):

- W3C runnable total 1662 pass, 0 fail — SPARQL 1.1 631/0, RDF 1.1
  1031/0. These two are THE FLOORS: every landing re-verifies them
  from repo root. SHACL 120/120, RDFC-1.0 86/86, RML 76/76, ShEx
  1181 of 1182 (1 upstream fixture defect), JSON-LD toRdf 460/467,
  OWL 2 RL PE 28/30 (the 2 are a documented-impossible comprehension
  pair), RIF Core 34/50 (labeled skips), VC stage 1 109/120.
- Database: durable SPARQL UPDATE (append-only delta log, framing
  round-trips proved in F\*, SIGKILL harnesses accept zero torn
  states), native COTTAS writer v2 (13.90 B/quad on the 888,949-quad
  gene corpus, DuckDB byte-exact), HDT read path stages 1-4 fully
  verified, in-memory bytes store (64.4 B/quad native; 67 B/quad
  retained in the browser vs 612 heap), IndexedDB persistence proved
  across real reloads, Graph Store Protocol + SPARQL protocol server
  AND client.
- Tri-target is real: native, js_of_ocaml, wasm_of_ocaml all pass
  parity pins; wasm reads COTTAS byte-identically to native since
  the stdint .wat shim (a23ea27). KaRaMeL C: 107/134 modules clean
  (docs/designissues/2026-07-06-karamel-coverage-audit.md) but the
  C-to-wasm route is measured dead for speed (see §3).
- This week's extensions: LATERAL (Jena-differential-verified),
  GeoSPARQL v0 (pure exact-rational), fulltext slice 1 (jena-text
  vocabulary), SPARQL protocol client, virtual-sources design
  ratified with two implementation slices in flight at time of
  writing.

## 2. The owner and the collaboration

The owner is danbri — deep RDF/SemWeb background. Never explain RDF
basics. He reads code and specs, spot-checks claims (he once probed
an empty-dataset ASK to catch missing axiomatic triples, #281), and
gives terse, high-trust directives ("Kutgw", "do X NOW", "Yup").
Things that have gone wrong with him watching, and the corrections:

- Cryptic jargon: "Wtf is a floor?" — define terms in plain language
  on first use. Floor = a score that must never drop. Landing =
  commit + push after the gate battery.
- Miscounted triples in a doc example; overclaimed that class
  equivalence needs OWL. He caught both. Check examples like code.
- Bare ratios ("972/59") are banned — write "972 pass, 59 fail (out
  of 1031)". This is anti-pattern #25 and he notices violations.
- No sycophantic adjectives (markdown-style skill). The sentence
  carries weight or it doesn't.
- Iron rule #13: NO Claude attribution in commits. The harness
  default trailer must be actively suppressed every time.

He asks compound questions in bursts ("Also X. Also Y. Are Z???").
Answer every clause; he notices dropped ones. When he says a thing
twice across sessions (named graphs, HACL\*, "no regressions pls"),
it becomes a standing directive — treat it as permanent.

## 3. Findings this week that should steer strategy

1. **The join is the biggest unclaimed prize.** At 1M triples, a
   2-pattern join+FILTER times out at 600s on ALL THREE runtimes
   (docs/test-results/runtime-bench.json). This is algorithmic —
   almost certainly nested-loop evaluation in SPARQL11.Algebra — and
   no amount of runtime or data-structure work fixes O(n·m). A
   hash-join (build side chosen by sc_estimate, which already exists
   in store_caps and is underused) is plausibly the single largest
   perf win available. Nobody has attacked it yet.
2. **The C-to-wasm hypothesis is dead; wasm_of_ocaml is the wasm
   strategy.** Measured on the delta log: C-wasm tracks C-native to
   N=5,000 then cliffs 48x at 10,000 and fails at 20,000, while
   wasm_of_ocaml BEATS the native binary on Turtle parse (4.08s vs
   6.46s at 1M). Full matrix in docs/web/perf/. Do not reopen this
   without new evidence.
3. **The dominant cost everywhere is extracted data-structure
   shape**, not runtime choice: list-of-char strings, list-based
   solution multisets, ~41 KB RSS per delta entry. A byte-buffer /
   compact-string core in F\* would lift parse, serialize, joins,
   and RAM simultaneously. Large, risky, highest structural payoff.
4. **Profile before rewriting.** The "GROUP BY problem" was not in
   GROUP BY: callgrind put it in build_indexed's sort recomputing an
   allocating key O(N log N) times. The Schwartzian fix (09aac50)
   sped up every in-memory query. The diagnosed residual — eager
   construction of all 6 bucket indexes even when a query reads none
   — has an agent on it now; if unlanded, it's specified in that
   commit's report thread.
5. **The capability seam (store_caps) has paid for itself
   repeatedly.** HDT, delta overlay, the bytes store, virtual RML,
   and the tool-wrapping design all plug in through
   caps_of_backend without evaluator changes. Protect this seam;
   route every new backend through it; resist per-backend special
   cases in the evaluator.
6. **Differential testing beats prose.** The LATERAL agent probing a
   live Jena caught two substitution-semantics bugs the spec text
   would never have settled. Jena 5.2.0 is cached at
   ~/.cache/factoidal-bench/apache-jena-5.2.0; pyoxigraph installs
   clean. Use them as oracles for any semantics on the SPARQL 1.2
   track.

## 4. What is missing (gaps a "world class offering" still has)

Ranked by my judgement of impact:

1. **RDF-star / SPARQL 1.2.** Not implemented at all. The rdf12
   working group's test suites exist; a 2026 "world class" RDF
   database without quoted triples is increasingly conspicuous.
   LATERAL was the first 1.2-track feature; RDF-star is the second
   and much larger. Needs a design doc first (term model change
   touches RDF.Term — the deepest possible change; the stratification
   work makes it cheaper if sequenced after).
2. **Join algorithm + planner** (see §3.1). sc_estimate exists;
   nothing reorders BGPs by it, and OPTIONAL appears to re-issue
   per-row searches (q6 hypothesis, unconfirmed — verify first).
3. **The #118 glue migration.** ~4,000 lines of unverified OCaml on
   the COTTAS fast paths is the reason the README qualifier exists.
   The bound-side landing (9c3d160) already made part of
   cottas_runtime.sh's term-dictionary machinery dead on the live
   query path — deleting dead glue is cheap ratchet progress before
   the harder rewrites.
4. **Fulltext ranking** (score is a stub) and index persistence (the
   design doc's later slices — in-memory rebuild-on-batch landed).
5. **GeoSPARQL phases 3-5**: R-tree over bboxes, then the COTTAS
   geometry column + H3-Roaring sidecar. Phase 6 (buffer/convexHull)
   needs the owner's GEOS decision — pure-F\* was his instruction
   for v0; revisit explicitly, don't assume.
6. **Concurrency/transactions**: single-writer + concurrent readers
   is proven; group commit, multi-statement transactions, and any
   isolation story beyond snapshot-by-epoch are absent.
7. **Server hardening**: no auth, no per-client quotas, read-only
   flag is the only safety. Fine for demos; not for a hosted write
   endpoint.
8. **VC crypto via HACL\*** (#63): the verified-crypto adoption has
   a policy doc (skills/crypto-policy) but signatures still route
   through stubs; VC stage 2 is blocked on it.
9. **Wasm zstd decompress** is identity-shimmed — wasm reads
   uncompressed COTTAS only. Documented in build-ocaml.sh's header.
   Same shim mechanism as the stdint fix applies (wat module or a
   vendored wasm zstd).
10. **The Fly.io Parliament endpoint** runs a pre-GSP binary. The
    fly-deploy workflow exists and fails fast on the missing
    FLY_API_TOKEN secret — only the owner can add it. Nag gently.

## 5. Workflow: what works, what bites

The operating pattern that produced ~15 clean landings today:

- **Orchestrate on the expensive model, implement on sonnet-class
  agents, one agent = one commit-sized deliverable** with a
  code-sketch-bearing brief (anti-patterns #23/#24). Briefs that
  cite file:line and name acceptance tests come back landable;
  "figure it out" briefs come back as essays.
- **Worktree isolation for every code agent.** Main checkout stays
  clean for the coordinator. Budget ~1 GB per worktree and PRUNE
  IMMEDIATELY after landing — this box hit 100% disk mid-day and
  test failures from ENOSPC look exactly like real regressions.
- **The landing series** (do not improvise): cherry-pick the agent's
  single commit onto origin tip in its own worktree (never rebase
  its whole branch — worktree branches often carry superseded
  pre-amend history); conflicts will be binaries/build-state 95% of
  the time — take theirs, then REBUILD from merged source (extract,
  not just compile, if any shared .fst changed); run the floors
  YOURSELF from the worktree root plus the feature e2e set; restore
  CI-owned docs/test-results/ and delete stray history files BEFORE
  `git add -A`; amend; push. The 629/2 SPARQL reading is always the
  wrong-cwd artifact — rerun from the root before believing it.
- **Agents stall by ending turns to "wait for Monitor
  notifications."** This happened six-plus times today. The fix is
  mechanical: SendMessage the agent to resume with foreground
  bounded polling (sleep 20-30s loops, iteration cap); if the
  message merely queues, TaskStop then SendMessage. Watch for the
  silent variant: transcript mtime stale AND no compiler processes
  — that one needs the TaskStop route.
- **Verify agent claims about shared state.** One agent leaked its
  entire diff into the main checkout despite instructions (verify
  main is clean after every completion); another attributed test
  failures to the wrong cause (patch-62) when the real cause was a
  concurrent sibling build. When two agents share a checkout, their
  floor readings are unreliable — only the post-merge rebuild
  battery counts.
- **Use `git -C <abs-path>` for every git call during landings.**
  I corrupted my own cwd bookkeeping once today and started a
  cherry-pick in the wrong repo. Absolute paths cost nothing.
- **docs/ is 11ty-rendered.** Any `{{ ... }}` or `{% ... %}` in a
  committed markdown file (e.g. quoting GitHub Actions syntax)
  breaks the site build — wrap in raw tags. This broke the deploy
  once today; check `cd docs && npm run build` with a REAL exit
  code (`| tail` eats it) before pushing docs.
- **Cost discipline**: today's pattern — Fable coordinating,
  sonnet agents at 150k-450k tokens each executing — is the right
  shape. tools/session-cost.sh measures real spend including
  children.

## 6. Suggested sequencing for the next sessions

Near term (finish the started things first):
1. Land whatever of the three in-flight agents (SERVICE wrap 1-2,
   virtual RML stage 5, lazy buckets) didn't land before this
   session ended — their briefs and gates are in the transcript and
   reports; their worktrees may still exist under .claude/worktrees.
2. Hash join + estimate-driven BGP ordering. Measure with the
   competitive harness; the 1M join timeout is the acceptance test.
3. Delete the dead Bet7 term-dictionary glue paths (ratchet #118).
4. Wasm zstd shim (mirrors the stdint fix).

Medium term:
5. The SPARQL11.Algebra stratification split (unlocks KaRaMeL 107
   to ~123, the monomorphization fix, and makes RDF-star cheaper) —
   then the directory restructure via the store/hdt pilot
   (docs/designissues/2026-07-06-fstar-directory-structure.md is
   ratification-ready).
6. RDF-star design doc → implementation (the biggest standards gap).
7. Byte-buffer string/solution core (the structural perf unlock —
   do AFTER stratification, the blast radius needs the cleaner
   module graph).
8. Virtual sources stages 3-4 (MCP, exec-with-allowlist), fulltext
   scoring, GeoSPARQL phase 3.

Long term: HACL\* signatures + VC stage 2, HDT stage 5 rank/select
shared with the Roaring track, concurrency story, local-first
browser positioning (OPFS workers + service-worker endpoint — the
bytes store and IndexedDB work make this credible now).

## 7. Orientation pointers

- CLAUDE.md — the rules; its Skills index is the real manual.
- docs/claude-rules/current-state.md — scores + inventory, refreshed
  at landings.
- docs/designissues/ — every program has a dated design doc; the
  2026-07-06 crop covers durable UPDATE, unified store, bytes store,
  browser persistence, benchmarks, HDT, directory structure, virtual
  sources, KaRaMeL coverage.
- docs/web/perf/ — the runtime matrix. docs/web/hub/ — 18 live-cell
  posts; post 18 runs the durable log in the browser.
- The board: harness task list (#55 is the active goal); GitHub
  issues #118/#254 (glue), #282 (delta I/O), #283 (zstd writer),
  #284 (client https), #285 (pycottas test bootstrap).

One last judgement, for whoever picks this up: the discipline that
makes this project unusual — floors re-verified per landing, claims
labeled and dated, glue quarantined and counted, designs ratified
before implementation — is worth more than any single feature. The
owner built that culture deliberately. Inherit it before you
inherit the roadmap.
