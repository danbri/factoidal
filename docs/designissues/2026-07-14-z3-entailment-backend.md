# 2026-07-14 — Z3 as a runtime reasoning backend behind the entailment interfaces

Date: 2026-07-14. Status: PLAN (decision-ready design; no `.fst`,
`.ml`, or build edits in this branch). Owner question (paraphrased):
"consider whether z3 can be wired up behind OWL, RIF or SPARQL
entailment interfaces. Potentially ported to wasm too?"

This is a design decision, not an implementation. It answers seven
questions and hands a phased plan with per-phase test-flip estimates
and a go/no-go gate on each phase.

## Two unrelated z3 roles — read this first

z3 already exists in this repo, in a role this document does **not**
touch. Do not conflate them.

- **Role 1 — build-time F\* verification backend (existing, unchanged).**
  `fstar.exe` discharges its proof obligations through z3 at
  *compile/verify* time (`formal/fstar/Makefile:1`,
  `fstar.exe --z3version 4.13.3`, iron rule #10). This z3 sees F\* SMT
  queries, never user RDF, and never runs when the extracted engine
  answers a query. It is toolchain infrastructure. Nothing here changes
  it.

- **Role 2 — runtime entailment oracle (new, THIS DOCUMENT).** A z3
  invoked at *query/validation time* on **user data**: at the moment a
  consistency or entailment question is asked, an F\*-written encoder
  turns the user's axioms + question into an SMT-LIB 2 string, a z3
  instance returns `sat`/`unsat`/`unknown`, and that verdict feeds the
  entailment answer the engine hands back. This is a live reasoning
  engine behind the OWL/RIF/SPARQL entailment interfaces — a use z3 has
  never had in this codebase.

These share only a vendored solver artifact. They are **not** the same
integration, the same trust story, the same data path, or the same
lifecycle. Framing role 2 as "extending the toolchain" would be wrong:
role 1 is about proving *our F\* code* correct; role 2 is about
answering *the user's ontology* at runtime with a component we do
**not** prove correct. Every section below is about role 2 only. The
sole permitted crossover is one pragmatic vendoring note (Q6: can the
already-pinned 4.13.3 binary double as the runtime solver, or is a
separate runtime pin cleaner) — and that note exists precisely to keep
the two roles from silently coupling.

## TL;DR recommendation

- Wire z3 behind the **OWL DL consistency** interface only, and only
  for the **finite-model counting fragment** the verified tableau
  provably cannot decide (dl-909/910 + one=two: pigeonhole with
  cardinality multiplication). Encode that fragment into SMT-LIB 2
  with a **verified F\* function** (`ontology_ast -> Tot smtlib`); the
  single unverified seam is one `assume val z3_check_sat` — a
  host-engine call-out in exactly the sense regex already is
  (`ocaml-boundary` skill, `ASSUME-HOST`).
- z3 is consulted **only in the branch where the tableau already
  returned `None` (indeterminate)**, mirroring the existing
  `dl_refutes` contract in `bin/owl-runner/owl_runner.ml:628`. It can
  strengthen a verdict toward "inconsistent"; it can never lower a
  score below the current verified baseline, and a z3 timeout returns
  the same fallback verdict the runner produces today.
- Because a z3-derived pass is **not verified**, any test it flips is
  reported in a separate **oracle-assisted** column with the
  pure-verified score kept alongside — the honesty requirement that
  W3C scores never silently depend on an unverified component.
- **Do not** put z3 behind SPARQL entailment regimes (that suite is
  already 70 pass, 0 fail via the verified anchor rewrite — adding an
  oracle would only demote a fully-verified score) or behind RIF (RIF
  Core is a Horn/fixpoint evaluator, not a satisfiability problem — SMT
  is the wrong tool). These are non-goals.
- **wasm is a later phase, gated**, not part of the first landing: the
  default `z3-solver` wasm build needs pthreads + `SharedArrayBuffer` +
  COOP/COEP cross-origin isolation and runs z3 in an Emscripten worker
  (async), which breaks the synchronous-after-init property the HACL\*
  wasm precedent relies on. Native-first; wasm only after the
  async/threads question is resolved.

## 1. Where entailment lives today (ground truth in the tree)

The project already has a layered OWL entailment stack, all verified
F\* extracted to OCaml, with the runner doing dispatch/fallback
plumbing only:

- **OWL-RL Datalog closure** — `RDF.Graph.Executable`
  (`owl_rl_closure_step`, `entailment_closure` dispatch, `is_inconsistent`
  marker scan). Forward-chaining; the RL regime baseline.
- **Positive tableau materialisation** — `Tableau.fst`
  (`tableau_materialise`, `owl_tableau_entails`). Positive-sound only:
  emits entailed `i rdf:type CE` triples for conclusion matching, never
  detects unsatisfiability.
- **Clash-detecting refutation tableau** — `Tableau.Refute.fst`
  (`tableau_consistent : rdf_graph -> fuel:nat -> Tot (option bool)`).
  `Some false` = refuted (inconsistent, with a per-rule model-theoretic
  soundness argument); `Some true` = expanded with no clash (NOT a
  completeness proof — treated as "not inconsistent"); `None` =
  fuel/budget exhausted. ~3000 lines, zero admits/assumes/`--lax`.
  Implements NNF, lazy TBox unfolding, budgeted disjunction branching,
  depth-capped existential witnesses, the SHIQ ≤-rule with witness
  merging and named-individual identification, role box
  (subPropertyOf / FunctionalProperty / TransitiveProperty),
  differentFrom-backed counting clashes.
- **RIF Core** — `RIF.Core.{Syntax,Translation,Eval,Builtins,Conformance}`.
  A Horn-rule dialect evaluated by fixpoint, plus a structural
  conformance/safeness checker. Not a satisfiability problem.

Runner integration (`bin/owl-runner/owl_runner.ml`):

```ocaml
// dl_refutes: consult the F*-extracted refuter over the RL-closed
// graph. `true` ONLY on `Some false`. Runs under its own (short)
// SIGALRM cap; cap-trip or fuel-out falls back to `false`, i.e. the
// pre-existing RL `is_inconsistent` verdict. The DL result can never
// score below the RL baseline. Dispatch/fallback plumbing only.
let dl_refutes closure =
  match !regime with
  | Regime_RL -> false
  | Regime_DL ->
    (try with_refute_cap (fun () ->
       match Tableau_Refute.tableau_consistent closure refute_fuel with
       | Some false -> true | _ -> false)
     with _ -> false)
```

**This is the template.** A z3 backend is a second consultation with
the identical monotonicity contract, invoked one rung further out:
only when `tableau_consistent` returns `None`.

### Current measured scores (2026-07-14, `docs/test-results/latest.csv`)

- SPARQL entailment regime suite: **70 pass, 0 fail (out of 70)**.
- OWL 2 DL type-inconsistency: **110 pass, 18 fail (out of 128)**.
- OWL 2 DL type-consistency: **334 pass, 18 fail (out of 352)**.
- RIF core corpus: **42 pass, 1 fail, 3 skip (out of 46)**;
  rif-sparql-manifest **4 pass, 0 fail**.
- Floors: SPARQL **631 pass, 0 fail**; RDF **1031 pass, 0 fail**.
- Soundness gate: **exactly one** `unexpected-inconsistency`
  (WebOnt-miscellaneous-202, pre-existing, #236).

The residual tinc fails include dl-909/910 + one=two, classified as
**finite-model cardinality arithmetic** (`docs/claude-rules/current-state.md`,
`docs/designissues/2026-07-10-owl2-dl-completion-program.md` §3): a
max-cardinality bound forces fillers into fewer distinct individuals
than a min-cardinality demands, and detecting the contradiction needs
pigeonhole reasoning *with multiplication* over a finite domain. The
tableau's ≤-rule merges witnesses pairwise under budget but does not
solve the arithmetic; z3 does exactly this in microseconds.

## 2. Design question answers

### Q1 — Trust boundary

**Options considered:** (a) z3 as oracle (accept verdicts, label them);
(b) z3 as pre-filter/hint (z3 flags inconsistent, tableau must confirm —
no soundness cost, but no win on the tests the tableau already can't
confirm); (c) proof replay (parse z3 unsat cores/proofs, re-check in
F\* — highest assurance, highest cost).

**Recommendation, per interface:**

- **OWL DL consistency (finite-model counting fragment): (a) oracle,
  explicitly labelled.** Option (b) is self-defeating here: the whole
  reason to reach for z3 is that the tableau *cannot* confirm the
  counting contradiction (dl-909/910), so "tableau must confirm" leaves
  the tests failing. Option (c) is attractive in principle but collapses
  in this specific fragment: the z3 unsat core for a pigeonhole-counting
  case is a handful of linear-integer facts, and an F\* checker able to
  replay them is an F\* checker able to *decide* the fragment — at which
  point we should do the reasoning in F\* and not call z3 at all. So (c)
  is not a middle path here; it is either "trust z3" (a) or "finish the
  F\* finite-model reasoner" (no z3). We recommend (a) now, with the F\*
  reasoner as the eventual retirement path (same lifecycle as every
  `assume val`: a z3 backend is an acknowledged, tracked gap, not a
  permanent dependency).

  The oracle is contained: it is consulted only in the tableau's `None`
  branch, only for InconsistencyTests, and only strengthens toward
  "inconsistent". A z3 `Unsat` that contradicts an expected-consistent
  test is a **soundness-gate failure** (the `unexpected-inconsistency`
  count must stay at exactly one) and breaks the build — so a mis-encoding
  cannot silently corrupt the consistency side.

- **SPARQL entailment regimes: (b) at most — in practice, none.** The
  regime suite is already 70/0 via the verified `OWL.QueryRewrite`
  anchor rewrite. Introducing an oracle into a fully-verified green
  suite trades verified assurance for nothing. If a future regime
  fixture needs finite-model counting, it inherits the OWL-DL-consistency
  backend transitively (the regime check runs over the same closure);
  no separate SPARQL wiring.

- **RIF: none.** RIF Core is Horn/fixpoint; SMT satisfiability is a
  category mismatch. Non-goal (see Q3, Q7).

**Honesty requirement.** Any test a z3 verdict flips is reported in a
dedicated **oracle-assisted** column, with the pure-verified score
retained in the same table and a footnote naming z3 + its pinned
version. The dashboard already distinguishes RL vs DL; this adds a
third, clearly-unverified tier. The project's public qualifier already
carries "on-disk backend has unverified OCaml-side optimization
layers"; a z3-assisted OWL-DL row is disclosed the same way.

### Q2 — Interface shape

The verified/unverified split is drawn exactly where rule #11 draws it.

**Verified in F\* (Tot, deterministic):**

```fstar
// Verdict is a closed sum; no z3 internals leak into F*.
type z3_verdict = | Z3_Sat | Z3_Unsat | Z3_Unknown | Z3_Timeout

// Encode ONE fragment: finite-model cardinality counting over a
// finite domain (SHIQ-with-cardinalities restricted to the counting
// core). Pure integer arithmetic in SMT-LIB 2 -- for each individual
// and role, an Int successor-count per relevant filler class, with
// >= / <= bounds from min/max(Qualified)Cardinality axioms and a
// distinctness budget from differentFrom. Unsat iff no assignment
// exists, i.e. the individual is unsatisfiable => graph inconsistent.
val encode_counting_fragment : ontology_ast -> Tot smtlib_string

// A conservative recogniser: does this closure fall inside the
// fragment `encode_counting_fragment` is complete for? Returns false
// (=> never call z3) on anything outside it, so the oracle is only
// ever consulted where the encoding is known-faithful.
val in_counting_fragment : rdf_graph -> Tot bool
```

**The single `assume val` (host-engine call-out, `ASSUME-HOST`):**

```fstar
// Host satisfiability oracle. Semantics are z3's, exactly as
// regex_match's semantics are the host regex engine's -- moving z3
// into F* would be as wrong as reverifying the regex engine. The
// `rlimit` bounds work DETERMINISTICALLY (see Q4 parity) rather than
// by wall-clock, so the same input yields the same verdict on native
// and wasm.
assume val z3_check_sat : smtlib:string -> rlimit:nat -> Tot z3_verdict
```

**Glue (realises the `assume val` only, no semantics):**
- Native: spawn the pinned `z3` binary with `-in`, feed the SMT-LIB
  string on stdin, parse `sat`/`unsat`/`unknown` from stdout. A
  process spawn is pure host I/O (`ASSUME-IO`) around a host decision
  (`ASSUME-HOST`) — the boundary-clean forms rule #11 already permits.
- wasm/js: call the `z3-solver` API (Q4).

The encoding function is where all the semantic content lives, and it
is verified. Start with the counting fragment — small, total, decidable
by linear integer arithmetic — **not** a general OWL-DL-to-SMT
translation (which would drag the entire DL score into oracle-land and
is an explicit non-goal, Q7).

### Q3 — Which interface first

Ordering, by expected verified-baseline test flips:

1. **OWL DL consistency, counting fragment (Phase 1–2).** Directly
   targets dl-909/910 + one=two. Expected immediate flip: **+3**
   (dl-909, dl-910, one=two) into the oracle-assisted column. A sweep of
   the remaining 18 tinc fails at fragment-recognition time will show
   how many more are pure-counting (candidates among the "finite-model
   cardinality arithmetic" family) — estimate **+3 to +6** total, to be
   measured, not asserted, in Phase 2's gate.
2. **SPARQL entailment regimes — skip.** 70/0 already; no flips
   available, and an oracle would demote assurance. Revisit only if a
   new W3C regime fixture is imported that needs counting (inherits the
   OWL backend for free).
3. **RIF — non-goal.** RIF Core (42/1/3) is a fixpoint evaluator; its
   one fail + three skips are safeness/import-rejection and vocabulary-
   separation cases (`RIF.Core.Conformance`), not satisfiability. z3
   flips zero RIF tests. Do not wire it.

So the entire value is in stage 1. Stages 2 and 3 are documented here
to record that they were considered and rejected, per the owner's
question naming all three.

### Q4 — wasm

**Facts (verified 2026-07-14, re-check at pin time):**
- z3 ships an official wasm build via the **`z3-solver` npm package**,
  current version **4.16.0, MIT**, compiled with Emscripten. Files:
  `z3-built.js`, `z3-built.wasm`, `z3-built.worker.js`.
- The default build **requires pthreads and therefore
  `SharedArrayBuffer`**, which in a browser needs cross-origin
  isolation (`Cross-Origin-Opener-Policy: same-origin` +
  `Cross-Origin-Embedder-Policy: require-corp`). It runs z3 in an
  Emscripten **worker** — the API is **async**.
- Load is slow (~15 s Chrome, <1 s Firefox in the maintainers'
  measurements); solve time is within ~2–5x native.
- The wasm artifact is on the order of tens of MB uncompressed —
  materially larger than the HACL\* wasm closure (~520 KB). The exact
  current figure must be measured at pin time and recorded in the
  provenance table (do not quote a stale number in public prose).
- Single-threaded z3 wasm builds exist (e.g. `cpitclaudel/z3.wasm`,
  `bramvdbogaerde/z3-wasm`, or z3 built with threads disabled), which
  drop the `SharedArrayBuffer`/COOP-COEP requirement at some
  performance cost.

**How the `assume val` glue reaches z3 wasm from the jsoo bundle —
mirroring the HACL\* precedent** (`node-crypto-haclstar-vc-wasm-build`
skill): an `initZ3()` loader loads the wasm module once (async) and
stashes the ready API object on `globalThis.__factoidalZ3`; the
`z3_check_sat` realisation reads that object. Same **throw-on-uninit
safety contract** as `caml_hacl_backend()`: if the backend is not
initialised, the primitive **throws** — it never returns a fabricated
`Z3_Unsat`. A fabricated `Unsat` is a soundness hole exactly as a
fabricated `verify=true` is; the wasm crypto seam already established
this pattern and it transfers verbatim.

**Where the wasm story diverges from HACL\* (the load-bearing wrinkle):**
HACL\* runs **synchronously after init** — no `await` on the hot path,
so the `assume val` realisation is a plain synchronous call. z3's
default wasm build runs in a **worker and is async**. That breaks the
"sync after init" property. Two resolutions:
  - (i) Make the OWL-consistency npm API **async** (returns a Promise;
    `await fn.owlIsConsistent(...)`). Clean, but the F\*-extracted call
    site (`z3_check_sat`) is typed `Tot` (synchronous) — the async hop
    must be handled entirely inside the glue, e.g. by making the
    *consumer* wrapper async and only calling into F\* once the z3
    answer is already resolved and memoised. This needs the
    consistency check restructured so z3 is consulted out-of-band and
    its verdict passed *in*, rather than F\* calling out mid-computation.
  - (ii) Use a **single-threaded** z3 wasm build and a synchronous-over-
    worker shim (`Atomics.wait` on a `SharedArrayBuffer`) — which
    reintroduces the COOP/COEP requirement. Not recommended for the
    browser demo (header constraints on the static host); acceptable
    under Node.

Recommendation: **native backend first**; wasm behind a gate that
resolves (i) vs (ii). If wasm ships, prefer (i) with a single-threaded
build so no COOP/COEP headers are needed, accepting that
`fn.owlIsConsistent` is async — acceptable for a *new* API surface (the
existing bundle is unaffected).

**Determinism / cross-runtime parity** (`test-suites` skill, parity
section): native z3 and wasm z3 are different builds and versions, so
`Sat`/`Unsat` must agree (both are decision procedures for the
counting fragment) but resource-limit boundaries differ (wasm is
2–5x slower). Policy:
  - Bound work with z3's **`rlimit`** (a deterministic instruction-count
    budget), **not** wall-clock. `Unknown`/`Timeout` then becomes a
    deterministic function of the query, identical across runtimes.
  - On **any** `Unknown`/`Timeout`, both runtimes fall back to the
    tableau verdict identically (Q5) — so cross-runtime parity holds
    regardless of z3's answer: the fallback is the same verified value
    on both.
  - Parity tests assert native and wasm produce the **same reported
    verdict** on the counting-fragment fixtures; because both defer to
    the same tableau on indeterminate and both trust the same `Unsat`
    on decided cases, parity is structurally guaranteed, not merely
    hoped for.

### Q5 — Fallback + budget semantics

z3 is consulted **after** the tableau, only in its `None` (indeterminate)
branch:

```
RL closure  --(is_inconsistent)-->  RL verdict          // never regresses
   |  (DL regime)
tableau_consistent
   |-- Some false  -> inconsistent (verified)            // best case
   |-- Some true   -> not inconsistent (treated as None-for-scoring)
   |-- None        -> in_counting_fragment closure ?
                        yes -> z3_check_sat (rlimit)
                                 |-- Z3_Unsat            -> inconsistent (ORACLE)
                                 |-- Z3_Sat / Unknown /
                                     Timeout             -> fall back to
                                                            tableau/RL verdict
                        no  -> fall back to tableau/RL verdict
```

Properties (the `dl_refutes` monotonicity contract, one rung out):
- z3 can only add "inconsistent" verdicts; it never removes one. A z3
  timeout returns **exactly** the verdict the runner produces today, so
  **no previously-passing test can flake** — the pre-z3 outcome is the
  z3-timeout fallback outcome, deterministically.
- z3 runs **only** on closures the verified path already gave up on
  (`None`) *and* that `in_counting_fragment` recognises — so it never
  touches the common path and never slows a test the tableau decided.

**Budget composition.** `FACTOIDAL_OWL_CAP_SEC` (currently 30 s default,
`owl_runner.ml:521`) caps the whole per-test closure+check. z3 gets a
**sub-budget carved from what remains** after the tableau returns:
a new `FACTOIDAL_OWL_Z3_RLIMIT` (deterministic, primary bound) plus a
`FACTOIDAL_OWL_Z3_CAP_SEC` SIGALRM wall-clock backstop (smaller than
the refuter cap, e.g. 3 s) so a pathological z3 spawn can never exceed
the parent cap. The rlimit is the parity-relevant bound; the wall-clock
cap is only a safety backstop and a wall-clock trip falls back
identically to an rlimit `Unknown`. Same `with_*_cap` SIGALRM
machinery already in the runner — plumbing only, no new semantics.

### Q6 — Vendoring / licence

z3 is **MIT** — compatible, no copyleft concern.

**Version pins — two, deliberately separate (the one permitted
role-1/role-2 crossover note):**
- **Role 1**, the F\* **verification** toolchain, pins z3 **4.13.3**
  (`formal/fstar/Makefile:1`, iron rule #10) for proof reproducibility.
- **Role 2**, the **runtime** entailment oracle, takes an **independent
  pin**. Reusing the role-1 4.13.3 binary as the runtime solver is
  possible and is the lowest-friction starting choice (it is already on
  the machine), but even when the *same bytes* serve both, the runtime
  pin must be recorded and bumped *separately* from the toolchain pin,
  for three reasons: (a) SMT-LIB 2 input is version-stable, so runtime
  behaviour need not track the prover version F\* happens to use; (b) a
  future verification-toolchain z3 bump must not silently change
  *runtime* verdicts; (c) wasm needs the `z3-solver` npm build anyway,
  which is a different version (4.16.0) — the native and wasm runtime
  pins are already distinct, so pretending there is "one z3" is
  fiction. Document both runtime pins in the provenance table.

**Vendoring layout** (mirrors the HACL\* wasm precedent and the
`formal/third_party/` policy in `2026-05-07-io-verification-and-third-party.md`):

```
third_party/z3-native/     -- runtime native pin (or a note that the
  VERSION                     toolchain 4.13.3 binary is reused)
  LICENSE                     -- z3 MIT
  PROVENANCE.md
third_party/z3-wasm/       -- z3-solver wasm closure (when wasm lands)
  VERSION                     -- z3-solver 4.16.0 (or single-threaded build)
  LICENSE
  PROVENANCE.md               -- upstream commit + Emscripten version
  INFO.txt                    -- threaded vs single-threaded, artifact size
npm/factoidal/z3-wasm/     -- mirror, so the npm package is self-contained
```

**Provenance table (to fill at pin time):**

| Artifact | Version | Licence | Source | Size | Trust model |
|---|---|---|---|---|---|
| **Role 2** native z3 (runtime) | 4.13.3 (initial; reuse role-1 binary) or independent pin | MIT | Z3Prover/z3 release | n/a | runtime oracle on user data; verdicts labelled oracle-assisted |
| **Role 2** z3-solver (wasm) | 4.16.0 (or single-threaded build) | MIT | npm `z3-solver` / Emscripten | tens of MB (measure) | runtime oracle on user data; same |
| **Role 1** F\* toolchain z3 | 4.13.3 | MIT | pinned per iron rule #10 | n/a | build-time F\* verification only; NOT a runtime dependency; listed only to keep the two roles distinct |

No editing of vendored artifacts; deviations recorded in
`LOCAL_PATCHES.md` per the third-party policy.

### Q7 — Risks + non-goals

**Non-goals (what this does NOT replace):**
- The verified tableau (`Tableau.Refute.fst`) stays the **default and
  only verified** consistency path. z3 is **additive**, for one fragment
  the tableau provably lacks. If the F\* finite-model reasoner is later
  completed, z3 retires (tracked like any `assume val` gap, iron rule #3).
- **No general OWL-DL-to-SMT translation.** Encoding all of DL into SMT
  would make the *entire* DL score oracle-dependent and discard the
  verified refuter's assurance. Explicitly rejected. Only the counting
  fragment is encoded, guarded by `in_counting_fragment`.
- **No SPARQL query evaluation via z3**, no RIF via z3.

**Risks + mitigations:**
- *Oracle dependence creeping into headline scores.* Mitigation: the
  oracle-assisted column + retained pure-verified score + z3 consulted
  only in the `None` branch. The verified number never drops.
- *Encoding bug producing an unsound `Unsat`.* Mitigation:
  `encode_counting_fragment` is a verified `Tot` F\* function with a
  soundness obligation (its `Unsat` implies inconsistency under Direct
  Semantics for inputs `in_counting_fragment` accepts); plus the
  build-breaking `unexpected-inconsistency` gate catches any consistent
  test wrongly flipped. We cannot verify z3 itself — that is the
  acknowledged oracle boundary, disclosed.
- *z3 as a large unverified binary in the trusted base.* Mitigation:
  consulted only for a decidable linear-integer fragment, only in the
  indeterminate branch; the soundness gate bounds the blast radius.
- *wasm weight + threads/COOP-COEP + async + slow init.* Mitigation:
  wasm is a gated later phase, single-threaded build preferred, async
  API accepted for the new surface; native ships first and carries all
  the test-flip value.
- *Determinism drift native vs wasm.* Mitigation: deterministic
  `rlimit` bound + identical fallback on `Unknown`/`Timeout` (Q4).

## 3. Phased plan (per-phase flips + go/no-go gate)

Each phase is one commit-sized deliverable. Scores labelled per
anti-pattern #25. Floors that must hold every phase: SPARQL 631/0,
RDF 1031/0, RIF 42/1/3, SPARQL-entailment 70/0, and **exactly one**
`unexpected-inconsistency`.

### Phase 0 — encoding spec + fragment recogniser (F\* only, no z3)

Write `encode_counting_fragment` and `in_counting_fragment` in F\*,
plus the `z3_verdict` type and the `assume val z3_check_sat` stub
(with its rule-#3 patch skeleton + open issue). No glue yet;
`z3_check_sat` returns `Z3_Unknown` (throw-on-uninit) so the whole
pipeline compiles and behaves exactly as today.
- **Flips:** 0 (behaviour identical; `in_counting_fragment` measured
  against the 18 tinc fails to size the real prize).
- **Go/no-go gate:** F\* verifies clean (no `--lax`, no admits); all
  current scores unchanged to the test; the fragment-recogniser sweep
  reports how many of the 18 tinc fails it accepts (the honest upper
  bound on Phase 2's flips).

### Phase 1 — native glue + oracle wiring

Realise `z3_check_sat` by spawning the pinned native z3 (stdin SMT-LIB,
parse verdict). Wire it into the runner's `None` branch behind
`in_counting_fragment`, under `FACTOIDAL_OWL_Z3_RLIMIT` +
`FACTOIDAL_OWL_Z3_CAP_SEC`. Add the oracle-assisted reporting column.
- **Flips:** **+3** expected (dl-909, dl-910, one=two) into the
  oracle-assisted column.
- **Go/no-go gate:** the three named tests flip to pass *in the
  oracle-assisted column*; pure-verified score unchanged; soundness
  gate still exactly one `unexpected-inconsistency`; a run with the z3
  binary absent (or `rlimit`=0) reproduces today's exact scores
  (proves the fallback is transparent). If the soundness gate trips,
  **stop** — a consistent test was wrongly refuted; fix the encoding
  before proceeding.

### Phase 2 — fragment sweep + measured additional flips

Extend/confirm `in_counting_fragment` coverage across the remaining
tinc fails; measure and land whatever additional pure-counting tests
flip.
- **Flips:** measured, estimate **+0 to +3** beyond Phase 1.
- **Go/no-go gate:** named fail-set diff (not just counts); no floor
  regression; soundness gate holds. Any test that needs reasoning
  *outside* the counting fragment is left failing and documented as
  out-of-fragment (candidate for the F\* reasoner, not z3).

### Phase 3 — wasm backend (gated, optional)

Only if the async/threads resolution (Q4) is settled. Vendor the
`z3-solver` (or single-threaded) wasm closure with provenance; add the
`initZ3()` loader + throw-on-uninit realisation; expose an **async**
`fn.owlIsConsistent`. Parity-test native vs wasm on the counting
fixtures with a deterministic `rlimit`.
- **Flips:** 0 new (same verdicts as native); value is off-native reach.
- **Go/no-go gate:** parity tests green (native == wasm reported
  verdict on every counting fixture); COOP/COEP requirement eliminated
  (single-threaded build) or explicitly accepted for Node-only; bundle
  rebuilt with npm-entry forced and `tests/hub` still green
  (anti-pattern #28); artifact size recorded in the provenance table.
  If parity or the header constraint fails, **hold** — native remains
  the shipped backend and carries all the value.

## 4. Boundary-rule compliance summary

- The only `assume val` is `z3_check_sat` — an `ASSUME-HOST`
  host-engine call-out (satisfiability is z3's semantics, not ours),
  the same category the `ocaml-boundary` taxonomy already sanctions for
  regex. Rule #3 patch + open issue accompany it.
- All semantic content (the SMT-LIB encoding, the fragment recogniser,
  the verdict handling) is verified `Tot` F\*. No semantics in glue;
  process spawn / wasm API call is pure I/O around the host decision.
- Native binaries committed per iron rule #9; runtime z3 pinned
  separately from the verification toolchain (Q6).
- No `--lax`, no admits (iron rule #10) — the encoding and recogniser
  verify like the rest of the tree.

## 5. References

- Runner refuter integration + fallback: `bin/owl-runner/owl_runner.ml`
  (`dl_refutes` ~628, `FACTOIDAL_OWL_CAP_SEC` ~521, `with_refute_cap` ~603).
- Refutation tableau: `formal/fstar/Tableau.Refute.fst`
  (`tableau_consistent`, ≤-rule + named-merge banners).
- Positive tableau + RL closure: `formal/fstar/Tableau.fst`,
  `formal/fstar/RDF.Graph.Executable.fst`.
- RIF Core: `formal/fstar/RIF.Core.{Syntax,Eval,Translation,Conformance}.fst`.
- Finite-model counting fail family + wave plan:
  `docs/designissues/2026-07-10-owl2-dl-completion-program.md` §3,
  `docs/claude-rules/current-state.md`.
- OCaml boundary / `assume val` taxonomy (`ASSUME-HOST`):
  `skills/ocaml-boundary/SKILL.md`.
- Third-party vendoring policy + host-primitive precedent (regex):
  `docs/designissues/2026-05-07-io-verification-and-third-party.md`.
- wasm-vendoring precedent (throw-on-uninit, `initHacl`, provenance):
  `skills/node-crypto-haclstar-vc-wasm-build/SKILL.md`,
  `skills/crypto-policy/SKILL.md`.
- z3-solver npm (4.16.0, MIT, Emscripten wasm, threads/SharedArrayBuffer):
  <https://www.npmjs.com/package/z3-solver>,
  <https://github.com/Z3Prover/z3/discussions/6551>.
- Single-threaded z3 wasm builds:
  <https://github.com/cpitclaudel/z3.wasm>,
  <https://github.com/bramvdbogaerde/z3-wasm>.
