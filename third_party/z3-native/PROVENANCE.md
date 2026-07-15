# Z3 native runtime pin (Z33kr Role 2 — runtime entailment oracle)

> **Status update 2026-07-15 — oracle RETIRED IN PRACTICE for the shipped
> corpus.** A verified F\* class-size linear-arithmetic reasoner
> (`Tableau.CountingOracle.class_size_unsat`, a Farkas-certificate
> validator with a build-checked soundness Lemma) now decides the
> counting-fragment systems inside the verified boundary and is consulted
> ONE RUNG BEFORE this oracle. The only two W3C tests the oracle ever
> flipped — WebOnt-description-logic-910 and one=two — now pass as plain
> VERIFIED passes (confirmed with `FACTOIDAL_OWL_Z3_RLIMIT=0`, i.e. z3
> never spawned). WebOnt-description-logic-909 the oracle never flipped
> (its class-size system is genuinely satisfiable — z3 answers `sat`), and
> still does not flip: deriving `|finite| >= 1` would need an unsound
> nonemptiness rule, which is deliberately NOT added. So for the shipped
> OWL corpus the oracle is now unreachable — no test reaches
> `z3_oracle_refutes` with a flippable input. The code path is KEPT (not
> deleted) for future counting fixtures outside what the verified reasoner
> decides; this pin stays valid until such a fixture appears or the
> reasoner subsumes it. See
> [`docs/designissues/2026-07-15-owl2-wave-c-finite-model-refutation.md`](../../docs/designissues/2026-07-15-owl2-wave-c-finite-model-refutation.md)
> § forward path and issue #296.

| Field | Value |
|---|---|
| Component | z3 (native), used as the **runtime** satisfiability oracle behind the OWL 2 DL consistency interface |
| Version | **4.13.3** |
| Licence | MIT (Z3Prover/z3) |
| Source | Z3Prover/z3 release; the binary already pinned for the F* verification toolchain is reused as the initial runtime pin |
| Trust model | Runtime oracle on **user data**. Its verdicts are labelled **oracle-assisted** and never folded into the pure-verified score. Consulted only in the tableau's non-refuting branch, only inside `Tableau.CountingOracle.in_counting_fragment`, only for InconsistencyTests. |

## Two deliberately separate z3 pins (design doc Q6)

This project pins z3 **twice, on purpose** — see
[`docs/designissues/2026-07-14-z3-entailment-backend.md`](../../docs/designissues/2026-07-14-z3-entailment-backend.md)
§ "Two unrelated z3 roles" and Q6.

- **Role 1 — build-time F\* verification backend.** `fstar.exe` discharges
  proof obligations through z3 4.13.3 (`formal/fstar/Makefile`, iron rule
  #10). This z3 sees F\* SMT queries, never user RDF. It is toolchain
  infrastructure and is NOT a runtime dependency.
- **Role 2 — runtime entailment oracle (THIS pin).** The z3 invoked at
  query/validation time on the user's ontology, via the
  `Tableau.CountingOracle.z3_check_sat` ASSUME-HOST realisation
  (`minimal_regrettable_glue_code_each_with_an_open_issue/296_z3_check_sat.sh`).

**Initial runtime pin: the Role-1 4.13.3 binary is reused** (lowest
friction — it is already on the machine). Even though the *same bytes*
currently serve both roles, this runtime pin is recorded and MUST be
bumped **independently** of the toolchain pin, because:

1. SMT-LIB 2 input is version-stable — runtime behaviour need not track
   the prover version F\* happens to use.
2. A future verification-toolchain z3 bump must not silently change
   *runtime* verdicts.
3. The wasm runtime (design doc Phase 3, not yet landed) uses the
   `z3-solver` npm build, a different version (4.16.0) — so the native
   and wasm runtime pins are already distinct; there is no single "z3".

## Binary resolution at runtime

The `z3_check_sat` realisation spawns `z3` from `PATH` by default, or the
binary named by the `FACTOIDAL_Z3_BIN` environment variable. No z3 binary
is vendored into this directory yet (the toolchain binary is reused); when
the runtime pin diverges from the toolchain pin, drop the pinned binary
here and point `FACTOIDAL_Z3_BIN` at it. No editing of the vendored
artifact; deviations would be recorded in `LOCAL_PATCHES.md` per the
third-party policy.
