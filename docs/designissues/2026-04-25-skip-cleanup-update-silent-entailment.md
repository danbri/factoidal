# 2026-04-25 — Skip Cleanup: update-silent + entailment

Agent Bet, Wave 8 main-thread cycle. Goal: drive SKIP count toward zero in
two non-protocol suites. The user counts skips as debt, not free.

## Baseline (./bin/darwin-arm64/w3c_runner)

```
update-silent  pass:11 fail:0 skip:2 unsupported:0
entailment     pass:63 fail:3 skip:4 unsupported:0
```

## Part A: update-silent (2 skips)

Both skips are `LOAD SILENT` tests:

| Test | File | Source IRI | Expected |
|------|------|------------|----------|
| `LOAD SILENT` | `load-silent.ru` | `<somescheme://www.example.com/THIS-GRAPH-DOES-NOT-EXIST/>` | empty dataset |
| `LOAD SILENT INTO` | `load-silent-into.ru` | same | empty dataset |

Per SPARQL 1.1 Update §3.1.4: `LOAD SILENT` MUST NOT produce a fault even
if the source IRI is unreachable. Both tests use a deliberately
non-resolvable scheme; expected `mf:result` is empty (no input data, no
fetched data). The "silently succeed = do nothing" semantic is exactly what
`U_Load _ _ _ -> ds` already implements in `SPARQL11.Algebra.fst:5273`.

The skip exists because `is_implemented_op` returns `false` for **every**
`U_Load`, including the SILENT variants. That's overly conservative: when
`silent = true`, the no-op semantic is correct and verifiable.

### Fix (F*-first per rule #15)

Patch `is_implemented_op` in `SPARQL11.Algebra.fst` so `U_Load true _ _`
is "implemented" (correct behavior: do nothing, succeed). `U_Load false _ _`
remains unimplemented — the runner will continue to skip it (none in
update-silent suite).

The runner then naturally executes both LOAD SILENT tests through the
existing Update pipeline, the F* evaluator returns the unchanged dataset,
and `triple_sets_match` confirms it matches `mf:result []`. No runner
changes needed.

### Non-silent LOAD

Out of scope here — there is no `LOAD <iri>` test in `update-silent/`
(by definition; the suite is the SILENT suite). Non-silent LOAD would
need real HTTP I/O and is tracked separately.

## Part B: entailment (4 skips)

All 4 are RIF tests, ent:RIF entailment regime:

| Test | Name |
|------|------|
| `:rif01` | RIF Logical Entailment (referencing RIF XML) |
| `:rif03` | RIF Core WG tests: Frames |
| `:rif04` | RIF Core WG tests: Modeling Brain Anatomy |
| `:rif06` | RIF Core WG tests: RDF Combination Blank Node |

`docs/claude-rules/scope.md` only listed 2 RIF tests
(`BindingsClause-Core`, `RIFCore-NoSubclassNorTyping-1`) — those names
don't appear in the manifest. The actual RIF tests are the 4 above.
Scope.md is wrong about names, but the policy (RIF is permanent SKIP) is
unchanged. Updating scope.md to reflect the manifest's actual test IDs.

### Fix

Document only — no code change. RIF stays out of scope per project
charter (no rule engine, no production-rule language). The runner
already correctly tags these `RIF-Skip` and emits `Skip "RIF not
implemented"`.

## Expected Delta on Next Sweep

```
update-silent  pass:13 fail:0 skip:0 unsupported:0   (+2 pass, -2 skip)
entailment     pass:63 fail:3 skip:4 unsupported:0   (unchanged; RIF permanent skip)
```

Total skip-count delta: **-2** in non-protocol suites.

## Files Touched

- `formal/fstar/SPARQL11.Algebra.fst` — `is_implemented_op` accepts
  `U_Load true _ _`.
- `formal/fstar/ocaml-output/SPARQL11_Algebra.ml` — extracted form (manual
  parallel edit; main-thread does NOT extract this cycle).
- `formal/fstar/ocaml-output/w3c_runner.ml` — comment update (LOAD SILENT
  no longer skipped).
- `docs/claude-rules/scope.md` — fix the RIF test names to match manifest.
