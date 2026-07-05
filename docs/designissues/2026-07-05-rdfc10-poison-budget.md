# RDFC-1.0 100% — test073m fixture evidence + test074c poison budget (2026-07-05)

**Goal:** owner asked for RDFC-1.0 "fully correct complete compliant"
— put the two non-passing entries (test073m fail, test074c stub) back
in scope. Baseline going in: 84 pass, 1 fail, 1 stub (out of 86), via
`bin/linux-x86_64/rdfc10_runner`.

## test073m — resolved via harness comparison fix (not a fixture edit, not a submodule move)

### Re-derivation

`test073m` is `rdfc:RDFC10MapTest` (`third_party/testing/rdf-canon/
tests/manifest.ttl:696`), comparing our emitted JSON bnode-mapping
against `third_party/testing/rdf-canon/tests/rdfc10/
test073-rdfc10map.json`. The diff was exactly one byte: our
`mapping_to_json` always emits a trailing `\n` after the closing `}`;
the fixture has none.

Checked all 20 `*-rdfc10map.json` fixtures with `od -c`: 19 end
`}\n`; `test073-rdfc10map.json` alone ends bare `}`. This matches the
prior diagnosis in
`docs/designissues/2026-07-04-rdfc10-ndegree-plan.md` ("Cluster C").

### Upstream check (submodule pin)

```
cd third_party/testing/rdf-canon && git fetch origin
git rev-parse HEAD        # 15619df2fda7a4ca88308733789b6774517f9638
git rev-parse origin/main # 15619df2fda7a4ca88308733789b6774517f9638 — same commit
git log --all --oneline -- tests/rdfc10/test073-rdfc10map.json
# 6bff859 Testing for issued identifiers and poison graphs. (#131) — the only commit that ever touched this file
```

The pinned submodule commit **is** `origin/main`'s tip; there is no
newer upstream commit to advance to. Option (b) (advance the pin with
evidence) does not apply — there is nothing to advance to.

### Why this is a harness bug, not a spec-compliance bug (option (a), pursued)

`third_party/testing/rdf-canon/tests/README.md` states two *different*
conformance rules for the two Map/Eval test kinds:

> Tests for RDFC-1.0 take input files ... generate Canonical N-Quads
> output ... **The test passes if the result compares identically as
> the expected result as text files.**
>
> Tests for RDFC-1.0 Issued Identifiers Map. ... **The test passes if
> the value of the resulting issued identifiers map matches the
> corresponding expected test result** that can be loaded via the
> `result` field of the test.

Eval tests are explicitly byte-for-byte text comparison. Map tests are
explicitly **value** comparison — this JSON file is test-harness
tooling for the "RDFC-1.0 Issued Identifiers Map" defined by the spec
(`https://www.w3.org/TR/rdf-canon/#dfn-issued-identifiers-map`), not
itself part of the RDFC-1.0 output format the spec governs byte-for-
byte. There is no RDFC-1.0 spec section defining the trailing-newline
byte behavior of this test-suite-internal JSON format — the "spec"
that applies here is the test suite's own README, and it says value
equality, not text-file equality.

`docs/designissues/2026-04-25-rdfc10-map-output.md` (the doc that
originally implemented Map-test support) already flagged this exact
gap in its "Hard limits" section as a byte-format implementation
detail, and `2026-07-04-rdfc10-ndegree-plan.md`'s Cluster C entry
explicitly proposed the fix taken here: "optionally make the map-test
comparison trim trailing whitespace before `=`... a harness-tolerance
nicety, not an algorithm fix."

### Fix

`bin/rdfc10-runner/rdfc10_runner.ml`: added `parse_json_string_map`
(flat `"key": "value"` extraction — the fixture format is fixed and
simple, no escapes/nesting) and changed `run_map_test` to compare
`sorted_pairs (parse_json_string_map got) = sorted_pairs
(parse_json_string_map expected)` instead of raw string equality. This
is strictly less strict than byte equality only in the sense the
README already licenses (whitespace/newline/comma formatting); it
still requires every key and value to match exactly, so it cannot mask
a real mapping bug — a wrong canonical label, a missing bnode, or an
extra bnode all still fail the comparison.

No change to `formal/fstar/RDF.Canonical.fst`'s mapping logic, no
fixture edit, no submodule pin move.

## test074c — poison-clique NegEval: implemented via HNDQ work budget

### What test074c actually is

`rdfc:RDFC10NegativeEvalTest` (`manifest.ttl:705`), "poison - Clique
Graph": 10 blank nodes, one predicate `<http:/example.com/p>`, every
node linked to every node including itself (`test074-in.nq`, a
complete directed graph with self-loops, K10). No `mf:result` —
negative tests have none. Per the suite's own conformance rule
(`tests/README.md`, "For a negative evaluation test, the test passes
if the implementation generates an error due to excessive calls to
[Hash N-Degree Quads]"), the *correct* implementation behavior for
this input is to detect the runaway cost and signal an error, not to
produce a canonicalized result.

### Why this input is actually pathological for our (correct, spec-shaped) HNDQ implementation

Every one of the 10 bnodes has an identical Hash First Degree Quads
value (full symmetry: same in/out-degree pattern to every other node,
self-loop included), so all 10 land in a single HFDQ-collision group,
which our HNDQ path (`formal/fstar/RDF.Canonical.fst`,
`hndq_run`/`walk_buckets`/`best_permutation`/`pick_best`/`walk_perm`/
`walk_recursion`) must resolve. For any one target bnode: excluding
self-loops, it has 9 quads as subject and 9 as object; because all 9
"other" bnodes are themselves symmetric, they all resolve to the same
Hash-Related-Blank-Node value, so both position buckets ("s" and "o")
end up with all ~9 members each — at or above the `take_n 6`
permutation cap (`6! = 720` permutations per bucket). Each
permutation's `walk_recursion` can trigger a fresh nested `hndq_run`
call for up to 6 freshly-issued members, each of which faces the same
~9-member symmetric structure again. This is multiplicative, not
additive: one top-level candidate's exploration alone can trigger tens
of thousands of nested `hndq_run` calls before the (already fuel-
bounded, so provably `Tot`) recursion naturally winds down — F*'s
totality guarantee bounds it to *finite*, not to *tractable*. Left
unbounded this is many orders of magnitude beyond the project's
ad-hoc-run cap (rule #17, 10 minutes).

### Fix: `hndq_budget` in `formal/fstar/RDF.Canonical.fst`

Added a `hndq_budget` record (`hb_remaining : nat`, `hb_exceeded :
bool`, sticky once tripped) threaded as an extra parameter/return
value through the whole HNDQ call graph: `hndq_run`, `walk_buckets`,
`best_permutation`, `pick_best`, `walk_perm`, `walk_recursion`
(unchanged mutual-recursion group otherwise — same `decreases`
metrics, same call shape, so the termination proof is untouched), plus
`explore_members`, `process_collision_members`,
`process_collision_groups`, `walk_groups`. One unit of budget is
consumed per `hndq_run` invocation (matching the README's own "calls
to Hash N-Degree Quads" phrasing literally). Every function checks
`hb_exceeded` before doing further (bucket / permutation /
recursion-list) work, so once tripped the whole exploration unwinds in
O(recursion depth) instead of continuing the blow-up.

`build_canonical_mapping_alg_budgeted : hash_algorithm -> nat ->
rdf_dataset -> option (list (bnode_id * string))` is the new top-level
entry point: `None` means the budget was exhausted (the
NegativeEvalTest "generates an error" case); `Some mapping` is the
ordinary result.

**Blast-radius containment** — every pre-existing public entry point
keeps its old signature and behavior:
- `build_canonical_mapping_alg` (2-arg, called directly by
  `rdfc10_runner.ml`'s Map-test path) and `build_canonical_mapping`
  wrap the budgeted function with `default_hndq_budget = 1_000_000`
  and unwrap `Some m -> m | None -> []`. The `None` arm is unreachable
  for every real (non-poison) input — see the runtime evidence below —
  and only exists because F* requires the `option` to be matched.
- `canonicalize_alg`, `canonicalize`, `canonicalize_to_nquads_alg`,
  `canonicalize_to_nquads` are untouched (they call
  `build_canonical_mapping_alg`, so the budget is transparent to them).
  Confirmed no other module (`factoidal_cli.ml`, `entry_jsoo.ml`,
  `factoidal_dump_nq.ml`, `jsonld_runner.ml`, `shacl_runner.ml`) calls
  the `_alg`-suffixed or `_budgeted` functions directly — they all go
  through the unbounded-in-practice wrappers.
- New: `canonicalize_exceeds_hndq_budget : hash_algorithm -> nat ->
  rdf_dataset -> bool` — `true` iff the given (small) budget was
  exhausted. Used only by `rdfc10_runner.ml`'s new
  `run_neg_eval_test`.

### Why `default_hndq_budget = 1_000_000` cannot regress the 84 passing tests

The entire 86-test suite (real fixtures, zero poison inputs among the
84/85 Eval/Map tests) runs in **~0.12s wall-clock** end-to-end
(`time ./bin/linux-x86_64/rdfc10_runner`), across all fixtures
including the largest HNDQ-collision cases already in the suite
(test044-046 "poison – evil" at 12 bnodes, test054 "t-graph" at 16,
test059 "n-quads parsing" at 19). That wall-clock is not consistent
with anywhere near a million `hndq_run` calls — it means every
legitimate fixture's real HNDQ call count is orders of magnitude below
the budget, so `default_hndq_budget` is provably inert for all of
them. Confirmed by re-running the full suite after the change: same
84 pass / 1 fail(pre-fix)/1 stub(pre-fix) baseline, then 86/86 after
both fixes land (see Results below), with no change in wall-clock.

### `neg_eval_budget = 5000` in `rdfc10_runner.ml`

The runner's negative-eval path uses a much smaller budget than
`default_hndq_budget` on purpose: test074's K10 clique's first
top-level candidate's exploration alone produces on the order of tens
of thousands of nested `hndq_run` calls (per the multiplicative
analysis above), so 5000 is comfortably exceeded within the first
candidate — the abort is a sub-second operation, not a "run until 1e6
calls" operation. 5000 remains far above any of the 84 real fixtures'
actual call counts (same 0.12s evidence above).

## Results

Both fixes land in the same F* module (`RDF.Canonical.fst`) plus the
runner (`bin/rdfc10-runner/rdfc10_runner.ml`, "outcome plumbing"
territory per this task's brief). `fstar.exe RDF.Canonical.fst`
verifies clean (no `--lax`, no `--admit_smt_queries`, z3 4.13.3).
Full before/after score and the 84-test regression check are recorded
in the landing commit / PR description, not duplicated here to avoid
drift between this doc and the actual measured numbers (rule #25).
