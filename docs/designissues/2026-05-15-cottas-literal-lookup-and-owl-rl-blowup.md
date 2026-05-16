# 2026-05-15 — Two regressions surfaced while wiring up the test environment

**Status (updated end-of-session):**
- **#261 (COTTAS literal lookup):** **FIXED** in two parts.
  - part A (literal-bound object encode): `1b4f412`.
  - part B (named-graph dispatch on Bet7): `ac77a12`.
  - All 4 `tests/local/cottas_corpus_regressions.sh` checks PASS; W3C SPARQL 561/561 and RDF 1031/1031 unchanged.
- **#262 (OWL-RL closure explosion):** characterised but not fixed. Bisect (commit `8e62e67`) shows no single rule is responsible — the blow-up is in the sequential sameAs cluster within `owl_rl_closure_step`. Needs sequenced inter-rule timing to localise.
- **#263 (owl_runner RDF/XML stall):** confirmed to be a duplicate of #262. The XML parser is fast (57 ms on the 260 KB profile-RL.rdf); the hang is in `owl_rl_closure_with_reflexivity` called per test premise.

Original text preserved below for archaeology.

While re-running the full test pipeline on a fresh build of
`bin/linux-x86_64/{w3c_runner, factoidal}` (commit `7eaf955`) two
soundness-class regressions surfaced. Both are reproducible end-to-end
in this repo with no external corpus once `pycottas` and the W3C
submodule are available.

## 1. COTTAS triple-pattern lookup silently drops literal-bound objects

### Symptom

`tests/local/backend_parity_regressions.sh`:

```
FAIL backend-default-ask
--- plain ---
true
--- cottas ---
[bet7-trace] ...
false
```

Reduced repro:

```bash
# data: 5 quads; one is in the default graph
cat > /tmp/d.nq <<EOF
<https://example.org/alice> <https://example.org/name> "Alice" <https://example.org/g/people> .
<https://example.org/default-subject> <https://example.org/status> "default" .
EOF

# materialise to COTTAS
./tools/.../corpus_pipeline.py materialize-nq-cottas-corpus \
  --input /tmp/d.nq --corpus-root /tmp/c --dataset-name s --chunk-name s

# plain answers "true"; COTTAS answers "false"
factoidal --data /tmp/d.nq  -e 'ASK { ?s ?p "default" }'    # true   (correct)
factoidal --data-cottas /tmp/c/s/v1/data.cottas \
                              -e 'ASK { ?s ?p "default" }'    # false  (WRONG)
```

### Axis isolation

Pattern shape → COTTAS result:

| Pattern | Result |
|---|---|
| `{ ?s ?p ?o }` (no bound terms) | matches all 5 rows ✓ |
| `{ <iri> ?p ?o }` (bound IRI subject) | matches ✓ |
| `{ ?s <iri> ?o }` (bound IRI predicate) | matches ✓ |
| `{ ?s ?p "lit" }` (bound literal object) | **0 results** ✗ |
| `{ <iri> <iri> "lit" }` (all bound, literal object) | **0 results** ✗ |

The failure axis is **bound literal in object position**, regardless of
whether other positions are bound or wildcards.

### Root cause (likely)

The pycottas-materialised parquet column stores literals in N-Triples
form, surrounded by ASCII double quotes:

```
('<https://example.org/alice>', '<https://example.org/name>',  '"Alice"',
 '<https://example.org/g/people>')
('<https://example.org/default-subject>', '<https://example.org/status>',
 '"default"', 'DEFAULT')
```

IRIs are stored with angle brackets (matching what the F\* SPARQL
evaluator passes), so IRI-bound lookups round-trip cleanly. Literals
in the column carry their ASCII double-quote wrapper, but the
F\*-side lookup token (the `token` argument to
`ondisk_lookup_obj_id_global` realised by
`experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh`)
appears to be passed without the quote wrapper. The
`Hashtbl.find_opt (table_of tables) token` lookup therefore misses
every literal-keyed row.

The diagnosis is consistent with the lookup-shape mismatch the recovery
plan calls out — see
[`docs/designissues/fstar-ocaml-boundary-audit.md`](fstar-ocaml-boundary-audit.md)
section "Codename violator confirmation" rows for **#118** and **#254**.
This bug is plausibly retired when those land, but it's a soundness gap
worth flagging on its own ticket.

### Why CI did not catch this

`tests/local/backend_parity_regressions.sh` requires `pycottas`
in a venv at `_tmp.junk/pycottas-venv/`. The sandbox we run in did not
have that until installed today; CI presumably also skips the test by
not installing pycottas — the script exits 0 (script-level "skipped")
rather than failing, so the dashboard reflects "no failures."

### Severity

Silent wrong-answer bug for any SPARQL query whose triple pattern binds
a literal in the object slot. Affects ASK, SELECT, CONSTRUCT, MINUS,
FILTER NOT EXISTS, etc. — anywhere the COTTAS backend is the active
store and a literal constant appears in a BGP.

### Suggested next step

Add a unit test that builds a tiny COTTAS file in-process and exercises
`ondisk_lookup_obj_id_global` with a literal that exists in the column.
The current hash-witness writers (`tests/unit/*_writer_roundtrip.ml`)
provide most of the infrastructure to construct test fixtures
deterministically.

## 2. OWL-RL closure explodes on the W3C `entailment/simple1` test fixture

### Symptom

`bin/linux-x86_64/w3c_runner entailment` hangs forever at test
[50/70] `simple1` (OWL-Direct entailment regime). Two budgets
(15 min, 30 min) died at exactly the same position.

### Repro (16-triple input, no W3C runner needed)

```bash
# parses 16 triples, then calls RDF_Graph_Executable.owl_rl_closure_with_reflexivity
tests/unit/owl_direct_pipeline_timing.ml
```

Output:

```
parsed: 16 triples
[owl_rl_closure fuel=1           ] 0.086s
  -> 207 triples (0.086s)
... fuel=2 never returns within 5 min
```

`simple.ttl` has the standard W3C `entailment/` fixture: 3 named OWL
classes, 1 functional property, 4 individuals. After one step the
closure produces 207 triples — a 13× growth. After two steps it does
not terminate in 5 min.

### Cross-check

The committed binary in `bin/linux-x86_64/w3c_runner` is byte-identical
to a fresh build from this repo (no `git diff`). The May-14 dashboard
(`docs/test-results/latest.json`) reports `70 pass, 0 fail` on
entailment, suggesting CI either:

- runs with a per-test wall-clock cap that marks long-running tests
  as skipped (no such cap is visible in `bin/w3c-runner/w3c_runner.ml`),
- or the closure is somehow non-deterministic on different hardware,
- or the dashboard was generated against a prior build whose closure
  shape was different.

### Suggested next step

Add a `--fuel-cap` argument to `owl_rl_closure_with_reflexivity` (or
respect the existing `fuel` arg more aggressively) so closure work is
bounded per test. Separately, audit which closure rules fire on
`simple.ttl` between steps 1 and 2 — the 13× per-step growth at this
input size suggests an unstratified reflexivity / sameAs rule firing
once on every new triple it produces.

## 3. owl_runner stalls on any non-trivial RDF/XML catalog

### Symptom

`bin/linux-x86_64/owl_runner` (no args) silently consumes wall-clock for
10+ minutes then SIGTERM. Reading `profile-RL.rdf` (4919 lines / ~200KB)
never produces output.

### Repro

```bash
# the only catalog small enough to terminate (725 bytes, 24 lines):
$ time owl_runner third_party/testing/owl/RL-RDF-rules-tests.rdf
  parsed 3 triples in 0.00s
  Totals: 0 test cases
  ...
real  0m0.027s

# any catalog above ~1KB hangs:
$ timeout 30 owl_runner third_party/testing/owl/profile-QL.rdf   # 181 KB
Terminated  (exit 143)

$ timeout 30 owl_runner third_party/testing/owl/profile-EL.rdf   # ~190 KB
Terminated  (exit 143)
```

The runner never reaches the "parsed N triples in T.Ts" line on these
inputs, so the hang is during RDF/XML parse, not during test execution.

### Likely root cause

`Parser.RDFXML.fst` exhibits superlinear behavior. The smallest file
that succeeds is 24 lines / 3 triples; the smallest that fails is
3289 lines / ~180KB. Native parsers for similar XML inputs typically
take milliseconds.

The 'parsers belong in F*' rule (Iron Rule #4) is preserved here, but
the verified parser implementation needs an algorithmic audit. Likely
suspects: string-append quadratic, list-prepend then reverse, or
re-parsing the same nested element on every push.

### Severity

`owl_runner` is documented as a "Phase 0 skeleton — does NOT run any
reasoning yet" per its `--help`. The dashboard's
`owl_rl_positive_entailment: pass:20,fail:10,total:30` (`docs/test-results/latest.json`)
must therefore use a different path — possibly a smaller manifest, an
earlier pre-parsed catalog, or an entirely different runner. Worth
clarifying which path produces that number before treating the dashboard
as the source of truth for OWL.

### Suggested next step

Profile `Parser.RDFXML.fst` against a small RDF/XML fixture
(e.g. `third_party/testing/w3c/rdf-tests/rdf/rdf11/rdf-xml/example-01.rdf`),
locate the hot loop, audit for quadratic-in-input idioms.
