# Jena ARQ probe refresh — 2026-07-03

Re-run of the four Jena ARQ comparison probes
([tools/jena_arq_syntax_probe.sh](../../tools/jena_arq_syntax_probe.sh),
[tools/jena_arq_basic_probe.sh](../../tools/jena_arq_basic_probe.sh),
[tools/jena_arq_graph_probe.sh](../../tools/jena_arq_graph_probe.sh),
[tools/jena_arq_ask_probe.sh](../../tools/jena_arq_ask_probe.sh))
against the committed binary `bin/linux-x86_64/factoidal` at commit
`20f27b3` ("ci: .checked verification cache for the check-extraction PR
gate (P4)"). Every run was capped at `timeout 600`.

Binary provenance: a concurrent extraction build was rewriting the
workspace copy of `bin/linux-x86_64/factoidal` during this session
(`git status` showed it modified), so all results below were confirmed
against the exact committed bytes, extracted with
`git show HEAD:bin/linux-x86_64/factoidal > /tmp/factoidal-committed`.
The workspace (mid-build) copy produced identical scores on all four
probes.

Two regressions against the historical docs, both reproduced and
root-caused below: query-side blank nodes no longer match on the
default (backend) evaluation path, and blank-node labels collide
across separately loaded data files. Syntax and ASK are clean.

## Environment: getting the Jena test data

The Jena repository layout moved since the historical probes were
recorded. `jena-arq/testing/DAWG-Final/` and `jena-arq/testing/ARQ/Ask/`
no longer exist as checked-in directories at Jena HEAD — the whole old
testing tree is preserved inside a zip at
`jena-arq/testing/ARQ/testing-2026-05.zip`.

Working recipe (release assets do not download through the proxy, but
git clone does):

```bash
git clone --depth 1 --filter=blob:none --sparse https://github.com/apache/jena /tmp/jena
git -C /tmp/jena sparse-checkout set jena-arq/testing
unzip -q -o /tmp/jena/jena-arq/testing/ARQ/testing-2026-05.zip -d /tmp/jena-zip-extract
ln -sfn /tmp/jena-zip-extract/testing/DAWG-Final /tmp/jena/jena-arq/testing/DAWG-Final
ln -sfn /tmp/jena-zip-extract/testing/ARQ/Ask   /tmp/jena/jena-arq/testing/ARQ/Ask
pip install rdflib   # basic/graph probes parse manifests with rdflib
```

The zip's `testing/DAWG-Final/` content is byte-identical in the suites
we probe (query text and data files carry 2007 DAWG timestamps
repackaged in 2026), so historical comparisons remain apples-to-apples.

## Script fix

All four probe scripts hardcoded
`BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"`. That path is a
symlink into `bin/<platform>/`, but it sits inside `formal/fstar/`
which an extraction build can rewrite mid-run. Each script now accepts
a `FACTOIDAL_BIN` override with the old path as default:

```diff
-BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
+BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
```

(same one-line change in all four scripts). All runs below used
`FACTOIDAL_BIN=/home/user/factoidal/bin/linux-x86_64/factoidal`.

## Results

| Probe | Suite | 2026-07-03 result | Historical | Delta |
|---|---|---|---|---|
| syntax | syntax-sparql3 | 9 of 9 positive pass, 42 of 42 negative pass | 9/9 pos, 42/42 neg | unchanged |
| syntax | syntax-sparql4 | 4 of 4 positive pass, 8 of 8 negative pass | 4/4 pos, 8/8 neg | unchanged |
| syntax | syntax-sparql5 | 2 of 2 positive pass | 2/2 | unchanged |
| basic | DAWG-Final/basic (full, 27 tests) | 24 pass, 3 fail | n/a (full suite not previously run) | — |
| basic | DAWG-Final/basic (LIMIT=20 slice) | 17 pass, 3 fail | 20 pass, 0 fail | **regression** |
| graph | DAWG-Final/graph (11 approved tests) | 9 pass, 2 fail | 11 pass, 0 fail | **regression** |
| ask | ARQ/Ask (8 tests) | 8 pass, 0 fail | no recorded baseline | new baseline |

### Individual failures

- `basic/list-2` — expected 1 row, got 0. Query `SELECT ?p { :x ?p (1) . }`
  fails to match the collection `("1"^^xsd:integer)`.
- `basic/list-3` — expected 1 row, got 0. Same shape with `(?v)`.
- `basic/list-4` — expected 1 row, got 0. Same shape with `(?v ?w)`.
- `graph/graph-09` — expected 0 rows, got 1. Default-graph `_:x`
  (data-g3.ttl) spuriously joins named-graph `_:x` (data-g4.ttl).
- `graph/graph-10b` — expected 0 rows, got 2. Same collision between
  data-g3.ttl and data-g3-dup.ttl.

## Regression 1: query blank nodes are constants on the backend path

Every query-side blank node fails to match — not just collections.
Minimal repro against `DAWG-Final/basic/data-2.ttl`:

- `SELECT ?p { :x ?p [] . }` — 0 rows (should be 4)
- `SELECT ?p { :x ?p _:b . _:b rdf:first 1 . }` — 0 rows (should be 1)
- `SELECT ?p { :x ?p ?l . ?l rdf:first 1 ; rdf:rest rdf:nil . }` — 1 row
  (correct; explicit variables work)

Cause, in two halves:

1. The F\* algebra evaluator applies the SPARQL 1.1 §18.2.2.9
   bnode-to-existential-variable rewrite — `rewrite_query_bnodes_pattern`
   at `formal/fstar/SPARQL11.Algebra.fst:3715` inside
   `eval_select_query`. The backend executor
   (`eval_select_query_backend_dataset` /
   `eval_select_query_backend_on_graph` / `eval_pattern_backend` in
   [formal/fstar/SPARQL11.Store.fst](../../formal/fstar/SPARQL11.Store.fst),
   around line 752) never applies it, so `PT_BNode` falls through to
   the constant-term match at `SPARQL11.Algebra.fst:1871`
   (`if rdf_term_eq (T_BNode b) o then ... else None`).
2. The CLI's `use_backend_exec` gate in
   [bin/factoidal-cli/factoidal_cli.ml](../../bin/factoidal-cli/factoidal_cli.ml)
   (around line 1036) was widened from `data_cottas_files <> []` to
   "every SELECT/ASK with no entailment regime", to pick up the
   `detect_streaming_count_group_by_graph` fast path for in-memory
   loads. That routed all ordinary `--data` queries onto the
   rewrite-less backend path.

Confirmation: `factoidal --entail RDFS --data data-2.ttl --query
list-2.rq` (which forces the algebra path because the backend gate
requires the no-entailment case) returns the expected 1 row
`?p = :list1`; the same query without `--entail` returns 0 rows.

Fix direction (F\*-side, per rule #11 — not applied here because an
extraction build was running in `formal/fstar/` during this session):
apply `rewrite_query_bnodes_pattern` to `q.q_pattern` at the top of the
backend SELECT/ASK entry points in `SPARQL11.Store.fst`, mirroring
`SPARQL11.Algebra.fst:3715`, and extend the synthetic-variable
projection skip (`is_synthetic_bnode_var`) the same way the algebra
path does.

## Regression 2: blank-node labels collide across loaded files

[docs/designissues/jena-arq-graph-probe.md](jena-arq-graph-probe.md)
records that "separate loaded files now get distinct blank-node
namespaces at the RDF dataset boundary". That behaviour is absent in
the current binary: `_:x` parsed from `data-g3.ttl` (default graph via
`--data`) and `_:x` parsed from `data-g4.ttl` (named graph via
`--named`) are the identical `T_BNode "_:x"` term, so
`{ ?s ?p ?o GRAPH ?g { ?s ?q ?v } }` joins them (graph-09: 1 row
instead of 0; graph-10b: 2 rows instead of 0).

`load_dataset` / `load_triples` in
[bin/factoidal-cli/factoidal_cli.ml](../../bin/factoidal-cli/factoidal_cli.ml)
(lines 112-140) call the extracted parsers and merge the results with
no per-file blank-node scoping, and no relabeling happens downstream at
the dataset-assembly point (lines ~980-1027). This one is independent
of the backend-vs-algebra path split — the collision is baked in at
load time.

Fix direction: per-file blank-node scoping belongs in F\* at the
dataset boundary (e.g. a `scope_bnodes : string -> rdf_graph ->
rdf_graph` applied per loaded file, or per-parse fresh label prefixes),
then the CLI merge stays a plain concatenation. Whatever module carried
the original fix appears to have been lost in a refactor; the shallow
clone history (single squashed commit touching the probe docs) does not
show when.

## What to add to tests/local/

Both regressions are Jena disagreements that reflect real SPARQL 1.1
semantics gaps, and neither is covered by
[tests/local/backend_parity_regressions.sh](../../tests/local/backend_parity_regressions.sh)
(which compares in-memory vs COTTAS answers — both backends share the
bnode bugs, so parity stays green while both are wrong). Two additions:

1. `tests/local/sparql/query_bnode_collection.rq` + a fixture copy of
   the 4-triple `data-2.ttl` under `tests/local/data/` — assert
   `SELECT ?p { :x ?p (1) . }` returns exactly 1 row. Covers the
   §18.2.2.9 rewrite on whatever path the CLI defaults to, so the
   backend-gate widening can never silently drop it again.
2. A two-file fixture (`bnode_scope_default.ttl`, `bnode_scope_named.ttl`,
   both containing `_:x :p 1 .`) with the graph-09 query shape —
   assert 0 rows when one is loaded via `--data` and the other via
   `--named`. Covers per-file blank-node scoping.

Not added in this session (deliverable was measurement + doc, no
commits); the fixtures above are copy-paste-ready from the repro
commands in this doc.

## Reproduction commands

```bash
export FACTOIDAL_BIN=/home/user/factoidal/bin/linux-x86_64/factoidal
timeout 600 tools/jena_arq_syntax_probe.sh
timeout 600 tools/jena_arq_basic_probe.sh
timeout 600 tools/jena_arq_graph_probe.sh
timeout 600 tools/jena_arq_ask_probe.sh
```
