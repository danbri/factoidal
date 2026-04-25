# 2026-04-25 — factoidal-http: --data-cottas FILE

Status: in flight (Agent Daleth2)

## Goal

Allow `factoidal-http` to seed its dataset from a binary COTTAS / Parquet
artifact instead of (or in addition to) an N-Quads / Turtle / TriG file.

The motivation is concrete: the UK Parliament 2019 corpus is 584 MB as
N-Quads but 62 MB as COTTAS, and Wave 13's Cottas-Perf bulk-page-decode
path (HEAD `08f1855`) loads that 3.14 M-quad corpus in seconds rather
than minutes. We want to A/B compare an in-memory N-Quads endpoint
against a binary-COTTAS endpoint on :3032.

## Plan

1. Add fields to `factoidal_http.ml`'s `config` record:
   - `mutable data_cottas_files : string list`
2. Extend `parse_args` with two equivalent spellings:
   - `--data-cottas FILE` (matches the `factoidal` CLI)
   - `--cottas-data FILE` (alias requested by user)
   Repeatable; appends to `cfg.data_cottas_files`.
3. In `load_dataset`, after building `base_ds` from `--dataset` and
   merging `--load-rw-graphs`, merge each COTTAS dataset by reusing the
   loader already in `factoidal_cli.ml`. Inline a copy of
   `load_cottas_dataset` (it's pure OCaml glue around the F\* reader;
   per rule #15 no semantic logic is being added — this is wiring).
4. Add usage docs + startup log lines.
5. Compile via `build-ocaml.sh compile`.
6. Smoke test:
   ```
   ./bin/darwin-arm64/factoidal-http --host 100.107.116.70 --port 3032 \
       --read-only --cors='*' \
       --data-cottas /tmp/ukpar_corpus/ukparliament-2019/v1/data.cottas
   curl -G --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' \
       http://100.107.116.70:3032/sparql
   ```
   Expected: 3 143 406 in seconds.

## Rules touched

- #1 F\* is the source of truth — yes, COTTAS decoder is in F\*
  (`Parser.BallyhooCOTTAS.fst` + `Parquet.Footer.fst`); we only reshape
  the decoded result into `rdf_dataset`.
- #13 Don't edit extracted .ml — `factoidal_http.ml` is hand-authored
  OCaml glue, not extracted; editing it is fine.
- #15 No semantic logic in patches/glue — this change is pure I/O wiring.

## Coordination

Agent Gamma2 is editing the landing page in the same file. Daleth2's
edits are confined to:
- `config` record (top of file)
- `default_config`
- `usage` block (insert lines near `--dataset`)
- `parse_args` (one new clause)
- `load_dataset`
- startup log printf in `run_server`

No overlap with the landing-page HTML helpers.

## F\* verify

None — pure OCaml glue. The F\* COTTAS reader is unchanged.

## Resolution (2026-04-25 ~08:00)

Code changes landed in commit `807cbb1` alongside Gamma2's landing-page
edits (the same file got both diffs squashed when Gamma2 picked up the
in-flight change before staging). Smoke test on a small 2 KB COTTAS
(`tmp/kgx-cottas-direct-import/therapeutic_use/data.cottas`):

```
factoidal-http --port 3033 --read-only --cors='*' \
  --data-cottas .../therapeutic_use/data.cottas
# READY in 2 s
# store totals: 0 default-graph triples, 1 named graph(s)
SELECT (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }  # -> 92
SELECT DISTINCT ?g ...                                     # -> urn:factoidal:kgx:therapeutic_use
```

The argv parser, `load_cottas_dataset`, named-graph routing, and SPARQL
evaluator are wired correctly end-to-end.

### Pre-existing perf issue: Parliament-scale corpus

3.14 M-quad UK Parliament COTTAS (62 MB) does **not** complete on
either binary in this build:

- `factoidal --data-cottas .../data.cottas --count` — **terminated
  abnormally after 1329 s** (real), 1315 s user. Exit code 0 to the
  shell, but no output. This is the existing CLI binary in HEAD
  (Wave 13, `9378d52`).
- `factoidal-http --data-cottas .../data.cottas` — same hang; the
  process spends 100 % CPU in `Batteries.UTF8.nth_aux` (per `sample`
  trace), tracking with the per-row UTF-8 token decode in
  `cottas_runtime.sh:300-314`.
- 1.2 MB COTTAS (`protein__protein1`) hung > 615 s — never reached
  LISTEN. So the cliff is well below 3 M quads.

This is documented separately in
`2026-04-25-cottas-http-hang-diagnosis.md` (Zayin2). It is **not**
caused by this `--data-cottas` wiring; the loader is the same code
path the CLI already uses, and the CLI fails at the same point.
Fixing belongs in F\* / `cottas_runtime.sh` (the per-row token
parsing), not in `factoidal_http.ml`.

### Launching the comparison endpoint (when the loader is fast)

```
# In-memory N-Quads endpoint (already running on :3030):
factoidal-http --host 100.107.116.70 --port 3030 --read-only --cors='*' \
  --dataset /tmp/ukpar_corpus/ukparliament-2019/v1/data.nq

# Binary COTTAS endpoint:
factoidal-http --host 100.107.116.70 --port 3032 --read-only --cors='*' \
  --data-cottas /tmp/ukpar_corpus/ukparliament-2019/v1/data.cottas
```

Compare with:
```
curl -G --data-urlencode 'query=SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' \
     -H 'Accept: application/sparql-results+json' \
     http://100.107.116.70:3032/sparql
```

