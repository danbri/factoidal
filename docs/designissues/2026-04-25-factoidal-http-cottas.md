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
