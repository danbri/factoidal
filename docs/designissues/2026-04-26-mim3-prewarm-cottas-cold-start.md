# Mim3 — Pre-warm COTTAS columns on daemon boot (cold-start hide)

Date: 2026-04-26
Issue: #100 (followup to Bet7 commit `7ecf720`)
Branch: `claude/main`

## Problem

After Bet7's lazy/parallel handle build (`7ecf720`), `cottas_ondisk_open` is
~0.023 s. But each column's `ensure_*_loaded` populator still runs on the
**first** query that needs it:

| Populator                        | First-query cost on UK Parliament |
|----------------------------------|-----------------------------------|
| `ensure_predicates_loaded`       | ~14 s                             |
| `ensure_subjects_loaded`         | ~30 s                             |
| `ensure_objects_loaded`          | ~30 s                             |
| `ensure_graphs_loaded`           | ~ms-to-seconds                    |

Aleph6 measured a predicate-bound `LIMIT 5` taking 87 s cold (almost all
populate, 1/26 row groups walked). Demos opening tomorrow (2026-04-27) need
sub-second first-query latency.

## Decision

Pre-warm all four columns at daemon-boot inside the worker block that calls
`open_cottas_ondisk_files`, before flipping `loading := false`. Boot grows
by ~30–60 s (acceptable; demo runner waits once).

## Approach (A — direct ensure-call)

In `formal/fstar/ocaml-output/factoidal_http.ml::open_cottas_ondisk_files`,
after each successful `cottas_ondisk_open`, call:

```ocaml
let h = store.RDF_CottasStore.cods_handle in
let tables = RDF_CottasStore.Cottas_ondisk_runtime.tables_for h in
RDF_CottasStore.Cottas_ondisk_runtime.ensure_predicates_loaded h tables;
RDF_CottasStore.Cottas_ondisk_runtime.ensure_subjects_loaded   h tables;
RDF_CottasStore.Cottas_ondisk_runtime.ensure_objects_loaded    h tables;
RDF_CottasStore.Cottas_ondisk_runtime.ensure_graphs_loaded     h tables;
```

Bet7's `Cottas_ondisk_runtime` module (extracted into `RDF_CottasStore.ml`)
already exposes both `tables_for` and the four `ensure_*_loaded` at top
level — no glue change needed in `cottas_ondisk_z_lazy_open.sh`.

## Rejected: Approach B (dummy `LIMIT 1` SELECT)

Less precise — predicate population needs a separate predicate-bound query.
Approach A is direct and one call per column.

## Smoke target

```
./bin/darwin-arm64/factoidal-http --port 3032 \
  --data-cottas tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas
```

First HTTP query after the "ready" line should return in <2 s
(was 87 s cold).
