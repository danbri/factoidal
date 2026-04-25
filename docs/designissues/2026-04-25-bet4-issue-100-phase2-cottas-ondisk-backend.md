# 2026-04-25 — Issue #100 Phase 2 — On-disk COTTAS backend (Bet4)

**Branch:** `claude/100-phase2-cottas-ondisk`
**Status:** in flight
**Author:** Claude (Bet4 subagent)

## Goal

Make `--data-cottas` a real on-disk SPARQL backend. Stop materialising
the parquet to an in-memory `rdf_dataset` at startup. Page reads on
demand at query time, sized by an LRU buffer pool (default 64 MB).

## Where we are now

- F\* `SPARQL11.Store.fst` has `GB_COTTAS` which calls into
  `cottas_search`/`cottas_estimate` — all `assume val`.
- The OCaml extraction (`ocaml-output/Parser_BallyhooCOTTAS.ml`) has a
  `Ballyhoo_cottas_runtime` module that:
  1. Pre-decodes ALL four columns at `cottas_open_dataset_store` via
     `Parquet_Footer.probe_parquet_column_decode_all` (issue #98 path).
  2. Builds full id ↔ term hashtables.
  3. Stores a `quads : quad_row list` and walks it with `List.fold_right`
     for every `cottas_search` call.
- `factoidal_http.load_cottas_dataset` then walks `cache.quads` AGAIN to
  rebuild an `rdf_dataset` for the in-memory eval path.

So we already have an indirection layer. The fix is at the runtime
boundary: keep the F\* AST + assume-val signatures, but change the
*OCaml backing* and the F\* search logic so that:

- `load_cache` defers per-cell decoding until queried.
- The "cache" holds (a) compact dictionaries and (b) row-level term-id
  arrays only — not materialised triples.
- A buffer pool sits behind the parquet file for column page reads.

## Design

### The artifact-level API stays the same

`cottas_open_dataset_store : string -> option summary -> option ds`
keeps its current signature. We do NOT rename `GB_COTTAS`. The
existing `factoidal_http.ml:399` codepath that goes
`load_cottas_dataset → rdf_dataset → list_dataset_backend` is replaced
by `cottas_open_dataset_store → GB_COTTAS ds None`.

### What changes, on disk

A `cottas_dataset_store` after this work holds, in OCaml-runtime terms:

```
{ cds_artifact_path : string                       (* same *)
  cds_summary       : option cottas_artifact_summary  (* same *)
  cds_handle        : cottas_handle                (* OPAQUE — see below *)
}
```

`cottas_handle` (ABSTRACT in F\*; concrete in OCaml glue):

```ocaml
type cottas_handle_concrete = {
  ch_path             : string;
  ch_term_id_columns  : term_id_arrays;     (* (Z.t array * Z.t array * Z.t array * Z.t option array) *)
  ch_dictionaries     : dictionaries;       (* int -> string maps for s/p/o/g *)
  ch_predicate_index  : (Z.t, int list) Hashtbl.t;  (* hot index: predicate term-id -> row indexes *)
  ch_summary          : cottas_artifact_summary option;
}
```

Key choice: we keep the **per-column dictionaries** (already small:
the parliament corpus has tens of thousands of unique terms not
millions) and the **per-row term-id arrays** (one int per row per
column = 4 * num_quads * ~8 bytes ≈ 100 MB for the 3.14 M parliament
corpus — comfortably bounded).

**What we drop:** the 3.14 M `quad_row` records, the parsed
`subject`/`wf_iri`/`rdf_term` values for every row (these become *lazy*
— decoded only for matching rows at query time), and the
`load_cottas_dataset` materialisation entirely.

### Buffer pool — punted to Phase 3

For the parliament corpus, decoded term-id arrays + dictionaries are
~100 MB. That's strictly less than the current `quads` list
(~3M `quad_row` records + the 4 hashtables + the materialised
`rdf_dataset` triple list = several hundred MB).

An mmap'd page cache atop the parquet would let us avoid even those
~100 MB, but that's a much bigger lift requiring:
- F\* models for parquet row-group page boundaries (Yod3 / #98 Gap B).
- A page-LRU in OCaml with eviction.
- A *streaming* search path that doesn't pre-decode anything.

Phase 2 ships the smaller win first: stop materialising triples /
rdf_dataset, keep only term-ids + dictionaries. Phase 3 can add the
page cache once #98 Gap B (multi-row-group walker) lands.

### F\* changes

`Parser.BallyhooCOTTAS.fst` adds:

```fstar
type cottas_predicate_index_entry = {
  cpie_pred : cottas_term_ref;
  cpie_count : nat;
}

assume val cottas_handle_predicate_count :
  cottas_dataset_store -> cottas_term_ref -> Tot nat

assume val cottas_handle_subject_count :
  cottas_dataset_store -> cottas_term_ref -> Tot nat
```

These give the F\* `cottas_estimate` something more precise than
"length of a full scan" without requiring F\* itself to model the
hashtable. The actual estimate function (`cottas_estimate`) stays
declared as `assume val` for now — **the search logic is in OCaml glue**.

This is acceptable per CLAUDE.md rule 3: every `assume val` is an
acknowledged gap with a stub. Issue #100 Phase 2 lists this as the
intentional gap. **Future Phase 3 promotes the search to F\*** once
we have a verified sorted-index ADT to work against.

### Acceptance test

```bash
factoidal serve --data-cottas tmp/ukparliament/CorpusCOTTAS/.../data.cottas --port 5081 &
SERVER=$!
sleep 5  # bind fast (issue #99) — load runs in bg

# Wait for /backend-info.json to report ready
until curl -s localhost:5081/backend-info.json | jq -e '.loading == false'; do sleep 1; done

# Memory snapshot
ps -o rss= -p $SERVER  # vs the eager-load baseline

# Smoke query
time curl -s localhost:5081/sparql --data-urlencode \
  'query=SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
# Expect ?n = 122880 (or 3.14M after #98 Gap B), wall-clock < 30 s
```

## Out of scope (defer)

- Real mmap + page-LRU — Phase 3 after #98 Gap B.
- INSERT/DELETE on disk (Phase 4).
- SQLite/RocksDB external backend (Phase 5).

## Tracking

- Issue #100 (this work)
- Issue #99 (fixed: bind-first behaviour stays — `factoidal_http.ml`
  loader thread continues to populate `dataset_ref` in the
  background; what changes is *what* it loads).
- Issue #98 (Resh's RLE_DICTIONARY decoder; Gap B needed for >1
  row group support).
