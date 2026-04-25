# Vav2 — COTTAS `next_id` O(N²) → O(1) per-column counters

Date: 2026-04-25

## Problem (per Resh2's diagnosis)

`cottas_runtime.sh` injects `Ballyhoo_cottas_runtime.next_id`, which on every
intern call walks **all four** interning hashtables via `Hashtbl.fold` to find
the max id, then `Z.succ`'s it. That's O(N) per row per column. With ~3.14 M
rows × 4 columns interned each row, it becomes ~10¹⁴ Z.t comparisons.

The COTTAS Parquet decode itself is fine (Bet5 + Resh2 verified the multi-
row-group decode); the bottleneck is the hand-rolled OCaml glue that builds
the term-ref dictionary.

## Fix

Replace `next_id : (string,Z.t) Hashtbl.t list -> Z.t` with **per-column
mutable counters** stored on the cache record:

- `subj_counter`, `pred_counter`, `obj_counter`, `graph_counter` : `int ref`
- Each `intern_*` allocates `Z.of_int !counter`, then `incr counter`.

The id-spaces are independent per column (they are looked up by column-typed
references — `cottas_term_ref` for s/p/o, `cottas_graph_ref` for g — and the
decoders dispatch off the column's hashtable, not a shared id space). So
making the counters per-column is semantics-preserving.

Concurrency: the load path is single-threaded (a `for i = 0 to N-1 do`
loop in `load_cache`), so plain `int ref` is safe. No locking needed.

## Acceptance

```
./bin/darwin-arm64/factoidal cottas-info \
  tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas
# expect: quads: 3,143,406  (seconds, not minutes)
```

## Risk

Low. Only touches the patch script that injects the runtime module. F* spec
unchanged. No semantic logic added.
