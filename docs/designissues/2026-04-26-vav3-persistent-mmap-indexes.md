# Vav3 — persistent mmap'd COTTAS indexes (scratch)

**Date:** 2026-04-26
**Subagent:** Vav3
**Status:** in flight

## Problem

Today's COTTAS engine pays a 107 s pre-warm at boot (Mim3 `d63c4af`,
Yod6 `3a19ed4`, Tet3 `7ebba73`). It builds in-RAM Hashtbls:

| Hashtbl | Purpose | Parliament size |
|---|---|---|
| `ft_subj_tok_to_id` / `ft_id_to_subject` | encode/decode subjects | 908 k |
| `ft_pred_*` (×2) | predicates | 232 |
| `ft_obj_*` (×2) | objects | 956 k |
| `ft_graph_*` (×2) | graphs | 0 |
| `pred_presence_by_path` | Yod6 per-rg pred set | ~6 KB |
| `subj_presence_by_path` / `obj_presence_by_path` | Tet3 per-rg subj/obj sets | ~3 MB each |

All deterministic functions of the .cottas file. All thrown away on restart.
Pure waste.

## Plan

Replace pre-warm with persistent companion files mmap'd at boot. Lookup
functions written in F\* (`RDF.CottasStore.OnDiskIndex.fst`); only byte-range
I/O primitives are `assume val`.

### Companion files (sibling to `data.cottas`)

For each column `<col>` ∈ {s, p, o, g}:

**`data.cottas.<col>.dict`** — sorted token dictionary
```
[ magic 'COTD' u32 ][ version u32 ][ num_tokens u32 ][ pad u32 ]
[ ids_offset u64 ][ tokens_offset u64 ]
[ ids[]         u32 × num_tokens   sorted ASC by tokens[ids[i]] ]
[ token_offs[]  u64 × num_tokens+1 ]
[ token_data    bytes (UTF-8 concat) ]
```
- encode: binary search `ids[]`, comparing token to byte slice.
- decode: array lookup + slice.

**`data.cottas.<col>.presence`** — per-rg presence bitmap
```
[ magic 'COTP' u32 ][ version u32 ][ num_rgs u32 ][ num_tokens u32 ]
[ bitmap bytes ⌈num_rgs * num_tokens / 8⌉, bit (rg*num_tokens + tok) ]
```
- `rg_contains_token`: one byte read, one bit test.

### Three pieces

1. F\* module `RDF.CottasStore.OnDiskIndex.fst` with refinement types,
   F\*-pure lookup functions, `assume val` for mmap + byte-range reads.
2. OCaml writer + boot-mmap glue in
   `experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh`.
3. `factoidal_http.ml` rewires `prewarm_cottas_columns` → "open mmaps,
   else build companions once, then mmap".

### Disposition of Yod6 / Tet3 in-RAM Hashtbls

Replaced by mmap'd presence bitmap. Yod6/Tet3 patches stay on disk for
the build path (they walk parquet column chunks to discover which tokens
appear in which row group), but the **runtime query path** consults the
on-disk bitmap, not their in-RAM `pred_presence_by_path`/etc.

## Acceptance

1. F\* OnDiskIndex.fst verifies clean (no `--lax`).
2. First boot ~110 s (one-time companion build).
3. Second boot < 2 s (mmap-only).
4. 4 smoke queries identical to today's daemon.
5. W3C 1657/1/0/4 unchanged.
6. Companions persist across restart; deletion → rebuild.
