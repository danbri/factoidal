# Phi5 audit: Vav3 mmap'd companion-file READ path verification

**Status:** in progress, started 2026-04-26 by Phi5 (subagent).
**Phase:** 2.3 of `docs/designissues/fstar-purity-unwind.md`.
**Base commit:** 48cdf53.

## Goal

Verify that Vav3's mmap'd companion-file READ path actually goes through
F\* `RDF.CottasStore.OnDiskIndex.fst` and not through duplicate OCaml glue.
Identify duplicates as candidates for Phase 2.6 (do NOT fix yet).

## Method

For each function in `cottas_ondisk_zzzzz_ondisk_index.sh` and the resulting
`Cottas_companion_*` modules, classify as:

- **WRITER** (acceptable I/O glue per rule #15): builds `.dict`/`.presence`
  files at boot.
- **F\*-DELEGATING READER**: thin wrapper that calls F\*
  `RDF_CottasStore_OnDiskIndex.dict_decode_token` / `dict_encode_token` /
  `presence_test_bit` / `read_dict_header` / `read_presence_header` /
  `dict_header_ok` / `presence_header_ok`.
- **DUPLICATE READER**: parallel implementation in OCaml that doesn't
  call F\*. Rule-#11 violation candidate.

Cross-reference each `Cottas_companion_*` function in extracted
`RDF_CottasStore.ml` against `RDF.CottasStore.OnDiskIndex.fst`. Where the
F\* version exists and OCaml reimplements it, report.

## 5-min plan

1. Read `RDF_CottasStore.ml` Cottas_companion_writer + Cottas_companion_boot
   sections.
2. Grep for direct mmap/byte reads (`Bigarray.Array1.unsafe_get`,
   `read_u32_le_int`, `read_u64_le_int`) outside the OnDiskIndex `Vav3_mmap`
   module — those are the smoking gun for "OCaml duplicates F\* reader".
3. Tabulate and emit recommendations.

(audit body to be expanded below)

## Audit table

(to be filled in)

## Recommendations for Phase 2.6

(to be filled in)

## Honest gaps

(to be filled in)
