# Aleph5 — COTTAS-on-Parquet v1 spec scratch / reading log

Date: 2026-04-25
Goal: write `docs/cottas-format-v1.md` pinning the format we currently read.

## Reading list

- formal/fstar/Parquet.Footer.fst — F* reader (Yod3 miniblock fix, Resh RLE_DICT, Bet5 multi-rg)
- formal/fstar/experimental_ocaml_glue/cottas_runtime.sh — OCaml glue: column → s/p/o/g
- tools/ukparliament_trig_to_cottas.py — pycottas writer
- docs/designissues/cottas-native-backend.md — existing design notes
- tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas — real example (66 MB)
- formal/fstar/RDF.Graph.Executable.fst:331-345 — subject_to_key / term_to_key_opt

## Findings (filled in as I read)

(see commit; this scratch is just the trail)

## Constraints

- pure docs; no F*/OCaml/Python touched
- cite line numbers in F* reader for each spec claim
- claude/main, one commit
- final commit msg: `docs: COTTAS-on-Parquet v1 format spec (factoidal contract)`
