# Het3 — Parquet.Footer tail-recursion fix

**Branch:** `claude/main`
**Trigger:** Pe4 diagnosis at
`docs/designissues/2026-04-25-pe4-mim2-daemon-crash-investigation.md` —
worker-pthread (cohttp accept loop, 544 KB stack on macOS) blows on the very
first column decode of row-group 0 in `search_fast`. Native stack frame
trail names `camlParquet_Footer__sum_nat_list_3087` walking a ~120 894-entry
per-row-group lengths list.

## Confirmed bug

`Parquet.Footer.fst` line 1637:

```fstar
let rec sum_nat_list (xs:list nat) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | hd :: tl -> hd + sum_nat_list tl
```

`hd + (sum_nat_list tl)` is the textbook non-tail-rec body. Z.add wraps the
recursive call in a frame, ~120 k frames × ~128 B = ~15 MB stack — far past
544 KB pthread default → SIGBUS, daemon dies, no exception trail.

`sum_nat_list` is called twice per row-group decode in
`Parquet.Footer.fst` (lines 1709 + 2425) and once per Phase D RDF
materialise — every COTTAS-on-disk SELECT(COUNT(*)) hits it.

## Audit of other Pe4-named recursives

Pe4 explicitly flagged three more "candidates if Phase D moves them onto
the worker thread":

- `build_dlba_length_list` (line 1550) — already accumulator form
  (`acc' :: ... List.Tot.rev acc`). Tail-rec. No change needed.
- `decode_plain_dictionary_entries` (line 1960) — already accumulator
  form. Tail-rec. No change needed.
- `map_indices_to_dict` (line 2130) — already accumulator form.
  Tail-rec. No change needed.

Other large-list recursives in `Parquet.Footer.fst` cross-checked:

- `prefix_sums` (1628), `slice_all_dlba_values` (1737),
  `ascii_strings_of_hex_slices` (1761), `repeat_append` (2022),
  `decode_bit_packed_indices` (2031), `decode_hybrid_rle_runs` (2051),
  `list_rev_append` (2505), `collect_row_group_columns` (2519) — all
  accumulator pattern, tail-rec.
- `count_used_miniblocks` (1374) — non-tail (`succ_nat (recurse ...)`)
  but only ever called by itself; not on any per-row data path.
  Skip per spec ("don't bother with O(footer-size) recursions").
- `nth_field_hex` (363), `extract_ascii_strings_hex` (88) — fuel-
  bounded, footer / dictionary scope only. Skip.

Conclusion: `sum_nat_list` is the only stack risk on the per-row-data
hot path.

## Fix

Standard accumulator pattern, mechanical:

```fstar
let rec sum_nat_list_aux (xs:list nat) (acc:nat) : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | hd :: tl -> sum_nat_list_aux tl (acc + hd)

let sum_nat_list (xs:list nat) : Tot nat = sum_nat_list_aux xs 0
```

No `--lax`, no `assume_total`. Straight `Tot (decreases xs)`. Should
verify trivially.

## Acceptance plan (to be filled after build)

1. `make verify` Parquet.Footer + downstream — TBD
2. `./build-ocaml.sh extract` then `compile` — TBD
3. Restart `:3032` daemon on parliament COTTAS; smoke
   `SELECT (COUNT(*) AS ?n)` — must not crash, must return — TBD
4. `./bin/darwin-arm64/w3c_runner --all` — must stay 1657/1/0 — TBD

## Out of scope

- OCaml-side patch 95 mirror for `sum_nat_list` — Pe4 noted as a
  back-up; we want the F\* fix to land first.
- Phase D column-prune planner (Tsade2 commit `8a945f7` already in
  main).
- Mmap'd `assume val` primitives (Mim2 deferred).
