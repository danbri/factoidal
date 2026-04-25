# Resh3 — issue #100 Phase A: lift 11 cottas_ondisk lookup fns to F\*

Date: 2026-04-25
Branch: `claude/main`
Issue: [#100](https://github.com/danbri/factoidal/issues/100)

## Goal

Per CLAUDE.md rules #1 / #7 / #15 + memory `feedback_fstar_first_always.md`,
encoding/decoding/index logic must live in F\*. `assume val` is reserved
for genuine I/O primitives. This commit replaces 11 of the 13
`cottas_ondisk_*` `assume val`s with real F\* definitions and renames the
on-disk module from `Parser.BallyhooCOTTAS` to `RDF.CottasStore`.

## What stays in OCaml glue (Phase B/C scope)

| Function | Why |
|---|---|
| `cottas_ondisk_open` | I/O: opens Parquet file via `Parquet_Footer.probe_*`, decodes 4 columns, materialises arrays. Phase C will refactor with mmap. |
| `cottas_ondisk_close` | I/O: not currently extracted by F\* (no use site). |
| `cottas_ondisk_search` | Performance: walks per-row `int array`s in tight `for`-loops. Phase B redesigns with row-group iteration / page streaming and the API shape may shift; lifting now then re-lifting is wasted. |
| `cottas_ondisk_estimate` | Same as search — same loop kernel. Phase B will share the iterator. |

## What moves to F\* in this commit

The 11 `assume val`s replaced with `Tot` definitions:

| Function | Body |
|---|---|
| `cottas_ondisk_summary` | Read the `cods_summary` field from the store record. |
| `cottas_ondisk_encode_subject` | `bucket_lookup` over the store's subject reverse map. |
| `cottas_ondisk_encode_predicate` | `bucket_lookup` over predicate reverse map. |
| `cottas_ondisk_encode_object` | `bucket_lookup` over object reverse map. |
| `cottas_ondisk_encode_graph` | `bucket_lookup` over graph reverse map. |
| `cottas_ondisk_decode_subject` | `nth_or` over subject distinct-strings list (parsed). |
| `cottas_ondisk_decode_predicate` | `nth_or` over predicate distinct-strings list (parsed). |
| `cottas_ondisk_decode_object` | `nth_or` over object distinct-strings list (parsed). |
| `cottas_ondisk_decode_graph_name` | `nth_or` over graph distinct-strings list (parsed). |
| `cottas_ondisk_predicate_present` | encode the predicate, then `bucket_lookup` for non-empty. |
| `cottas_ondisk_named_graphs` | Walk the parsed graph distinct-iri list, attach 0..n term-refs. |

## Module layout

`Parser.BallyhooCOTTAS.fst` keeps:
- `cottas_dataset_store` (older eager-load path, untouched)
- `cottas_open_dataset_store`, `cottas_search`, etc. (untouched)
- The shared `cottas_term_ref`, `cottas_graph_ref`, `cottas_bound_qp`,
  `cottas_qp_row` types — exported, since `RDF.CottasStore` re-exports.

`RDF.CottasStore.fst` (NEW) gets:
- `cottas_ondisk_handle` — but enriched: instead of an opaque `assume type`,
  we make it a record holding parsed dictionaries + decoded distinct-string
  lists. The OCaml glue produces this record at open() time.
- `cottas_ondisk_store` — wraps the handle.
- The 11 functions above as `Tot` F\* code.
- The 2 remaining `assume val`s (`cottas_ondisk_open`, `cottas_ondisk_search`,
  `cottas_ondisk_estimate`).

## Handle shape

The new on-disk handle moves from `assume type cottas_ondisk_handle` to a
real F\* record. Open() builds it once, lookups read from it. The OCaml
glue's `ondisk_handle` (`s_ids`/`p_ids`/etc. mutable hashtables) becomes
purely Phase B / C scope (search + page streaming). The handle exposes:

```fstar
noeq type cottas_ondisk_handle = {
  coh_path : string;
  coh_summary : option cottas_artifact_summary;
  // Distinct-term inventories per column. Subject/object/graph use the
  // already-parsed RDF terms; predicate uses already-parsed wf_iri. The
  // index in the list IS the term-id (as stored in the per-row int arrays).
  coh_subjects   : list subject;
  coh_predicates : list wf_iri;
  coh_objects    : list rdf_term;
  coh_graphs     : list iri;
  // Reverse maps: bucket_map keyed by canonical subject/object/iri key
  // → 1-element list of the int term-id (positive int wrapped as nat).
  coh_subj_revmap  : list (string * nat);
  coh_pred_revmap  : list (string * nat);
  coh_obj_revmap   : list (string * nat);
  coh_graph_revmap : list (string * nat);
  // Reference to the OCaml-side mutable arrays for the per-row int columns.
  // Kept opaque for Phase B/C: `cottas_ondisk_search` and
  // `cottas_ondisk_estimate` are still I/O — they unwrap this and walk
  // the int arrays. F* doesn't need to see inside.
  coh_columns : columns_handle;
}
assume type columns_handle
```

This is the Phase A shape. Phase B will replace `coh_columns` with an
F\*-side iterator + page descriptor; the four arrays move into a typed
`option int -> Tot (list quad_row)` interface.

## Patch surface

`experimental_ocaml_glue/cottas_ondisk_runtime.sh`: 11 of the
`failwith` → real-OCaml replacements are removed (they're now F\*-defined,
extraction produces real code, no `failwith` to replace).
`cottas_ondisk_open` keeps its OCaml body; it builds the new richer handle
record (with `coh_subjects`, `coh_predicates`, etc. lists +
`coh_*_revmap` bucket-lists) on top of the existing column-decoding
machinery. `cottas_ondisk_search` / `cottas_ondisk_estimate` continue to
unwrap `coh_columns : columns_handle` via `Obj.magic` — Phase B replaces
this.

Net OCaml deletion: ~250 LoC (the 11 stubs + their plumbing). The
column-decoding helpers + `search_rows` / `count_rows` stay (Phase B).

## SPARQL11.Store import

```fstar
- open Parser.BallyhooCOTTAS
+ open Parser.BallyhooCOTTAS  // for cottas_dataset_store still
+ open RDF.CottasStore        // for cottas_ondisk_*
```

`GB_CottasOnDisk : cottas_ondisk_store -> ...` still resolves; the type
moved modules but is in scope via the `open RDF.CottasStore`.

## Acceptance

1. `make verify` clean for `RDF.CottasStore`, `Parser.BallyhooCOTTAS`,
   `SPARQL11.Store`, `Parquet.Footer`.
2. `./build-ocaml.sh extract` clean.
3. `./build-ocaml.sh compile` clean.
4. Daemon smoke: kill any running `factoidal-http`, restart with
   `--data-cottas`, confirm `[qof3-trace]` lines still appear and the
   handle opens. Crash on first query is the known Phase B/C boundary.

## Out of scope

- Mmap (Phase C).
- Lazy search / page streaming (Phase B).
- Column-prune planner (Phase D).
- The post-search crash root-cause (separate; Phase B redesign should
  make it moot).
