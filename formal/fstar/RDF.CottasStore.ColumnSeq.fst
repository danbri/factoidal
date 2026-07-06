module RDF.CottasStore.ColumnSeq

// Phase 2.5a (issue #118) — array-shape column data for the COTTAS
// on-disk hot path.
//
// Why this exists: the existing F*-pure decoders in Parquet.Footer
// produce `list (option string)` for each row-group's column. For
// parliament's 122,880-row row groups, every walk of that list cons-
// cell-chases through the heap, allocating a new tail per filter
// iteration. The OCaml-side perf-shim (cottas_ondisk_runtime.sh)
// avoids this by working with `string option array` directly. To
// retire that shim (Phase 2.5e), F* needs a comparable shape.
//
// Approach (same pattern as RDF.CottasStore.PresenceBitmap.fst's
// bitmap_handle): an abstract type whose OCaml realisation is
// `string option array`, plus `assume val` accessors that do O(1)
// indexing. F* spec layer reasons about lengths and indices; the
// actual array bytes live in OCaml-side mmap or freshly-decoded
// arrays.
//
// What this module does NOT do: it does NOT modify any existing
// F* function (filter_zipped_rows, walk_row_groups_search, etc.) —
// they still consume the list shape. Phase 2.5b refactors them to
// consume the new shape; this commit just lands the foundation.

// ------------------------------------------------------------------
// Abstract type. Extracted by the OCaml realisation (in
// experimental_ocaml_glue/cottas_ondisk_column_seq_runtime.sh) as
// `string option array`. F* code never inspects the layout; it only
// uses the assume-val accessors below.
// ------------------------------------------------------------------

assume new type cottas_column : Type0

// ------------------------------------------------------------------
// Length. O(1). The OCaml realisation returns `Array.length arr`.
// ------------------------------------------------------------------

assume val cottas_column_length : cottas_column -> Tot nat

// ------------------------------------------------------------------
// Indexed accessor. O(1) array indexing in the OCaml realisation.
// The refinement `i < cottas_column_length c` ensures the F* spec
// statically rules out out-of-range access; the OCaml realisation
// can use `Array.unsafe_get` for the hot path with confidence the
// bound has already been checked at the F* layer.
// ------------------------------------------------------------------

assume val cottas_column_get :
  c:cottas_column ->
  i:nat{i < cottas_column_length c} ->
  Tot (option string)

// ------------------------------------------------------------------
// Decoder. Same I/O contract as
// Parquet.Footer.probe_parquet_column_decode_in_row_group, but
// returns the array-shape directly (no intermediate list).
//
// On success: the returned column has length = the row group's row
// count, with `cottas_column_get c i` returning the cell at row i
// of the column. On failure (bad path / unsupported encoding):
// returns None.
//
// The OCaml realisation reads the same parquet bytes the existing
// list-shape decoder reads; the only difference is the materialisation
// shape (Array.t vs list). This keeps the surface I/O semantics
// identical so the spec-side correctness lemmas in Phase 2.5b can
// rely on bridging the two shapes mechanically.
// ------------------------------------------------------------------

assume val probe_parquet_column_decode_in_row_group_seq :
  path:string ->
  rg_index:nat ->
  col_index:nat ->
  Tot (option cottas_column)

// ------------------------------------------------------------------
// Table-threaded sibling (issue #98/Mim3 follow-up, 2026-07-05): same
// contract as probe_parquet_column_decode_in_row_group_seq, but the
// row-group LOCATE step indexes into a precomputed
// `Parquet.Footer.parquet_row_group_offset_table` (built ONCE per
// query by the F* caller -- see plan_candidate_rgs /
// cottas_ondisk_search in RDF.CottasStore.fst) instead of
// skip-decoding every preceding row-group struct from scratch on
// every call. The OCaml realisation is the same mechanical
// Array.of_list coercion, over
// `Parquet_Footer.probe_parquet_column_decode_in_row_group_from_table`.
// The offsets themselves are computed in verified F*
// (`Parquet.Footer.probe_parquet_row_group_offset_table`) and only
// PASSED THROUGH this boundary, never computed or cached on the
// OCaml side (rule #11: the offsets are semantics; they live in F*).
// ------------------------------------------------------------------

assume val probe_parquet_column_decode_in_row_group_seq_from_table :
  table:Parquet.Footer.parquet_row_group_offset_table ->
  path:string ->
  rg_index:nat ->
  col_index:nat ->
  Tot (option cottas_column)

// ------------------------------------------------------------------
// Bridge functions for the transition period. These let Phase 2.5b
// refactor functions one at a time: a hot-path function can take the
// new shape and use either path until all callers have migrated.
//
// Both bridges are total. `column_to_list` walks i = 0..length-1 and
// builds a list; `column_of_list` is the inverse but goes through the
// list-shape decoder via probe_parquet (we don't add a list -> array
// realisation because callers should be migrating off list, not adding
// new list producers).
// ------------------------------------------------------------------

// Tail-recursive accumulator: walk indices in reverse, prepending each
// cell, then no flip is needed since we walked in reverse.
let rec column_to_list_acc (c:cottas_column) (i:nat) (acc:list (option string))
  : Tot (list (option string)) (decreases i) =
  if i = 0 then acc
  else
    let i' : nat = i - 1 in
    if i' < cottas_column_length c then
      let cell = cottas_column_get c i' in
      column_to_list_acc c i' (cell :: acc)
    else
      // Should not occur given the loop bound but keeps the function
      // total. The assume-val accessor's refinement requires the
      // strict bound; we drop the cell silently if anything ever
      // calls past length.
      column_to_list_acc c i' acc

// Materialise the column as a list, in row order (i=0 first).
let column_to_list (c:cottas_column) : Tot (list (option string)) =
  column_to_list_acc c (cottas_column_length c) []

// ------------------------------------------------------------------
// Identity / soundness lemma sketch (admitted body — to be discharged
// in Phase 2.5b alongside the refactor). The production-side
// correctness obligation is "the new array decoder produces the same
// cells as the existing list decoder for the same (path, rg, col)".
// We state it but don't try to prove it formally yet because the
// production side is OCaml glue.
// ------------------------------------------------------------------

// Spec-level: "the parquet bytes at (path, rg, col) decode to this
// list of cells (in row order)".
let parquet_decoded_cells_pred_t = string -> nat -> nat -> list (option string) -> Type0

// If `decoded path rg col cells` says the bytes decode to `cells`,
// AND the seq decoder returned `Some c`, AND `column_to_list c` equals
// `cells`, then the array decode is sound. We don't try to discharge
// the equivalence formally (it's a producer-side obligation about
// the OCaml realisation matching the F*-pure list decoder).
val column_decode_sound :
  decoded:parquet_decoded_cells_pred_t ->
  path:string -> rg:nat -> col:nat ->
  cells:list (option string) ->
  c:cottas_column ->
  Lemma
    (requires decoded path rg col cells /\
              probe_parquet_column_decode_in_row_group_seq path rg col == Some c /\
              column_to_list c == cells)
    (ensures decoded path rg col (column_to_list c))

let column_decode_sound decoded path rg col cells c = ()
