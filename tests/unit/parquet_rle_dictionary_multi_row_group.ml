(* parquet_rle_dictionary_multi_row_group.ml -- regression pin for issue
   #98 (reopened 2026-07-05): the on-disk COTTAS/Parquet reader must
   correctly decode RLE_DICTIONARY-encoded columns across every row
   group, not just the first.

   Root cause (see docs/designissues/2026-07-05-disk-backed-db-perf-review.md
   roadmap item 1 and Parquet.Footer.fst's bug-history comments):

     1. `probe_parquet_column_dictionary_page_offset[_in_row_group]` read
        Thrift field 14 (`bloom_filter_offset`) instead of field 11
        (`dictionary_page_offset`) off `ColumnMetaData`. DuckDB/pycottas
        write a bloom filter after the data pages by default, so field 14
        usually *was* present and looked like a valid offset -- but it
        pointed at bloom-filter bytes, not a dictionary page header, so
        decompression failed and the column read as undecodable.

     2. Every column DuckDB/pycottas emits is Parquet-schema OPTIONAL
        (confirmed via `parquet_schema()`; SQL `NOT NULL` on s/p/o is not
        propagated to the Parquet REQUIRED repetition type), so every
        data page opens with a definition-level run: a 4-byte LE
        byte-length, then that many bytes of RLE-encoded levels, BEFORE
        the actual value bytes. The DLBA decoder already skipped this
        (`..._values_offset[_in_row_group]`); the RLE_DICTIONARY decoder
        did not, so it silently misread definition-level bytes as the
        dictionary bit-width + index stream. On some columns this still
        produced a decode of the *right length* -- a silent wrong answer,
        not a loud failure -- observed on medication.cottas's predicate
        column (3-bit dictionary) before the fix.

   Fixture: tests/unit/fixtures/parquet_rle_dictionary_multi_rg.cottas,
   4,100 quads / 3 row groups (2048, 2048, 4), built by DuckDB with
   PARQUET_VERSION v2 + DICTIONARY_SIZE_LIMIT 4 so p/g are
   RLE_DICTIONARY in every row group and o adaptively switches from
   DELTA_LENGTH_BYTE_ARRAY (row groups 0-1, 2048 distinct values each)
   to RLE_DICTIONARY (row group 2, only 4 rows / 4 distinct values) --
   the same adaptive-encoding shape the perf review measured on
   gene.cottas. Row i (0-indexed, row order = insertion order): s =
   "http://ex.org/s<i mod 4>", p = "http://ex.org/p<i mod 3>", o =
   "lit<i>" (unique per row), g cycles gA / gB / DEFAULT every 3 rows.
   Built via a direct DuckDB `INSERT` (not through
   tools/corpus_pipeline.py), so cell values are bare strings, NOT
   N-Quads-token-wrapped (no `<...>` / `"..."` the way real pycottas
   output stores them) -- irrelevant here since this fixture pins
   byte-level Parquet decode mechanics (row-group walk, dictionary-page
   field number, definition-level skip), which do not care what string
   content is inside a cell. Rebuild with tools/../scratchpad
   make_fixture.py-equivalent logic if the shape ever needs to change;
   do not hand-edit the binary. *)

let passed = ref 0
let failed = ref 0

let check ~name ok =
  if ok then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

(* Matches the convention in tests/unit/lifesci_closure_timing.ml etc.:
   a repo-root-relative path. run-all.sh (and any manual invocation of
   the compiled test binary) is expected to run with cwd = repo root. *)
let fixture_dir = "tests/unit/fixtures"

let fixture_path = Filename.concat fixture_dir "parquet_rle_dictionary_multi_rg.cottas"
let truncated_path = Filename.concat fixture_dir "parquet_rle_dictionary_multi_rg.truncated.cottas"

(* Second, single-row-group fixture pinning a DISTINCT bug from the same
   #98-reopened investigation: the per-row-group and whole-column
   dispatchers used to "try DELTA_LENGTH_BYTE_ARRAY first, and if it
   returns Some at all, use it" before falling back to RLE_DICTIONARY.
   That try-then-fallback shape is unsound -- the DLBA parser has no
   encoding discriminator of its own, so pointed at RLE_DICTIONARY bytes
   it can walk the generic varint header fields and land on an
   internally-consistent-looking small/zero value_count, returning
   `Some []` (or `Some` of a wrong-length list) instead of `None`. `Some
   []` is indistinguishable from "this column has zero rows" to every
   caller upstream -- a silent wrong answer, not a decode failure. This
   is exactly the shape of the g21-fixture "silent COUNT=0" bug the perf
   review recorded: 818 real quads, a genuinely RLE_DICTIONARY-encoded
   named-graph column, decoding to zero rows through the OLD dispatcher
   even though every individual RLE_DICTIONARY primitive worked in
   isolation. Fixed by dispatching on the page header's OWN declared
   encoding instead of a try/fallback.

   parquet_rle_dictionary_named_graph_column.cottas: 818 quads, 1 row
   group, g column RLE_DICTIONARY with exactly 2 distinct named graphs
   (no default-graph rows at all -- this is what made the pre-fix bug
   reproduce reliably: an all-named-graph column with nothing to fall
   back on). Source data: s cycles "http://ex.org/s<i mod 200>", p
   cycles "http://ex.org/p<i mod 5>", o = "val<i>" (unique per row), g
   cycles gA/gB every other quad -- but DuckDB's on-disk physical row
   order does not preserve insertion order for this table (see
   `ng_expected_g` below), so point-lookup expectations are pinned from
   an observed `parquet_scan` read, not derived from the source formula. *)
let ng_fixture_path = Filename.concat fixture_dir "parquet_rle_dictionary_named_graph_column.cottas"
let ng_expected_n = 818
(* DuckDB's on-disk physical row order for this table does not match
   source insertion order (internal chunking/threading during the
   CREATE TABLE + executemany + COPY pipeline reorders rows) -- these
   are the actual decoded values at each sampled index, read once via
   `SELECT s,p,o,g FROM parquet_scan(...)` at fixture-build time and
   pinned here as ground truth, not derived from a formula. *)
let ng_expected_g = function
  | 0 | 1 | 2 | 3 | 408 | 409 -> "<http://ex.org/gA>"
  | 816 | 817 -> "<http://ex.org/gB>"
  | i -> failwith (Printf.sprintf "ng_expected_g: no pinned value for row %d" i)

let opt_get name = function
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None ->
    check ~name:(name ^ " [must decode]") false;
    failwith (name ^ ": decode returned None, aborting test")

let expected_n = 4100

let expected_s i = Printf.sprintf "http://ex.org/s%d" (i mod 4)
let expected_p i = Printf.sprintf "http://ex.org/p%d" (i mod 3)
let expected_o i = Printf.sprintf "lit%d" i
let expected_g i = match i mod 3 with
  | 0 -> "http://ex.org/gA"
  | 1 -> "http://ex.org/gB"
  | _ -> "DEFAULT"

let string_of_cell = function
  | FStar_Pervasives_Native.Some s -> s
  | FStar_Pervasives_Native.None -> "<NONE-CELL>"

let () =
  Printf.printf "== parquet_rle_dictionary_multi_row_group ==\n";
  Printf.printf "  fixture: %s\n%!" fixture_path;

  if not (Sys.file_exists fixture_path) then begin
    Printf.printf "  FAIL  fixture missing at %s\n" fixture_path;
    Printf.printf "== summary: 0 pass, 1 fail (out of 1) ==\n";
    exit 1
  end;

  (* 1. Multi-row-group shape sanity. *)
  let rg_count =
    opt_get "row_group_count" (Parquet_Footer.probe_parquet_row_group_count fixture_path) in
  check ~name:"row_group_count = 3" (Z.to_int rg_count = 3);

  (* 2. Every column decodes across ALL row groups, with the right total
     row count -- this is the #98 Gap B assertion (multi-row-group). *)
  let decode_col col_index =
    opt_get (Printf.sprintf "decode column %d" col_index)
      (Parquet_Footer.probe_parquet_column_decode_all_row_groups fixture_path (Z.of_int col_index))
  in
  let s_col = decode_col 0 in
  let p_col = decode_col 1 in
  let o_col = decode_col 2 in
  let g_col = decode_col 3 in
  check ~name:"s column row count" (List.length s_col = expected_n);
  check ~name:"p column row count" (List.length p_col = expected_n);
  check ~name:"o column row count" (List.length o_col = expected_n);
  check ~name:"g column row count" (List.length g_col = expected_n);

  (* 3. Point-lookup rows: check a sample spanning all three row groups
     (including the tiny 4-row trailing group where o adaptively
     switches from DLBA to RLE_DICTIONARY) decode to the exact expected
     strings -- this is the #98 Gap A assertion (RLE_DICTIONARY value
     correctness), not just "some string came out." *)
  let sample_indices = [0; 1; 2; 2047; 2048; 2049; 4095; 4096; 4098; 4099] in
  List.iter (fun i ->
    let s = string_of_cell (List.nth s_col i) in
    let p = string_of_cell (List.nth p_col i) in
    let o = string_of_cell (List.nth o_col i) in
    let g = string_of_cell (List.nth g_col i) in
    check ~name:(Printf.sprintf "row %d s" i) (s = expected_s i);
    check ~name:(Printf.sprintf "row %d p" i) (p = expected_p i);
    check ~name:(Printf.sprintf "row %d o" i) (o = expected_o i);
    check ~name:(Printf.sprintf "row %d g" i) (g = expected_g i)
  ) sample_indices;

  (* 4. Distinct-value counts: p and g must resolve through the
     dictionary to exactly the low-cardinality set (3 each), not a
     misaligned/garbage superset. *)
  let distinct_count col =
    let tbl = Hashtbl.create 16 in
    List.iter (fun c -> Hashtbl.replace tbl (string_of_cell c) ()) col;
    Hashtbl.length tbl
  in
  check ~name:"p distinct = 3" (distinct_count p_col = 3);
  check ~name:"g distinct = 3" (distinct_count g_col = 3);
  check ~name:"s distinct = 4" (distinct_count s_col = 4);
  check ~name:"o distinct = 4100 (all unique)" (distinct_count o_col = expected_n);

  (* 5. Loud failure on a corrupt/truncated variant: a store that cannot
     be decoded must come back None, never a plausible-but-wrong answer
     (CLAUDE.md: silent wrong answers are the priority failure mode,
     worse than a hard error). The truncated file cuts the last row
     group's data pages off mid-file. *)
  if not (Sys.file_exists truncated_path) then
    check ~name:"truncated fixture present" false
  else begin
    (match Parquet_Footer.probe_parquet_column_decode_all_row_groups
             truncated_path (Z.of_int 3) with
     | FStar_Pervasives_Native.None ->
       check ~name:"truncated file: g column decode fails loudly (None)" true
     | FStar_Pervasives_Native.Some lst ->
       (* Acceptable alternate loud-failure shape: decoding succeeds in
          length but must not silently agree with the untruncated file's
          row count -- a length match here would mean the reader is
          fabricating rows past EOF, which is the silent-wrong-answer
          failure this test exists to catch. *)
       check ~name:"truncated file: g column must not silently match full row count"
         (List.length lst <> expected_n))
  end;

  (* 6. The second fixture: single-row-group, all-named-graph,
     RLE_DICTIONARY graph column -- pins the encoding-based-dispatch fix
     directly, since the multi-row-group fixture above happened not to
     trigger the old try/fallback dispatcher's spurious-empty-decode bug
     (byte-content-dependent; this fixture is the one that reliably did). *)
  if not (Sys.file_exists ng_fixture_path) then
    check ~name:"named-graph-column fixture present" false
  else begin
    let ng_rg_count =
      opt_get "ng row_group_count"
        (Parquet_Footer.probe_parquet_row_group_count ng_fixture_path) in
    check ~name:"ng row_group_count = 1" (Z.to_int ng_rg_count = 1);

    let ng_g_col =
      opt_get "ng decode g column"
        (Parquet_Footer.probe_parquet_column_decode_all_row_groups
           ng_fixture_path (Z.of_int 3)) in
    check ~name:"ng g column row count = 818 (not silently 0)"
      (List.length ng_g_col = ng_expected_n);
    check ~name:"ng g distinct = 2" (distinct_count ng_g_col = 2);
    List.iter (fun i ->
      let g = string_of_cell (List.nth ng_g_col i) in
      check ~name:(Printf.sprintf "ng row %d g" i) (g = ng_expected_g i)
    ) [0; 1; 2; 3; 408; 409; 816; 817]
  end;

  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
