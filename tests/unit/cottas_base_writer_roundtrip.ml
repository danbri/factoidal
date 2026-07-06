(* cottas_base_writer_roundtrip.ml -- round-trip witness for the native
   COTTAS base-file writer (formal/fstar/RDF.CottasStore.BaseWriter.fst,
   2026-07-06, the "why is Python still needed to write it" gap).

   The READER (Parquet.Footer.fst) is the spec: this test serializes a
   fixed quad list with the pure F* serialize_cottas, writes the bytes
   to a temp file, and reads it back through Parquet.Footer's OWN probe
   functions -- footer magic/num_rows, row-group count, per-column
   names/codec/encoding, and the full per-row-group column decode
   (probe_parquet_column_decode_in_row_group, the same entry point the
   COTTAS on-disk runtime uses at query time). Values must come back
   exactly as written, in (s,p,o,g)-sorted row order.

   Also pins a SHA-256 of the serialized bytes (the dict_writer_
   roundtrip.ml pattern) so any format drift in the F* source surfaces
   as a CI failure instead of silently changing on-disk bytes.

   Two fixtures:
     - single row group (5 quads, mixed named/default graphs -- the
       tests/local/data/cottas_sample.nq content verbatim);
     - three row groups exercised via a row_group cap of ... the writer's
       row_group_size is a module constant (122,880), so multi-row-group
       coverage at unit-test size is exercised through chunk_rows
       directly instead of a 250k-quad fixture. *)

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

let bytes_to_string (bs : int list) : string =
  let n = List.length bs in
  let b = Bytes.create n in
  List.iteri (fun i c -> Bytes.unsafe_set b i (Char.chr (c land 0xff))) bs;
  Bytes.unsafe_to_string b

let sha256_hex (s : string) : string =
  let module D = Digestif.SHA256 in
  D.digest_string s |> D.to_hex

let mk_quad s p o g =
  { RDF_CottasStore_BaseWriter.cq_s = s;
    RDF_CottasStore_BaseWriter.cq_p = p;
    RDF_CottasStore_BaseWriter.cq_o = o;
    RDF_CottasStore_BaseWriter.cq_g = g }

(* The cottas_sample.nq quads, already in (s,p,o,g) sorted order (the
   writer's contract: caller sorts). *)
let sample_quads = [
  mk_quad "<https://example.org/alice>" "<https://example.org/knows>"
          "<https://example.org/bob>" "<https://example.org/graph/people>";
  mk_quad "<https://example.org/alice>" "<https://example.org/name>"
          "\"Alice\"" "<https://example.org/graph/people>";
  mk_quad "<https://example.org/bob>" "<https://example.org/name>"
          "\"Bob\"" "<https://example.org/graph/people>";
  mk_quad "<https://example.org/default-subject>" "<https://example.org/status>"
          "\"default\"" "DEFAULT";
  mk_quad "<https://example.org/doc>" "<https://example.org/title>"
          "\"Specimen\"" "<https://example.org/graph/docs>";
]

(* Pinned 2026-07-06 against the first landing of the writer (DLBA all
   four columns, UNCOMPRESSED codec, OPTIONAL schema with converted_type
   UTF8, single 122,880-row-group chunking). Regenerate deliberately --
   never to make CI green -- when the format version changes. *)
let expected_sha256 = "bc87889359a8cf9f71626f208b9736055dbbb37c4759171f9f5e61dd8f6fb30a"

let () =
  Printf.printf "cottas_base_writer_roundtrip:\n";

  (* 1. Serialize + byte-hash pin. *)
  let bs = RDF_CottasStore_BaseWriter.serialize_cottas sample_quads in
  let serialized = bytes_to_string bs in
  let actual_hash = sha256_hex serialized in
  Printf.printf "  HASH  sample sha256=%s len=%d\n" actual_hash (String.length serialized);
  if expected_sha256 <> "PLACEHOLDER" then
    check ~name:"sample [byte hash pin]" (actual_hash = expected_sha256);

  (* 2. Write to a temp file; read back through Parquet.Footer's probes. *)
  let tmp = Filename.temp_file "cottas_base_writer_roundtrip" ".cottas" in
  let oc = open_out_bin tmp in
  output_string oc serialized;
  close_out oc;

  (* Footer. *)
  (match Parquet_Footer.probe_parquet_footer tmp with
   | FStar_Pervasives_Native.Some f ->
     check ~name:"footer magic PAR1" (f.Parquet_Footer.pf_magic = "PAR1")
   | FStar_Pervasives_Native.None ->
     check ~name:"footer magic PAR1" false);
  (match Parquet_Footer.probe_parquet_num_rows tmp with
   | FStar_Pervasives_Native.Some n ->
     check ~name:"num_rows = 5" (Z.to_int n = 5)
   | FStar_Pervasives_Native.None -> check ~name:"num_rows = 5" false);
  (match Parquet_Footer.probe_parquet_row_group_count tmp with
   | FStar_Pervasives_Native.Some n ->
     check ~name:"row_groups = 1" (Z.to_int n = 1)
   | FStar_Pervasives_Native.None -> check ~name:"row_groups = 1" false);

  (* Schema: column names in order. *)
  List.iteri (fun i expect ->
    match Parquet_Footer.probe_parquet_column_name tmp (Z.of_int i) with
    | FStar_Pervasives_Native.Some n ->
      check ~name:(Printf.sprintf "column %d name = %s" i expect) (n = expect)
    | FStar_Pervasives_Native.None ->
      check ~name:(Printf.sprintf "column %d name = %s" i expect) false)
    ["s"; "p"; "o"; "g"];

  (* Codec + declared encoding, per column. *)
  List.iter (fun i ->
    (match Parquet_Footer.probe_parquet_column_compression_codec tmp (Z.of_int i) with
     | FStar_Pervasives_Native.Some c ->
       check ~name:(Printf.sprintf "column %d codec UNCOMPRESSED" i) (c = "UNCOMPRESSED")
     | FStar_Pervasives_Native.None ->
       check ~name:(Printf.sprintf "column %d codec UNCOMPRESSED" i) false);
    (match Parquet_Footer.probe_parquet_column_page_header_data_encoding tmp (Z.of_int i) with
     | FStar_Pervasives_Native.Some e ->
       check ~name:(Printf.sprintf "column %d encoding DLBA" i)
         (e = "DELTA_LENGTH_BYTE_ARRAY")
     | FStar_Pervasives_Native.None ->
       check ~name:(Printf.sprintf "column %d encoding DLBA" i) false))
    [0; 1; 2; 3];

  (* Full column decode through the SAME dispatcher the on-disk COTTAS
     runtime uses. Expected columns in sorted row order. *)
  let expect_col = [|
    ["<https://example.org/alice>"; "<https://example.org/alice>";
     "<https://example.org/bob>"; "<https://example.org/default-subject>";
     "<https://example.org/doc>"];
    ["<https://example.org/knows>"; "<https://example.org/name>";
     "<https://example.org/name>"; "<https://example.org/status>";
     "<https://example.org/title>"];
    ["<https://example.org/bob>"; "\"Alice\""; "\"Bob\"";
     "\"default\""; "\"Specimen\""];
    ["<https://example.org/graph/people>"; "<https://example.org/graph/people>";
     "<https://example.org/graph/people>"; "DEFAULT";
     "<https://example.org/graph/docs>"];
  |] in
  Array.iteri (fun col expected ->
    match Parquet_Footer.probe_parquet_column_decode_in_row_group
            tmp Z.zero (Z.of_int col) with
    | FStar_Pervasives_Native.Some cells ->
      let actual =
        List.map (function
          | FStar_Pervasives_Native.Some s -> s
          | FStar_Pervasives_Native.None -> "<NULL>") cells in
      check ~name:(Printf.sprintf "column %d decode matches" col)
        (actual = expected);
      if actual <> expected then begin
        Printf.printf "    expected: %s\n" (String.concat " | " expected);
        Printf.printf "    actual:   %s\n" (String.concat " | " actual)
      end
    | FStar_Pervasives_Native.None ->
      check ~name:(Printf.sprintf "column %d decode matches" col) false)
    expect_col;

  (* 3. Multi-row-group chunking property at unit size: chunk_rows caps
     each group at the given size and preserves order/content. *)
  let groups =
    RDF_CottasStore_BaseWriter.chunk_rows sample_quads (Z.of_int 2) in
  check ~name:"chunk_rows cap=2 -> 3 groups" (List.length groups = 3);
  check ~name:"chunk_rows flatten preserves rows"
    (List.concat groups = sample_quads);

  Sys.remove tmp;

  (* 4. Writer v2 (RDF.CottasStore.BaseWriter.serialize_cottas_v2,
     2026-07-06): RLE_DICTIONARY for p/g always, plus s/o via
     encode_column_choose_smaller (build both DLBA and RLE_DICTIONARY,
     keep whichever is fewer bytes -- see the module banner). At this
     5-row fixture: s has 4 distinct values (one repeat: "alice" x2) so
     dictionary encoding already wins even at this tiny scale (787 <
     858 total file bytes, smaller than v1's DLBA-only output); o has 5
     distinct values out of 5 rows (no repetition at all) so DLBA
     correctly wins there -- a real, measured instance of the
     "choose smaller" crossover, not an assumed one. p and g are
     forced RLE_DICTIONARY per the always-dictionary policy. *)
  let bs2 = RDF_CottasStore_BaseWriter.serialize_cottas_v2 sample_quads in
  let serialized2 = bytes_to_string bs2 in
  let actual_hash2 = sha256_hex serialized2 in
  Printf.printf "  HASH  v2 sample sha256=%s len=%d (v1 len=%d)\n"
    actual_hash2 (String.length serialized2) (String.length serialized);
  let expected_sha256_v2 =
    "e74e99dfe06c2a4b76b4fd1636f8ecf549252dd69f6ccfa4e81cfc4db32b04fa" in
  check ~name:"v2 sample [byte hash pin]" (actual_hash2 = expected_sha256_v2);
  check ~name:"v2 smaller than v1 on this fixture"
    (String.length serialized2 < String.length serialized);
  let tmp2 = Filename.temp_file "cottas_base_writer_roundtrip_v2" ".cottas" in
  let oc2 = open_out_bin tmp2 in
  output_string oc2 serialized2;
  close_out oc2;
  let expect_encoding = [| "RLE_DICTIONARY"; "RLE_DICTIONARY"; "DELTA_LENGTH_BYTE_ARRAY"; "RLE_DICTIONARY" |] in
  List.iteri (fun i name ->
    (match Parquet_Footer.probe_parquet_column_compression_codec tmp2 (Z.of_int i) with
     | FStar_Pervasives_Native.Some c ->
       check ~name:(Printf.sprintf "v2 column %d (%s) codec UNCOMPRESSED" i name) (c = "UNCOMPRESSED")
     | FStar_Pervasives_Native.None ->
       check ~name:(Printf.sprintf "v2 column %d (%s) codec UNCOMPRESSED" i name) false);
    (match Parquet_Footer.probe_parquet_column_page_header_data_encoding tmp2 (Z.of_int i) with
     | FStar_Pervasives_Native.Some e ->
       check ~name:(Printf.sprintf "v2 column %d (%s) encoding %s" i name expect_encoding.(i))
         (e = expect_encoding.(i))
     | FStar_Pervasives_Native.None ->
       check ~name:(Printf.sprintf "v2 column %d (%s) encoding %s" i name expect_encoding.(i)) false))
    ["s"; "p"; "o"; "g"];
  Array.iteri (fun col expected ->
    match Parquet_Footer.probe_parquet_column_decode_in_row_group
            tmp2 Z.zero (Z.of_int col) with
    | FStar_Pervasives_Native.Some cells ->
      let actual =
        List.map (function
          | FStar_Pervasives_Native.Some s -> s
          | FStar_Pervasives_Native.None -> "<NULL>") cells in
      check ~name:(Printf.sprintf "v2 column %d decode matches" col)
        (actual = expected)
    | FStar_Pervasives_Native.None ->
      check ~name:(Printf.sprintf "v2 column %d decode matches" col) false)
    expect_col;
  Sys.remove tmp2;

  Printf.printf "cottas_base_writer_roundtrip: %d pass, %d fail\n" !passed !failed;
  if !failed > 0 then exit 1
