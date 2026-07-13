(* subject_offsets_writer_roundtrip.ml — round-trip witness for the
   #100 follow-up (2026-07-13) .s.offsets companion-file writer.

   Pairs serialize_subject_offsets with parse_subject_offsets in
   formal/fstar/RDF.CottasStore.SubjectOffsetsWriter.fst. By
   construction the pair is a round-trip; this test asserts the
   equality empirically on representative fixtures and pins a SHA-256
   of the serialized bytes per fixture so format drift in the F*
   source surfaces as a CI failure instead of silently changing the
   on-disk byte layout that the `.s.offsets` reader
   (RDF.Store.Columnar.SubjectOffsetIndex) depends on.

   Same discipline as offsets_writer_roundtrip.ml (the `.p.offsets`
   sibling test). *)

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

let int_pairs_to_z_pairs xs = List.map (fun (a, b) -> (Z.of_int a, Z.of_int b)) xs
let z_pairs_to_int_pairs zs = List.map (fun (a, b) -> (Z.to_int a, Z.to_int b)) zs

let run_case ~name ~expected_hash
    ~num_subjects ~num_rows_total ~ranges =
  let bs =
    RDF_CottasStore_SubjectOffsetsWriter.serialize_subject_offsets
      (Z.of_int num_subjects) (Z.of_int num_rows_total)
      (int_pairs_to_z_pairs ranges)
  in
  let serialized = bytes_to_string bs in
  let actual_hash = sha256_hex serialized in
  Printf.printf "  HASH  %s sha256=%s len=%d\n"
    name actual_hash (String.length serialized);
  if expected_hash <> "" then begin
    check ~name:(name ^ " [hash]") (actual_hash = expected_hash);
    if actual_hash <> expected_hash then
      Printf.printf "    expected %s\n    actual   %s\n"
        expected_hash actual_hash
  end;
  match RDF_CottasStore_SubjectOffsetsWriter.parse_subject_offsets bs with
  | FStar_Pervasives_Native.None ->
    check ~name:(name ^ " [parse]") false
  | FStar_Pervasives_Native.Some (ns, nr, rs) ->
    check ~name:(name ^ " [parse]") true;
    check ~name:(name ^ " [num_subjects]") (Z.to_int ns = num_subjects);
    check ~name:(name ^ " [num_rows_total]") (Z.to_int nr = num_rows_total);
    check ~name:(name ^ " [ranges]") (z_pairs_to_int_pairs rs = ranges)

let () =
  Printf.printf "== subject_offsets_writer_roundtrip ==\n";
  (* Hashes pinned 2026-07-13 against the F* serializer in
     RDF.CottasStore.SubjectOffsetsWriter.fst. Format: 16-byte 'COTS'
     header + num_subjects * (u64_le start, u64_le end) ranges. *)
  let cases = [
    (* Empty corpus: zero subjects, zero rows. *)
    ("empty",
       0, 0,
       [],
       "184f8469b06228b26bbbd5a29868f5a2832b5444a9c6d31c34d5345e33aa3d06");
    (* One subject, one row: range [0, 1). *)
    ("singleton",
       1, 1,
       [(0, 1)],
       "df022a3363424bc23bc38d644ce39f07629723b5e97d08bf21c1712e941a81df");
    (* Three subjects, contiguous, matching the gene-corpus q3 fixture
       shape: wd:Q100085837 occupies rows [5, 8), flanked by other
       subjects' ranges. *)
    ("three-contiguous",
       3, 20,
       [(0, 5); (5, 8); (8, 20)],
       "23684857221d55b3eccc895a8beb2c481d7cf9d271098353209eea03f9ebf576");
    (* A subject spanning a row-group boundary (e.g. rows 122878..122882
       straddling an 8-row-group, 122880-rows-per-rg layout). *)
    ("rg-boundary-straddle",
       2, 200000,
       [(0, 122882); (122882, 200000)],
       "2d0cf97955489c1112f18cd50f8eb0e03fed75ac0c419b4164fda46db64af61f");
  ] in
  List.iter (fun (name, num_subjects, num_rows_total, ranges, hash) ->
    run_case ~name ~expected_hash:hash
      ~num_subjects ~num_rows_total ~ranges
  ) cases;
  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
