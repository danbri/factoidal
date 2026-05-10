(* offsets_writer_roundtrip.ml — round-trip witness for #200 Section B
   .p.offsets companion-file writer.

   Pairs serialize_offsets with parse_offsets in
   formal/fstar/RDF.CottasStore.OffsetsWriter.fst. By construction the
   pair is a round-trip; this test asserts the equality empirically on
   representative fixtures and pins a SHA-256 of the serialized bytes
   per fixture so format drift in the F* source surfaces as a CI
   failure instead of silently changing the on-disk byte layout that
   the .p.offsets reader (RDF.Store.Columnar.OffsetIndex) depends on.

   Per #200 Section B done-criterion: every companion-file writer gets
   a hash-based round-trip CI witness. PR4 after PR3
   (CompoundPresenceWriter, 2026-05-10).

   Promoting the empirical witness to a formal F* lemma
   `lemma_parse_serialize_offsets` is tracked separately. *)

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

let int_list_to_z_list xs = List.map Z.of_int xs
let z_list_to_int_list zs = List.map Z.to_int zs

let run_case ~name ~expected_hash
    ~num_rgs ~num_preds ~rg_offsets ~subject_ids =
  let bs =
    RDF_CottasStore_OffsetsWriter.serialize_offsets
      (Z.of_int num_rgs) (Z.of_int num_preds)
      (int_list_to_z_list rg_offsets)
      (int_list_to_z_list subject_ids)
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
  match RDF_CottasStore_OffsetsWriter.parse_offsets bs with
  | FStar_Pervasives_Native.None ->
    check ~name:(name ^ " [parse]") false
  | FStar_Pervasives_Native.Some (rgs, preds, offs, subjs) ->
    check ~name:(name ^ " [parse]") true;
    check ~name:(name ^ " [rgs]")     (Z.to_int rgs = num_rgs);
    check ~name:(name ^ " [preds]")   (Z.to_int preds = num_preds);
    check ~name:(name ^ " [offsets]") (z_list_to_int_list offs = rg_offsets);
    check ~name:(name ^ " [subjs]")   (z_list_to_int_list subjs = subject_ids)

let () =
  Printf.printf "== offsets_writer_roundtrip ==\n";
  (* Hashes pinned 2026-05-10 against the F* serializer in
     RDF.CottasStore.OffsetsWriter.fst. Format: 16-byte 'COTO' header +
     (num_rgs*num_preds+1) u64_le rg_offsets + total_subjs u32_le
     subject_ids. *)
  let cases = [
    (* Empty: zero rgs and zero preds. rg_offsets is the single
       sentinel [0]. *)
    ("empty",
       0, 0,
       [0], [],
       "622d6bd71bb898ecfb1347b6ff254d670df048ca32fc575945980df8e843af99");
    (* 1 rg × 1 pred, one subject id. *)
    ("singleton",
       1, 1,
       [0; 1],
       [42],
       "9ef8d841d0a988f29f3d013ce33454540f8d815b337b2b9d711b12596c599b3d");
    (* 2 rgs × 3 preds, six (rg, pred) buckets, each with 0–2 subjs. *)
    ("2x3-mixed",
       2, 3,
       [0; 2; 2; 3; 4; 6; 7],
       [10; 20; 30; 40; 50; 60; 70],
       "4bed0db9a36b0f44ccbedf1a76b9bb7480c89256e5726ad049603e8b46f3c23e");
    (* 3 rgs × 2 preds, sparse: most buckets empty. *)
    ("3x2-sparse",
       3, 2,
       [0; 0; 1; 1; 1; 1; 3],
       [99; 100; 200],
       "c094e6661688ef48f77efbfadfb2c4a2da42d2ce5fd656f69865f5fc04b5da49");
  ] in
  List.iter (fun (name, num_rgs, num_preds, offs, subjs, hash) ->
    run_case ~name ~expected_hash:hash
      ~num_rgs ~num_preds ~rg_offsets:offs ~subject_ids:subjs
  ) cases;
  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
