(* compound_presence_writer_roundtrip.ml — round-trip witness for #200
   Section B .po.presence companion-file writer.

   Pairs serialize_compound_presence with parse_compound_presence in
   formal/fstar/RDF.CottasStore.CompoundPresenceWriter.fst. By
   construction the pair is a round-trip; this test asserts the
   equality empirically on representative fixtures and pins a SHA-256
   of the serialized bytes per fixture so format drift in the F* source
   surfaces as a CI failure instead of silently changing the on-disk
   byte layout that the .po.presence reader
   (RDF.CottasStore.CompoundPresenceBitmap) depends on.

   Per #200 Section B done-criterion: every companion-file writer gets
   a hash-based round-trip CI witness. PR3 after PR2 (PresenceWriter,
   2026-05-10).

   Promoting the empirical witness to a formal F* lemma
   `lemma_parse_serialize_compound_presence` is tracked separately. *)

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

(* F*'s `bytes = list FStar.Char.char` extracts to OCaml as `int list`
   (codepoints). Our fixtures use only small u64 values whose bytes are
   < 128 so codepoint = byte and the serialized payload is byte-
   identical to what the OCaml writer atomic_writes to disk. *)
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

(* expected_hash = "" means: print actual, do not assert. Used for
   first-cut fixture generation; baked-in hashes assert format
   stability after the first commit. *)
let run_case ~name ~expected_hash
    ~num_rgs ~pred_size ~obj_size ~rg_offsets ~pairs =
  let bs =
    RDF_CottasStore_CompoundPresenceWriter.serialize_compound_presence
      (Z.of_int num_rgs) (Z.of_int pred_size) (Z.of_int obj_size)
      (int_list_to_z_list rg_offsets)
      (int_list_to_z_list pairs)
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
  match
    RDF_CottasStore_CompoundPresenceWriter.parse_compound_presence bs
  with
  | FStar_Pervasives_Native.None ->
    check ~name:(name ^ " [parse]") false
  | FStar_Pervasives_Native.Some (rgs, ps, os, offs, pps) ->
    check ~name:(name ^ " [parse]") true;
    check ~name:(name ^ " [rgs]")     (Z.to_int rgs = num_rgs);
    check ~name:(name ^ " [pred]")    (Z.to_int ps = pred_size);
    check ~name:(name ^ " [obj]")     (Z.to_int os = obj_size);
    check ~name:(name ^ " [offsets]") (z_list_to_int_list offs = rg_offsets);
    check ~name:(name ^ " [pairs]")   (z_list_to_int_list pps = pairs)

let () =
  Printf.printf "== compound_presence_writer_roundtrip ==\n";
  (* Hashes pinned 2026-05-10 against the F* serializer in
     RDF.CottasStore.CompoundPresenceWriter.fst. Format: 20-byte 'COPO'
     header + (num_rgs+1) u64_le rg_offsets + total_pairs u64_le pairs. *)
  let cases = [
    (* Empty: zero rgs, zero pred/obj dicts. rg_offsets has a single
       sentinel entry [0]. *)
    ("empty",
       0, 0, 0,
       [0], [],
       "42282876f447080fc15bceb20937c388bb61977d69c765fbdd82e02a2a6f086c");
    (* Singleton: 1 rg, 1 pred, 1 obj, one pair. *)
    ("singleton",
       1, 1, 1,
       [0; 1],
       [0],
       "a6c5b8fd4900cd372543f68b18a1b548931030354d7bebc9fc1ec8b1fa3fd527");
    (* 2 rgs × 3 preds × 4 objs, two pairs in rg0, three in rg1. *)
    ("2x3x4-mixed",
       2, 3, 4,
       [0; 2; 5],
       [0; 7; 1; 5; 11],
       "7804392f35d9005ca228894d199cf610960d8f3270e841c1dba60184003c2e3a");
    (* 4 rgs, sparse: rg0 has 1 pair, rg1 empty, rg2 has 2, rg3 has 1. *)
    ("4-sparse",
       4, 5, 5,
       [0; 1; 1; 3; 4],
       [0; 7; 14; 21],
       "9c96f62ba26d77237b06eb22ba092a4a33a0bb96b252652904cd70fc8b839aa1");
  ] in
  List.iter (fun (name, num_rgs, pred_size, obj_size, offs, pps, hash) ->
    run_case ~name ~expected_hash:hash
      ~num_rgs ~pred_size ~obj_size ~rg_offsets:offs ~pairs:pps
  ) cases;
  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
