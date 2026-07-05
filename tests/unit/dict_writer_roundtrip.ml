(* dict_writer_roundtrip.ml — round-trip witness for #200 Section B
   .dict companion-file writer.

   serialize_dict and parse_dict in
   formal/fstar/RDF.CottasStore.DictWriter.fst are inverses by
   construction. This test asserts the equality empirically on
   representative fixtures and pins a SHA-256 of the serialized
   bytes for each fixture so format drift in the F* source surfaces
   as a CI failure (rather than silently changing the on-disk byte
   layout that downstream readers depend on).

   Per #200 Section B done-criterion: every companion-file writer
   gets a hash-based round-trip CI witness. This is the first.

   Promoting the empirical witness to a formal F* lemma
   `lemma_parse_serialize_dict : sorted_tokens -> Lemma (parse_dict
   (serialize_dict t) == Some t)` is tracked separately — the
   parse_dict docstring notes the deferral. *)

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
   (codepoints). For ASCII fixtures, codepoint = byte, so the
   serialized payload is byte-identical to what the OCaml writer
   atomic_writes to disk. *)
let bytes_to_string (bs : int list) : string =
  let n = List.length bs in
  let b = Bytes.create n in
  List.iteri (fun i c -> Bytes.unsafe_set b i (Char.chr (c land 0xff))) bs;
  Bytes.unsafe_to_string b

let sha256_hex (s : string) : string =
  let module D = Digestif.SHA256 in
  D.digest_string s |> D.to_hex

(* expected_hash = "" means: print actual, do not assert. Used for
   first-cut fixture generation; baked-in hashes assert format
   stability after the first commit. *)
let run_case ~name ~expected_hash tokens =
  let bs = RDF_CottasStore_DictWriter.serialize_dict tokens in
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
  match RDF_CottasStore_DictWriter.parse_dict bs with
  | None ->
    check ~name:(name ^ " [parse]") false
  | Some toks ->
    check ~name:(name ^ " [parse]") true;
    check ~name:(name ^ " [round-trip]") (toks = tokens)

let () =
  Printf.printf "== dict_writer_roundtrip ==\n";
  (* ASCII-only fixtures so F*'s codepoint-list matches the on-disk
     byte sequence verbatim. UTF-8 fixtures are valuable but require
     a tighter byte-vs-codepoint contract in RDF.Bytes; that's
     follow-up work. *)
  (* Hashes re-pinned 2026-07-05 against the F* serializer in
     RDF.CottasStore.DictWriter.fst after the dict_magic fix: the
     serializer's magic had drifted to 'COKD' (0x444b4f43) during the
     #200 PR2 byte-layout migration, while the reader/validator in
     RDF.CottasStore.OnDiskIndex.fst expects 'COTD' (0x44544f43) —
     so Cottas_companion_boot.companions_present_and_valid failed its
     header verify on every boot and rebuilt the four dict/presence
     sidecars unconditionally. Format: 32-byte 'COTD' header +
     ids[] (4*n) + token_offs[] (8*(n+1)) + token_data. Drift in
     either side will surface as a hash mismatch. *)
  let cases : (string * string list * string) list = [
    "empty",         [],
      "486401ad3679ae7b4daf49a768ad655bb9d642287b1dfa0b41c54f4ca62eca87";
    "singleton",     ["alpha"],
      "92ae5967933fd9d17749f04c7e519f5ddb4652e8ef0d188b988bb53885a2f919";
    "three-tokens",  ["alpha"; "beta"; "gamma"],
      "33eb82007018dc8c745ceea06e7ade30698c37497a05f29ae1dc02d90279ce40";
    "ten-tokens",
      ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"],
      "8d6a7366e328729db17776a78f6701d3a2046874f9b4ad07bd226f8c4c36dd82";
  ] in
  List.iter (fun (name, toks, hash) ->
    run_case ~name ~expected_hash:hash toks
  ) cases;
  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
