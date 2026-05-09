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
  (* Hashes pinned 2026-05-09 against the F* serializer in
     RDF.CottasStore.DictWriter.fst. Format: 32-byte 'COKD' header +
     ids[] (4*n) + token_offs[] (8*(n+1)) + token_data. Drift in
     either side will surface as a hash mismatch. *)
  let cases : (string * string list * string) list = [
    "empty",         [],
      "617ddd896d0bc888005f951633c104a8f46a746e878865b16692a35c96f0fd9a";
    "singleton",     ["alpha"],
      "914645e77b226e024e378472eb1877ab71dde4f971ebcedd55a5b569d11c3c62";
    "three-tokens",  ["alpha"; "beta"; "gamma"],
      "5e6a3a7d03f637d0088decb5556b2631eb1cf8305d665d6a05e33c29f1b49936";
    "ten-tokens",
      ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"],
      "81178eaf8dd38b0ab9ad758fbca35fe2b02f9d0b4464a10612dad61378adb539";
  ] in
  List.iter (fun (name, toks, hash) ->
    run_case ~name ~expected_hash:hash toks
  ) cases;
  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
