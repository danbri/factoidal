(* presence_writer_roundtrip.ml — round-trip witness for #200 Section B
   .presence companion-file writer.

   Pairs serialize_presence with parse_presence in
   formal/fstar/RDF.CottasStore.PresenceWriter.fst. By construction the
   pair is a round-trip; this test asserts the equality empirically on
   representative fixtures and pins a SHA-256 of the serialized bytes
   per fixture so format drift in the F* source surfaces as a CI
   failure instead of silently changing the on-disk byte layout that
   the .presence reader (RDF.CottasStore.PresenceBitmap) depends on.

   Per #200 Section B done-criterion: every companion-file writer gets
   a hash-based round-trip CI witness. PresenceWriter is the second
   (after DictWriter, 2026-05-09).

   Promoting the empirical witness to a formal F* lemma
   `lemma_parse_serialize_presence` is tracked separately. *)

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
   (codepoints). For our bitmap fixtures every byte value is < 128 so
   codepoint = byte and the serialized payload is byte-identical to the
   on-disk .presence file the OCaml writer produces. *)
let bytes_to_string (bs : int list) : string =
  let n = List.length bs in
  let b = Bytes.create n in
  List.iteri (fun i c -> Bytes.unsafe_set b i (Char.chr (c land 0xff))) bs;
  Bytes.unsafe_to_string b

let string_to_int_list (s : string) : int list =
  let n = String.length s in
  let rec loop i acc =
    if i < 0 then acc
    else loop (i - 1) (Char.code s.[i] :: acc)
  in
  loop (n - 1) []

let sha256_hex (s : string) : string =
  let module D = Digestif.SHA256 in
  D.digest_string s |> D.to_hex

(* Build a bitmap of `bits` bits, with set positions given by `set`.
   Row-major bit (rg*num_tokens + tok); same indexing as
   RDF.CottasStore.PresenceBitmap. *)
let make_bitmap ~bits ~set =
  let bytes = (bits + 7) / 8 in
  let b = Bytes.make bytes '\000' in
  List.iter (fun bit_index ->
    let byte_index = bit_index / 8 in
    let bit_in_byte = bit_index mod 8 in
    let cur = Char.code (Bytes.unsafe_get b byte_index) in
    Bytes.unsafe_set b byte_index
      (Char.chr (cur lor (1 lsl bit_in_byte)))
  ) set;
  Bytes.unsafe_to_string b

(* expected_hash = "" means: print actual, do not assert. Used for
   first-cut fixture generation; baked-in hashes assert format
   stability after the first commit. *)
let run_case ~name ~expected_hash ~num_rgs ~num_tokens ~bitmap_str =
  let bitmap_ints = string_to_int_list bitmap_str in
  let bs =
    RDF_CottasStore_PresenceWriter.serialize_presence
      (Z.of_int num_rgs) (Z.of_int num_tokens) bitmap_ints
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
  match RDF_CottasStore_PresenceWriter.parse_presence bs with
  | FStar_Pervasives_Native.None ->
    check ~name:(name ^ " [parse]") false
  | FStar_Pervasives_Native.Some (rgs, toks, bm) ->
    check ~name:(name ^ " [parse]") true;
    check ~name:(name ^ " [round-trip rgs]")
      (Z.to_int rgs = num_rgs);
    check ~name:(name ^ " [round-trip toks]")
      (Z.to_int toks = num_tokens);
    check ~name:(name ^ " [round-trip bitmap]")
      (bm = bitmap_ints)

let () =
  Printf.printf "== presence_writer_roundtrip ==\n";
  (* Hashes pinned 2026-05-10 against the F* serializer in
     RDF.CottasStore.PresenceWriter.fst. Format: 16-byte 'COTP' header
     + ceil(num_rgs * num_tokens / 8) bitmap bytes, row-major. *)
  let cases = [
    (* Empty: 0 rgs, 0 tokens. *)
    ("empty", 0, 0, make_bitmap ~bits:0 ~set:[],
       "2a81f78f8dc918586126c51f2a3e0bb3095a221626502dffe247875c4a0c8514");
    (* Singleton: 1 rg × 1 token, bit set. *)
    ("singleton-set", 1, 1, make_bitmap ~bits:1 ~set:[0],
       "1d3a0db8b65799b89fee3430734be4ea515ccc688d7a5c7414d831295dd56177");
    (* Singleton: 1 rg × 1 token, bit clear. *)
    ("singleton-clear", 1, 1, make_bitmap ~bits:1 ~set:[],
       "c650a40f2d76fe880bc5dcfdf6864aca0456e4c5b051ae5cdeb8bb110f13396a");
    (* 4 rgs × 8 tokens (32 bits = 4 bytes), one bit per rg on the
       diagonal. *)
    ("4x8-diagonal", 4, 8,
       make_bitmap ~bits:32 ~set:[0; 9; 18; 27],
       "5aeabfba78443fe86ce9baab139680ba0905d1fccbfd534e7404a8950655fbb8");
    (* 3 rgs × 17 tokens (51 bits = 7 bytes), every-other bit set. *)
    ("3x17-alternating", 3, 17,
       make_bitmap ~bits:51
         ~set:(List.init 26 (fun i -> i * 2)),
       "e68665d4649cd408822f8b0556c0e5d45b480e6cb7cb9bec9c4add08463e7e3c");
  ] in
  List.iter (fun (name, num_rgs, num_tokens, bitmap_str, hash) ->
    run_case ~name ~expected_hash:hash
      ~num_rgs ~num_tokens ~bitmap_str
  ) cases;
  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
