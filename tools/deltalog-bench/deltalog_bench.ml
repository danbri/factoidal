(* deltalog_bench.ml -- consumer-side micro-benchmark driver, native
   OCaml sibling of tools/deltalog-bench/deltalog_bench.c (the KaRaMeL
   C build) and the js_of_ocaml/wasm_of_ocaml `deltaBatchToHex` path
   (bin/npm-entry/entry_jsoo.ml).

   Per CLAUDE.md rule #11: consumer tool, no byte-layout logic of its
   own. Two modes calling only F*-extracted functions:

     pure N
       Build N DE_Add delta_entry ops directly (same shape as
       bin/delta-log-probe/probe.ml's batch_for_seq / the C harness's
       mk_entry), time RDF_Store_Columnar_DeltaLog.serialize_delta_batch
       and .parse_delta_batch. Comparable to the C-native/C-wasm
       numbers (no SPARQL parsing involved).

     sparql N
       Build one `INSERT DATA { ... N triples ... }` SPARQL Update
       string, time the exact same pipeline
       bin/npm-entry/entry_jsoo.ml's `delta_batch_to_hex` runs:
       SPARQL11_Parser.parse_sparql_update ->
       RDF_Store_Columnar_DeltaMerge.update_ops_to_delta_entries ->
       RDF_Store_Columnar_DeltaLog.serialize_delta_batch. Comparable
       to the js_of_ocaml/wasm_of_ocaml `deltaBatchToHex` numbers.

   Usage: deltalog_bench (pure|sparql) N
   Prints one JSON line to stdout.
*)

module DL = RDF_Store_Columnar_DeltaLog
module DMerge = RDF_Store_Columnar_DeltaMerge

let now () = Unix.gettimeofday ()

(* ---- pure mode: hand-built delta_entry list, no SPARQL ---- *)

let build_ops_pure (n : int) : DL.delta_entry list =
  List.init n (fun i ->
    let s : RDF_Term.subject =
      RDF_Term.S_IRI (Printf.sprintf "http://example.org/s%d" i) in
    let p : Prims.string = "http://xmlns.com/foaf/0.1/knows" in
    let o : RDF_Term.rdf_term =
      RDF_Term.T_IRI (Printf.sprintf "http://example.org/o%d" i) in
    let tr : RDF_Triple.triple = { RDF_Triple.s; RDF_Triple.p; RDF_Triple.o } in
    DL.DE_Add (tr, None))

let run_pure (n : int) : unit =
  let ops = build_ops_pure n in
  let batch : DL.delta_batch =
    { DL.db_seq = Z.of_int 1; DL.db_epoch = Z.of_int 0; DL.db_ops = ops } in
  let t0 = now () in
  let bytes = DL.serialize_delta_batch batch in
  let t1 = now () in
  let nbytes = List.length bytes in
  let t2 = now () in
  let parsed = DL.parse_delta_batch bytes in
  let t3 = now () in
  let ok = match parsed with FStar_Pervasives_Native.Some _ -> true | _ -> false in
  Printf.printf
    "{\"mode\":\"pure\",\"n\":%d,\"bytes\":%d,\"serialize_s\":%.6f,\"parse_s\":%.6f,\"parse_ok\":%b}\n%!"
    n nbytes (t1 -. t0) (t3 -. t2) ok

(* ---- sparql mode: INSERT DATA text -> delta_batch_to_hex pipeline ---- *)

let build_insert_data_text (n : int) : string =
  let buf = Buffer.create (n * 64) in
  Buffer.add_string buf "INSERT DATA { ";
  for i = 0 to n - 1 do
    Buffer.add_string buf
      (Printf.sprintf "<http://example.org/s%d> <http://xmlns.com/foaf/0.1/knows> <http://example.org/o%d> . "
         i i)
  done;
  Buffer.add_string buf "}";
  Buffer.contents buf

let hex_of_bytes (bs : RDF_Bytes.bytes) : string =
  let buf = Buffer.create (List.length bs * 2) in
  List.iter (fun b -> Buffer.add_string buf (Printf.sprintf "%02x" b)) bs;
  Buffer.contents buf

let run_sparql (n : int) : unit =
  let text = build_insert_data_text n in
  let t0 = now () in
  let hex, op_count =
    match SPARQL11_Parser.parse_sparql_update text with
    | SPARQL11_Parser.ParseErr msg -> failwith ("SPARQL update parse error: " ^ msg)
    | SPARQL11_Parser.ParseOk (u, _rest) ->
      (match DMerge.update_ops_to_delta_entries "bench_0" u.SPARQL11_Algebra.u_ops with
       | FStar_Pervasives_Native.None -> failwith "unsupported update op"
       | FStar_Pervasives_Native.Some entries ->
         let batch : DL.delta_batch =
           { DL.db_seq = Z.of_int 1; DL.db_epoch = Z.of_int 0; DL.db_ops = entries } in
         let bytes = DL.serialize_delta_batch batch in
         (hex_of_bytes bytes, List.length entries))
  in
  let t1 = now () in
  Printf.printf
    "{\"mode\":\"sparql\",\"n\":%d,\"opCount\":%d,\"hexLen\":%d,\"total_s\":%.6f}\n%!"
    n op_count (String.length hex) (t1 -. t0)

let () =
  match Sys.argv with
  | [| _; "pure"; n |] -> run_pure (int_of_string n)
  | [| _; "sparql"; n |] -> run_sparql (int_of_string n)
  | _ ->
    prerr_endline "usage: deltalog_bench (pure|sparql) N";
    exit 2
