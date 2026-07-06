(* probe.ml -- consumer-side driver for the durable-UPDATE delta-log
   crash-kill harness (tests/local/delta_log_crash_harness.sh).

   Per CLAUDE.md rule #11: this is a consumer tool, not part of the
   verified library, so it lives in bin/<consumer>/ rather than
   formal/fstar/ocaml-output/. It contains NO RDF/SPARQL semantic
   logic and NO byte-layout logic of its own -- every byte assembled
   or parsed goes through the F*-extracted, verified functions in
   RDF_Store_Columnar_DeltaLog (serialize_delta_batch / parse_log /
   expected_digest_bytes / delta_log_append / delta_log_fsync /
   delta_log_read_all / fsync_dir, realised by
   formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
   NNN_delta_log_io.sh). This file's only job is: generate
   deterministic test content, sequence calls to those functions
   (including deliberately SLICING one batch's bytes across several
   delta_log_append calls with a tiny pause between them, to widen
   the window a `kill -9` from the harness script can land inside),
   and report machine-readable PASS/FAIL lines the harness parses.

   Modes:
     init      <path>
     append    <path> <seed> <num_batches> <ops_per_batch> <chunk_size>
     verify    <path> <seed> <num_batches> <ops_per_batch>
     hashcheck <path>
*)

module DL = RDF_Store_Columnar_DeltaLog

(* --- deterministic fixture content --------------------------------- *)

(* Every (seed, batch_index) pair reproduces the exact same delta_batch
   -- no randomness, no wall-clock, no file-order dependence -- so
   `verify` can independently re-derive "what SHOULD batch i contain"
   without any side channel from `append`. *)
let batch_for_seq (seed : int) (i : int) (ops_per_batch : int) : DL.delta_batch =
  let ops =
    List.init ops_per_batch (fun j ->
      let s : RDF_Term.subject =
        RDF_Term.S_IRI (Printf.sprintf "http://example.org/s%d_%d_%d" seed i j) in
      let p : Prims.string = Printf.sprintf "http://example.org/p%d" j in
      let o : RDF_Term.rdf_term =
        RDF_Term.T_IRI (Printf.sprintf "http://example.org/o%d_%d_%d" seed i j) in
      let tr : RDF_Triple.triple = { RDF_Triple.s; RDF_Triple.p; RDF_Triple.o } in
      DL.DE_Add (tr, None))
  in
  { DL.db_seq = Z.of_int i; DL.db_epoch = Z.of_int 0; DL.db_ops = ops }

(* --- modes ----------------------------------------------------------- *)

let init (path : string) : unit =
  (if Sys.file_exists path then Sys.remove path);
  DL.delta_log_append path DL.serialize_log_header;
  DL.delta_log_fsync path;
  (try DL.fsync_dir (Filename.dirname path) with _ -> ());
  Printf.printf "INIT_OK path=%s\n%!" path

(* Slice one batch's serialized bytes into `chunk_size`-piece LISTS
   and append each piece with its OWN `delta_log_append` call (the
   real, patched realisation -- O_APPEND writes), pausing briefly
   between pieces. A `kill -9` sent by the harness at a random moment
   has a much better chance of landing between two of these small
   appends than it would against one large monolithic write() --
   that's the "mid-write via small writes" stress the design doc's
   stage-2 acceptance test calls for. Only the LAST successfully-
   completed batch's fsync is the durability boundary; a batch killed
   mid-slice is exactly the torn-tail case `parse_log` must reject.

   IMPORTANT: slice `RDF_Bytes.bytes` (the LOGICAL `int list` of byte
   values -- FStar_Char.char extracts to plain `int`, see
   FStar_Char.ml) rather than the OCTET string `bytes_to_string`
   produces. `bytes_to_string`/`bytes_of_string` round-trip through
   BatUTF8 (FStar_String.ml: `BatUTF8.init`/`.get`), so a byte value
   >= 128 becomes a MULTI-OCTET UTF-8 sequence in the string form --
   slicing that string at an arbitrary octet offset (chunk_size) can
   cut a multi-byte sequence in half and crash `bytes_of_string` on
   the resulting invalid partial UTF-8 with `BatUChar.Out_of_range`
   (hit exactly this while developing this driver). Slicing the
   `int list` instead sidesteps the encoding entirely: each chunk is
   independently well-formed, and UTF-8 encoding is per-codepoint
   (no cross-codepoint state), so
     bytes_to_string chunk1 ^ bytes_to_string chunk2
       == bytes_to_string (chunk1 @ chunk2)
   -- writing the chunks separately, in order, produces byte-for-byte
   the same on-disk octets as one whole-batch write would. *)
let rec take_n (n : int) (lst : 'a list) : 'a list =
  match n, lst with
  | 0, _ | _, [] -> []
  | n, x :: rest -> x :: take_n (n - 1) rest

let rec drop_n (n : int) (lst : 'a list) : 'a list =
  match n, lst with
  | 0, _ -> lst
  | _, [] -> []
  | n, _ :: rest -> drop_n (n - 1) rest

let append_one_batch (path : string) (b : DL.delta_batch) (chunk_size : int) : unit =
  let bytes = DL.serialize_delta_batch b in
  let total = List.length bytes in
  let pos = ref 0 in
  let remaining = ref bytes in
  while !pos < total do
    let n = if chunk_size < total - !pos then chunk_size else total - !pos in
    let chunk = take_n n !remaining in
    DL.delta_log_append path chunk;
    remaining := drop_n n !remaining;
    pos := !pos + n;
    if !pos < total then (try Unix.sleepf 0.001 with _ -> ())
  done;
  DL.delta_log_fsync path

let append (path : string) (seed : int) (num_batches : int) (ops_per_batch : int)
    (chunk_size : int) : unit =
  for i = 0 to num_batches - 1 do
    let b = batch_for_seq seed i ops_per_batch in
    append_one_batch path b chunk_size;
    Printf.printf "WROTE seq=%d\n%!" i
  done;
  Printf.printf "APPEND_DONE num_batches=%d\n%!" num_batches

let verify (path : string) (seed : int) (num_batches : int) (ops_per_batch : int) : unit =
  if not (Sys.file_exists path) then
    Printf.printf "RECOVERED=0 CORRUPT_ACCEPTS=0 FILE_MISSING=1\n%!"
  else
    let bytes = DL.delta_log_read_all path in
    match DL.parse_log bytes with
    | None ->
      (* Header itself is unreadable/corrupt -- the log is empty of
         any committed batch, but this must never be reported as a
         "corrupt accept" (nothing was accepted). *)
      Printf.printf "RECOVERED=0 CORRUPT_ACCEPTS=0 HEADER_BAD=1\n%!"
    | Some (recovered, leftover) ->
      let n = List.length recovered in
      let corrupt = ref 0 in
      List.iteri
        (fun i b ->
           if i < num_batches then begin
             let expected = batch_for_seq seed i ops_per_batch in
             if b <> expected then incr corrupt
           end else incr corrupt (* more batches than we ever wrote -- can't be real *))
        recovered;
      let leftover_len = List.length leftover in
      Printf.printf "RECOVERED=%d CORRUPT_ACCEPTS=%d LEFTOVER_BYTES=%d\n%!"
        n !corrupt leftover_len

(* Stage 2's own acceptance test (design doc's staged table, row 2):
   "expected_digest batch = sha256(read_bytes(path)) after a real
   append+fsync+read-back cycle, on-disk, this sandbox." Uses the
   ALREADY-wired Fstar_pure_hashes.sha256 (issue #63) -- see
   RDF.Store.Columnar.DeltaLog.fst section 11's banner comment for
   why the hash call lives here rather than inside that module. *)
let hashcheck (path : string) : unit =
  (if Sys.file_exists path then Sys.remove path);
  let b = batch_for_seq 999999 0 3 in
  let bytes = DL.serialize_delta_batch b in
  DL.delta_log_append path bytes;
  DL.delta_log_fsync path;
  let on_disk = DL.delta_log_read_all path in
  let expected_digest =
    Fstar_pure_hashes.sha256 (RDF_Bytes.bytes_to_string (DL.expected_digest_bytes b)) in
  let actual_digest = Fstar_pure_hashes.sha256 (RDF_Bytes.bytes_to_string on_disk) in
  if expected_digest = actual_digest then
    Printf.printf "HASH_WITNESS=PASS digest=%s\n%!" expected_digest
  else begin
    Printf.printf "HASH_WITNESS=FAIL expected=%s actual=%s\n%!" expected_digest actual_digest;
    exit 1
  end

(* --------------------------------------------------------------------
   Durable-UPDATE stage 3 (merge-on-read, tests/local/
   durable_update_stage3.sh): one semantically-real batch -- an ADD +
   a tombstoning REMOVE on the default graph, a CREATE+ADD into a
   brand-new named graph, and a CLEAR wiping an existing named graph --
   against the SAME small fixture tests/unit/store_capabilities_unit.ml
   already hardcodes (tests/local/data/cottas_sample.nq; reused rather
   than re-parsed for the same "both routes load literally the same
   dataset" reason that file's own banner gives). Unlike `append`
   above (deterministic but semantically arbitrary filler content),
   this scenario's ops are chosen to exercise every delta_entry
   constructor `tests/local/durable_update_stage3.sh` needs, and its
   ground truth is computed by calling the F*-extracted, VERIFIED
   `RDF_Store_Columnar_DeltaMerge.apply_entries_ref` directly on the
   hardcoded base graphs -- the same reference function that module's
   own `lemma_merge_on_read_matches_apply_entries` proves the delta-
   log/merge-on-read path agrees with. *)

module DM = RDF_Store_Columnar_DeltaMerge

let lit (v : string) : RDF_Term.rdf_term =
  RDF_Term.T_Literal
    { RDF_Term.lexical_form = v; RDF_Term.datatype = RDF_Term.xsd_string;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None }

let mk_triple (s : string) (p : string) (o : RDF_Term.rdf_term) : RDF_Triple.triple =
  { RDF_Triple.s = RDF_Term.S_IRI s; RDF_Triple.p = p; RDF_Triple.o = o }

let iri_default_subject = "https://example.org/default-subject"
let iri_status = "https://example.org/status"
let iri_carol = "https://example.org/carol"
let iri_name = "https://example.org/name"
let iri_graph_events = "https://example.org/graph/events"
let iri_attends = "https://example.org/attends"
let iri_event_x = "https://example.org/event-x"
let iri_graph_docs = "https://example.org/graph/docs"
let iri_graph_people = "https://example.org/graph/people"

let scenario_default_subject_status = mk_triple iri_default_subject iri_status (lit "default")
let scenario_carol_name = mk_triple iri_carol iri_name (lit "Carol")
let scenario_carol_attends = mk_triple iri_carol iri_attends (RDF_Term.T_IRI iri_event_x)

(* Fixture base graphs, hardcoded to match tests/local/data/
   cottas_sample.nq exactly (5 triples: 1 default, 3 in graph/people,
   1 in graph/docs). *)
let people_triples =
  [ mk_triple "https://example.org/alice" "https://example.org/name" (lit "Alice");
    mk_triple "https://example.org/alice" "https://example.org/knows"
      (RDF_Term.T_IRI "https://example.org/bob");
    mk_triple "https://example.org/bob" "https://example.org/name" (lit "Bob");
  ]
let docs_triples = [ mk_triple "https://example.org/doc" "https://example.org/title" (lit "Specimen") ]
let default_triples = [ scenario_default_subject_status ]

(* Durable-UPDATE stage 4 (compaction, tests/local/
   durable_update_stage4_compaction.sh): `epoch` is now a parameter
   (default 0, matching stage 3's original hardcoded value, so stage
   3's own script -- which never passes an epoch arg -- is unaffected)
   rather than a fixed constant, because stage 4's compaction protocol
   requires a caller appending AFTER a compaction to stamp its batch
   with an epoch strictly greater than the base's own recorded
   compacted_through_epoch (RDF.Store.Columnar.DeltaLog.fst section 13's
   banner) or the write is silently treated as already-folded and
   ignored at merge-on-read time. *)
let scenario_batch (epoch : int) : DL.delta_batch =
  { DL.db_seq = Z.zero; DL.db_epoch = Z.of_int epoch;
    DL.db_ops =
      [ DL.DE_Add (scenario_carol_name, FStar_Pervasives_Native.None);
        DL.DE_Remove (scenario_default_subject_status, FStar_Pervasives_Native.None);
        DL.DE_Create iri_graph_events;
        DL.DE_Add (scenario_carol_attends, FStar_Pervasives_Native.Some iri_graph_events);
        DL.DE_Clear (FStar_Pervasives_Native.Some iri_graph_docs);
      ] }

let scenario_write ?(epoch = 0) (path : string) : unit =
  (if Sys.file_exists path then Sys.remove path);
  DL.delta_log_append path DL.serialize_log_header;
  DL.delta_log_append path (DL.serialize_delta_batch (scenario_batch epoch));
  DL.delta_log_fsync path;
  Printf.printf "SCENARIO_WRITE_OK path=%s\n%!" path

(* Same content, sliced across small appends with a pause between each
   -- for the crash harness to SIGKILL mid-write, exactly the
   `append_one_batch` shape `append` above already uses. *)
let scenario_write_sliced ?(epoch = 0) (path : string) (chunk_size : int) : unit =
  (if Sys.file_exists path then Sys.remove path);
  DL.delta_log_append path DL.serialize_log_header;
  DL.delta_log_fsync path;
  append_one_batch path (scenario_batch epoch) chunk_size;
  Printf.printf "SCENARIO_WRITE_SLICED_DONE path=%s\n%!" path

(* Stage 4's "layering continues" scenario: a SECOND, distinct batch
   (adds "Dave") appended AFTER a compaction has already folded
   `scenario_batch` into a fresh base and truncated the log. Unlike
   `scenario_write` above, this APPENDS to whatever is already at
   `path` (typically just the fresh empty-log header a compaction just
   wrote) rather than removing/recreating it -- exactly the shape a
   real post-compaction Update commit would take. *)
let iri_dave = "https://example.org/dave"
let scenario_dave_name = mk_triple iri_dave iri_name (lit "Dave")

let scenario2_batch (epoch : int) : DL.delta_batch =
  { DL.db_seq = Z.zero; DL.db_epoch = Z.of_int epoch;
    DL.db_ops = [ DL.DE_Add (scenario_dave_name, FStar_Pervasives_Native.None) ] }

let scenario2_write (path : string) (epoch : int) : unit =
  DL.delta_log_append path (DL.serialize_delta_batch (scenario2_batch epoch));
  DL.delta_log_fsync path;
  Printf.printf "SCENARIO2_WRITE_OK path=%s epoch=%d\n%!" path epoch

let triple_line (t : RDF_Triple.triple) : string =
  let term_str (o : RDF_Term.rdf_term) =
    match o with
    | RDF_Term.T_IRI i -> "<" ^ i ^ ">"
    | RDF_Term.T_BNode b -> "_:" ^ b
    | RDF_Term.T_Literal l -> "\"" ^ l.RDF_Term.lexical_form ^ "\""
  in
  let subj_str =
    match t.RDF_Triple.s with
    | RDF_Term.S_IRI i -> "<" ^ i ^ ">"
    | RDF_Term.S_BNode b -> "_:" ^ b
  in
  Printf.sprintf "%s <%s> %s" subj_str t.RDF_Triple.p (term_str t.RDF_Triple.o)

(* Ground truth for one graph: apply_entries_ref over the hardcoded
   base, sorted (order-independent set comparison -- the shell script
   sorts the CLI's own SELECT output the same way before diffing). *)
let scenario_expect (which : string) : unit =
  let (graph_key, base) =
    match which with
    | "default" -> (FStar_Pervasives_Native.None, default_triples)
    | "people" -> (FStar_Pervasives_Native.Some iri_graph_people, people_triples)
    | "docs" -> (FStar_Pervasives_Native.Some iri_graph_docs, docs_triples)
    | "events" -> (FStar_Pervasives_Native.Some iri_graph_events, [])
    | _ -> failwith ("scenario-expect: unknown graph " ^ which)
  in
  let result = DM.apply_entries_ref graph_key base (scenario_batch 0).DL.db_ops in
  List.iter (fun t -> print_endline (triple_line t)) (List.sort compare result)

let () =
  match Array.to_list Sys.argv with
  | _ :: "init" :: path :: [] -> init path
  | _ :: "append" :: path :: seed :: num_batches :: ops_per_batch :: chunk_size :: [] ->
    append path (int_of_string seed) (int_of_string num_batches)
      (int_of_string ops_per_batch) (int_of_string chunk_size)
  | _ :: "verify" :: path :: seed :: num_batches :: ops_per_batch :: [] ->
    verify path (int_of_string seed) (int_of_string num_batches) (int_of_string ops_per_batch)
  | _ :: "hashcheck" :: path :: [] -> hashcheck path
  | _ :: "scenario-write" :: path :: [] -> scenario_write path
  | _ :: "scenario-write" :: path :: epoch :: [] -> scenario_write ~epoch:(int_of_string epoch) path
  | _ :: "scenario-write-sliced" :: path :: chunk_size :: [] ->
    scenario_write_sliced path (int_of_string chunk_size)
  | _ :: "scenario-write-sliced" :: path :: chunk_size :: epoch :: [] ->
    scenario_write_sliced ~epoch:(int_of_string epoch) path (int_of_string chunk_size)
  | _ :: "scenario-expect" :: which :: [] -> scenario_expect which
  | _ :: "scenario2-write" :: path :: epoch :: [] -> scenario2_write path (int_of_string epoch)
  | _ ->
    Printf.eprintf
      "usage: probe (init|append <path> <seed> <num_batches> <ops_per_batch> <chunk_size>\n\
      \             |verify <path> <seed> <num_batches> <ops_per_batch>|hashcheck <path>\n\
      \             |scenario-write <path> [epoch]\n\
      \             |scenario-write-sliced <path> <chunk_size> [epoch]\n\
      \             |scenario2-write <path> <epoch>\n\
      \             |scenario-expect (default|people|docs|events))\n";
    exit 2
