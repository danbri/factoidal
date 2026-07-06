(* cottas_memory_buffer_unit.ml -- stage 1 safety net for
   docs/designissues/2026-07-06-inmemory-bytes-store.md.

   Stage 1's claim: `Parquet_Footer.register_memory_buffer` (added by
   experimental_ocaml_glue/parquet_footer_zz_register_memory_buffer.sh)
   lets `RDF.CottasStore.cottas_ondisk_open` be handed a SYNTHETIC
   handle backed by an in-memory byte string instead of a real file
   path, and every existing query entry point built on top
   (`cottas_ondisk_search[_limited]`, `_estimate`, `_count_exact`,
   `_predicate_present`, `_has_decode_failure`, `_named_graphs`) works
   identically either way, because the whole reader treats the path
   argument as an opaque cache key (design doc §2.1).

   This is the "prove it" round-trip the design doc's stage list asks
   for BEFORE building anything else on top: read the SAME fixture
   COTTAS artifact tests/unit/store_capabilities_unit.ml already uses
   (tests/unit/fixtures/store_capabilities_sample.cottas) two ways --
   once via the real file path, once via a synthetic in-memory handle
   -- and assert every query result is IDENTICAL across the same
   bound/unbound shape matrix that file already exercises for the
   file-path case. No new decode/query logic is exercised here beyond
   what store_capabilities_unit.ml already pins; this file's only new
   claim is "the buffer path gives the SAME answers as the file path". *)

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

let some x = FStar_Pervasives_Native.Some x
let none = FStar_Pervasives_Native.None

let bound ?s ?p ?o () : SPARQL11_Algebra.triple_pattern_bound =
  { SPARQL11_Algebra.bs = (match s with None -> none | Some v -> some v);
    SPARQL11_Algebra.bp = (match p with None -> none | Some v -> some v);
    SPARQL11_Algebra.bo = (match o with None -> none | Some v -> some v) }

let shapes_of (t : RDF_Triple.triple) :
  (string * SPARQL11_Algebra.triple_pattern_bound) list =
  [ "unbound",   bound ();
    "bound-s",   bound ~s:t.RDF_Triple.s ();
    "bound-p",   bound ~p:t.RDF_Triple.p ();
    "bound-o",   bound ~o:t.RDF_Triple.o ();
    "bound-sp",  bound ~s:t.RDF_Triple.s ~p:t.RDF_Triple.p ();
    "bound-po",  bound ~p:t.RDF_Triple.p ~o:t.RDF_Triple.o ();
    "bound-so",  bound ~s:t.RDF_Triple.s ~o:t.RDF_Triple.o ();
    "bound-spo", bound ~s:t.RDF_Triple.s ~p:t.RDF_Triple.p ~o:t.RDF_Triple.o ();
  ]

let contains ~needle hay =
  let nl = String.length needle and hl = String.length hay in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
  go 0

(* Read a whole file into an OCaml string -- same idiom
   bin/factoidal-cli/factoidal_cli.ml's register_cottas_mem_file uses. *)
let read_whole_file (path : string) : string =
  let ic = open_in_bin path in
  let len = in_channel_length ic in
  let bytes =
    try really_input_string ic len
    with e -> close_in_noerr ic; raise e
  in
  close_in ic;
  bytes

let raw_bound_opt cods scope (b : SPARQL11_Algebra.triple_pattern_bound) =
  RDF_CottasStore.cottas_ondisk_build_bound_qp_opt cods
    b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp b.SPARQL11_Algebra.bo scope

let raw_solve cods scope b =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some bnd ->
    RDF_CottasStore.cottas_ondisk_rows_tok_to_triples
      (RDF_CottasStore.cottas_ondisk_search cods bnd)

let raw_solve_limited cods scope b n =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some bnd ->
    RDF_CottasStore.cottas_ondisk_rows_tok_to_triples
      (RDF_CottasStore.cottas_ondisk_search_limited cods bnd n)

let raw_estimate cods scope b =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> Z.zero
  | FStar_Pervasives_Native.Some bnd -> RDF_CottasStore.cottas_ondisk_estimate cods bnd

let raw_count_exact cods scope b =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> Z.zero
  | FStar_Pervasives_Native.Some bnd -> RDF_CottasStore.cottas_ondisk_count_exact cods bnd

(* Compare the file-backed store against the memory-backed store
   across every shape, for one graph scope. *)
let check_scope_equivalence ~label ~cods_file ~cods_mem ~scope ~(anchor : RDF_Triple.triple)
    ~(known_pred : string) ~(absent_pred : string) =
  List.iter
    (fun (shape_name, b) ->
      let name field = Printf.sprintf "%s/%s/%s" label shape_name field in
      check ~name:(name "solve")
        ((raw_solve cods_file scope b) = (raw_solve cods_mem scope b));
      check ~name:(name "solve_limited(1)")
        ((raw_solve_limited cods_file scope b Z.one) = (raw_solve_limited cods_mem scope b Z.one));
      check ~name:(name "estimate")
        ((raw_estimate cods_file scope b) = (raw_estimate cods_mem scope b));
      check ~name:(name "count_exact")
        ((raw_count_exact cods_file scope b) = (raw_count_exact cods_mem scope b)))
    (shapes_of anchor);
  check ~name:(Printf.sprintf "%s/predicate_present/known" label)
    ((RDF_CottasStore.cottas_ondisk_predicate_present cods_file known_pred)
     = (RDF_CottasStore.cottas_ondisk_predicate_present cods_mem known_pred));
  check ~name:(Printf.sprintf "%s/predicate_present/absent" label)
    ((RDF_CottasStore.cottas_ondisk_predicate_present cods_file absent_pred)
     = (RDF_CottasStore.cottas_ondisk_predicate_present cods_mem absent_pred));
  check ~name:(Printf.sprintf "%s/decode_failure" label)
    ((RDF_CottasStore.cottas_ondisk_has_decode_failure cods_file.RDF_CottasStore.cods_handle)
     = (RDF_CottasStore.cottas_ondisk_has_decode_failure cods_mem.RDF_CottasStore.cods_handle))

let () =
  Printf.printf "== cottas_memory_buffer_unit ==\n";

  let fixture_path = Filename.concat "tests/unit/fixtures" "store_capabilities_sample.cottas" in
  if not (Sys.file_exists fixture_path) then begin
    Printf.printf "  FAIL  fixture missing at %s\n" fixture_path;
    Printf.printf "== summary: %d pass, %d fail (out of %d) ==\n" !passed (!failed + 1) (!passed + !failed + 1);
    exit 1
  end;

  (* Register the SAME bytes under a synthetic handle. This is the
     stage 1 seam: no file named "mem:cottas_memory_buffer_unit" exists
     anywhere, and cottas_ondisk_open must still succeed on it. *)
  let bytes = read_whole_file fixture_path in
  let mem_handle = "mem:cottas_memory_buffer_unit" in
  Parquet_Footer.register_memory_buffer mem_handle bytes;

  (* Round-trip sanity: registering under a handle that is NOT on disk
     must not silently fall back to treating the handle as a real path
     (that would defeat the whole point -- e.g. if some code path did
     its own Sys.file_exists check outside the cache). *)
  check ~name:"synthetic handle is not a real file"
    (not (Sys.file_exists mem_handle));

  match RDF_CottasStore.cottas_ondisk_open fixture_path,
        RDF_CottasStore.cottas_ondisk_open mem_handle
  with
  | FStar_Pervasives_Native.None, _ ->
    Printf.printf "  FAIL  cottas_ondisk_open returned None for the FILE path %s\n" fixture_path;
    incr failed
  | _, FStar_Pervasives_Native.None ->
    Printf.printf "  FAIL  cottas_ondisk_open returned None for the MEMORY handle %s\n" mem_handle;
    incr failed
  | FStar_Pervasives_Native.Some cods_file, FStar_Pervasives_Native.Some cods_mem ->
    (* Named-graph inventory must agree between the two opens (same
       bytes, same decode, different cache key only). *)
    let ng_file = RDF_CottasStore.cottas_ondisk_named_graphs cods_file in
    let ng_mem = RDF_CottasStore.cottas_ondisk_named_graphs cods_mem in
    check ~name:"named_graphs agree (file vs memory)"
      (List.map fst ng_file = List.map fst ng_mem);

    let people_graph_iri =
      match List.find_opt (fun (iri, _) -> contains ~needle:"graph/people" iri) ng_file with
      | Some (iri, _) -> iri
      | None -> failwith "cottas_memory_buffer_unit: no .../graph/people entry in fixture"
    in

    let default_anchor =
      match raw_solve cods_file RDF_CottasStore.COS_DefaultOnly (bound ()) with
      | t :: _ -> t
      | [] -> failwith "cottas_memory_buffer_unit: default-graph scope returned zero rows"
    in
    let people_anchor =
      match raw_solve cods_file (RDF_CottasStore.COS_NamedGraph people_graph_iri) (bound ()) with
      | t :: _ -> t
      | [] -> failwith "cottas_memory_buffer_unit: people-graph scope returned zero rows"
    in

    check_scope_equivalence ~label:"default" ~cods_file ~cods_mem
      ~scope:RDF_CottasStore.COS_DefaultOnly ~anchor:default_anchor
      ~known_pred:"https://example.org/status" ~absent_pred:"https://example.org/does-not-exist";
    check_scope_equivalence ~label:"named-graph(people)" ~cods_file ~cods_mem
      ~scope:(RDF_CottasStore.COS_NamedGraph people_graph_iri) ~anchor:people_anchor
      ~known_pred:"https://example.org/name" ~absent_pred:"https://example.org/does-not-exist";

    (* Re-registering the SAME handle with the SAME bytes a second time
       (last-registration-wins semantics, design doc's open decision 1
       footnote) must not change anything observable -- the "opening
       many short-lived in-memory stores" case the doc flags, checked
       here in its simplest form: same handle, same bytes, twice. *)
    Parquet_Footer.register_memory_buffer mem_handle bytes;
    (match RDF_CottasStore.cottas_ondisk_open mem_handle with
     | FStar_Pervasives_Native.None ->
       check ~name:"re-registered handle still opens" false
     | FStar_Pervasives_Native.Some cods_mem2 ->
       check ~name:"re-registered handle: solve(unbound) unchanged"
         ((raw_solve cods_mem RDF_CottasStore.COS_DefaultOnly (bound ()))
          = (raw_solve cods_mem2 RDF_CottasStore.COS_DefaultOnly (bound ()))))

  ;
  Printf.printf "== summary: %d pass, %d fail (out of %d) ==\n" !passed !failed (!passed + !failed);
  if !failed = 0 then exit 0 else exit 1
