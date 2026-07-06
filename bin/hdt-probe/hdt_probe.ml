(* hdt_probe — consumer executable (outside the verified boundary,
   CLAUDE.md rule #11 CONSUMER class): opens an HDT file through the
   F*-extracted HDT.Container stage-1 reader and prints the section
   inventory plus the Header section's RDF metadata as parsed by the
   verified Parser.NTriples.

   Stage 2 (HDT.Dictionary — PFC dictionary decode + ID<->term
   mapping) adds: full dictionary-section dumps with CRC8/CRC32C
   validation, per-section ID round-trip (pfc_locate (pfc_extract id)
   = id) and role-level round-trip (hdt_term_to_id (hdt_id_to_term
   id) = id) over the full ID space of each section/role, and — when
   a ground-truth .nt path is given as the second argument — a term-
   set comparison between the dictionary's decoded terms (composed
   per the HDT shared/subjects/predicates/objects convention) and the
   fixture's source RDF as parsed by the project's own verified
   Parser.NTriples (a code path entirely independent of the PFC
   decoder under test).

   Usage: hdt_probe FILE.hdt [GROUND_TRUTH.nt]

   Exit code: 0 on a fully parsed inventory, 1 on any parse failure.
   All decisions (offsets, CRC checks, property parsing, header
   N-Triples decode, PFC block decode, ID<->term mapping) are made in
   F*; this file only formats output and drives the ground-truth
   comparison loop. *)

let z = Z.to_string

let print_ci (label : string) (ci : HDT_Container.hdt_control_info) =
  Printf.printf "%s control information\n" label;
  Printf.printf "  offset      : %s .. %s\n"
    (z ci.HDT_Container.hci_start) (z ci.HDT_Container.hci_end);
  Printf.printf "  format      : %s\n" ci.HDT_Container.hci_format;
  Printf.printf "  properties  : %s\n"
    (if ci.HDT_Container.hci_props_raw = "" then "(none)"
     else ci.HDT_Container.hci_props_raw);
  Printf.printf "  crc16       : stored 0x%04X computed 0x%04X %s\n"
    (Z.to_int ci.HDT_Container.hci_crc_stored)
    (Z.to_int ci.HDT_Container.hci_crc_computed)
    (if ci.HDT_Container.hci_crc_ok then "OK" else "MISMATCH")

let print_pfc (label : string) (s : HDT_Container.hdt_pfc_section) =
  Printf.printf "  %-10s : bytes %s .. %s  type=%s(PFC)  strings=%s  packed=%sB  blocksize=%s\n"
    label
    (z s.HDT_Container.pfc_start) (z s.HDT_Container.pfc_end)
    (z s.HDT_Container.pfc_type)
    (z s.HDT_Container.pfc_numstrings)
    (z s.HDT_Container.pfc_packed_bytes)
    (z s.HDT_Container.pfc_blocksize)

let () =
  if Array.length Sys.argv < 2 then begin
    prerr_endline "usage: hdt_probe FILE.hdt";
    exit 2
  end;
  let path = Sys.argv.(1) in
  (match HDT_Container.hdt_file_size path with
   | FStar_Pervasives_Native.None ->
     Printf.printf "cannot read %s\n" path; exit 1
   | FStar_Pervasives_Native.Some sz ->
     Printf.printf "file        : %s (%s bytes)\n" path (z sz));
  match HDT_Container.hdt_read_inventory path with
  | FStar_Pervasives_Native.None ->
    print_endline "PARSE FAILED: not a readable HDT v1 container (bad cookie, CRC mismatch, unsupported section type, or truncation)";
    exit 1
  | FStar_Pervasives_Native.Some (hex, inv) ->
    print_ci "global" inv.HDT_Container.inv_global;
    print_ci "header" inv.HDT_Container.inv_header_ci;
    Printf.printf "header data : bytes %s .. %s (%s bytes of N-Triples)\n"
      (z inv.HDT_Container.inv_header_data_start)
      (Z.to_string
         (Z.add inv.HDT_Container.inv_header_data_start
                inv.HDT_Container.inv_header_data_len))
      (z inv.HDT_Container.inv_header_data_len);
    print_ci "dictionary" inv.HDT_Container.inv_dict_ci;
    print_pfc "shared" inv.HDT_Container.inv_dict_shared;
    print_pfc "subjects" inv.HDT_Container.inv_dict_subjects;
    print_pfc "predicates" inv.HDT_Container.inv_dict_predicates;
    print_pfc "objects" inv.HDT_Container.inv_dict_objects;
    print_ci "triples" inv.HDT_Container.inv_triples_ci;
    Printf.printf "triples data: starts at byte %s (order=%s)\n"
      (z inv.HDT_Container.inv_triples_data_start)
      (match HDT_Container.hdt_triples_order inv with
       | FStar_Pervasives_Native.Some o -> z o
       | FStar_Pervasives_Native.None -> "?");
    (match HDT_Container.hdt_header_triples_hex hex inv with
     | FStar_Pervasives_Native.None ->
       print_endline "header      : COULD NOT DECODE"; exit 1
     | FStar_Pervasives_Native.Some triples ->
       Printf.printf "header RDF  : %d triples (via verified Parser.NTriples)\n"
         (List.length triples);
       List.iter
         (fun t ->
            print_string "  ";
            print_string (RDF_NQuads_Serialize.nq_line_for_triple_default_graph t))
         triples);

    (* --- stage 2: PFC dictionary decode (HDT.Dictionary) --- *)
    Printf.printf "\n--- stage 2: PFC dictionary decode ---\n";
    let opt_is_some = function
      | FStar_Pervasives_Native.Some _ -> true
      | FStar_Pervasives_Native.None -> false in
    let dict_sections =
      [ ("shared", inv.HDT_Container.inv_dict_shared);
        ("subjects", inv.HDT_Container.inv_dict_subjects);
        ("predicates", inv.HDT_Container.inv_dict_predicates);
        ("objects", inv.HDT_Container.inv_dict_objects) ] in
    let section_data =
      List.map
        (fun (label, sec) ->
           let crc_ok = HDT_Dictionary.pfc_section_crc_ok hex sec in
           match HDT_Dictionary.decode_section hex sec with
           | FStar_Pervasives_Native.None ->
             Printf.printf "  %-10s : DECODE FAILED\n" label;
             (label, sec, ([] : string list))
           | FStar_Pervasives_Native.Some strs ->
             let n_decoded = List.length strs in
             let n_expected = Z.to_int sec.HDT_Container.pfc_numstrings in
             let terms = List.map HDT_Dictionary.hdt_term_of_string strs in
             let n_term_ok = List.length (List.filter opt_is_some terms) in
             Printf.printf
               "  %-10s : decoded %d strings (expected %d), crc %s, term-parse %d/%d ok\n"
               label n_decoded n_expected
               (if crc_ok then "OK" else "MISMATCH")
               n_term_ok n_decoded;
             (label, sec, strs))
        dict_sections
    in

    (* --- stage 2: per-section ID round-trip --- *)
    Printf.printf "\n--- stage 2: per-section round-trip (pfc_locate (pfc_extract id) = id) ---\n";
    List.iter
      (fun (label, sec, _) ->
         let n = Z.to_int sec.HDT_Container.pfc_numstrings in
         let pass = ref 0 and fail = ref 0 in
         for i = 1 to n do
           let id = Z.of_int i in
           (match HDT_Dictionary.pfc_extract hex sec id with
            | FStar_Pervasives_Native.None -> incr fail
            | FStar_Pervasives_Native.Some s ->
              (match HDT_Dictionary.pfc_locate hex sec s with
               | FStar_Pervasives_Native.Some id2 when Z.equal id2 id -> incr pass
               | _ -> incr fail))
         done;
         Printf.printf "  %-10s : round-trip %d pass, %d fail (out of %d)\n"
           label !pass !fail n)
      section_data;

    (* --- stage 2: role-level ID round-trip (shared/subjects/objects
       arithmetic + predicates) --- *)
    Printf.printf "\n--- stage 2: role-level round-trip (hdt_term_to_id (hdt_id_to_term id) = id) ---\n";
    let roles =
      [ ("subject", HDT_Dictionary.Role_Subject);
        ("predicate", HDT_Dictionary.Role_Predicate);
        ("object", HDT_Dictionary.Role_Object) ] in
    List.iter
      (fun (label, role) ->
         let maxid = Z.to_int (HDT_Dictionary.hdt_role_max_id inv role) in
         let pass = ref 0 and fail = ref 0 in
         for i = 1 to maxid do
           let id = Z.of_int i in
           (match HDT_Dictionary.hdt_id_to_term hex inv role id with
            | FStar_Pervasives_Native.None -> incr fail
            | FStar_Pervasives_Native.Some term ->
              (match HDT_Dictionary.hdt_term_to_id hex inv role term with
               | FStar_Pervasives_Native.Some id2 when Z.equal id2 id -> incr pass
               | _ -> incr fail))
         done;
         Printf.printf "  %-10s : round-trip %d pass, %d fail (out of %d)\n"
           label !pass !fail maxid)
      roles;

    (* --- stage 2: dictionary term set vs. ground-truth .nt (optional
       2nd argument) — parsed independently via the project's own
       verified Parser.NTriples, never via the PFC decoder under
       test. --- *)
    if Array.length Sys.argv >= 3 then begin
      let nt_path = Sys.argv.(2) in
      Printf.printf "\n--- stage 2: dictionary term set vs ground truth (%s) ---\n" nt_path;
      let ic = open_in_bin nt_path in
      let n = in_channel_length ic in
      let buf = Bytes.create n in
      really_input ic buf 0 n;
      close_in ic;
      let content = Bytes.to_string buf in
      let triples = Parser_NTriples.parse_ntriples content in
      let subj_term (t : RDF_Triple.triple) =
        match t.RDF_Triple.s with
        | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
        | RDF_Term.S_BNode b -> RDF_Term.T_BNode b
      in
      let gt_subjects = List.sort_uniq compare (List.map subj_term triples) in
      let gt_predicates =
        List.sort_uniq compare
          (List.map (fun (t : RDF_Triple.triple) -> RDF_Term.T_IRI t.RDF_Triple.p) triples)
      in
      let gt_objects =
        List.sort_uniq compare (List.map (fun (t : RDF_Triple.triple) -> t.RDF_Triple.o) triples)
      in
      let terms_of label =
        let (_, _, strs) = List.find (fun (l, _, _) -> l = label) section_data in
        List.filter_map
          (fun s ->
             match HDT_Dictionary.hdt_term_of_string s with
             | FStar_Pervasives_Native.Some t -> Some t
             | FStar_Pervasives_Native.None -> None)
          strs
      in
      let shared_terms = terms_of "shared" in
      let dict_subjects = List.sort_uniq compare (shared_terms @ terms_of "subjects") in
      let dict_objects = List.sort_uniq compare (shared_terms @ terms_of "objects") in
      let dict_predicates = List.sort_uniq compare (terms_of "predicates") in
      let report label dict gt =
        let ok = dict = gt in
        Printf.printf "  %-10s : dictionary %d terms, ground truth %d terms -> %s\n"
          label (List.length dict) (List.length gt)
          (if ok then "MATCH" else "MISMATCH")
      in
      report "subjects" dict_subjects gt_subjects;
      report "predicates" dict_predicates gt_predicates;
      report "objects" dict_objects gt_objects
    end
