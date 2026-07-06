(* hdt_probe — consumer executable (outside the verified boundary,
   CLAUDE.md rule #11 CONSUMER class): opens an HDT file through the
   F*-extracted HDT.Container stage-1 reader and prints the section
   inventory plus the Header section's RDF metadata as parsed by the
   verified Parser.NTriples.

   Usage: hdt_probe FILE.hdt

   Exit code: 0 on a fully parsed inventory, 1 on any parse failure.
   All decisions (offsets, CRC checks, property parsing, header
   N-Triples decode) are made in F*; this file only formats output. *)

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
         triples)
