(* xml_probe.ml — ad-hoc driver for task #49 (XML generality sanity check).
   I/O glue only, per rule #11: no XML parsing logic here. Calls
   Parser_XML.parse_xml_document / parse_xml_document_children and
   XML_Namespaces.is_namespace_wellformed (both extracted from F-star) on a
   given file, reports what came back, and (with -bench) times the parse
   and prints peak RSS from /proc/self/status.

   Not part of the build; investigation-only artifact for
   docs/designissues/2026-08-10-xml-generality-findings.md. *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

let rec count_nodes (n : Parser_XML.xml_node) : int =
  match n with
  | Parser_XML.XElement (_, _, children) ->
    1 + List.fold_left (fun acc c -> acc + count_nodes c) 0 children
  | _ -> 1

let rec max_depth (n : Parser_XML.xml_node) : int =
  match n with
  | Parser_XML.XElement (_, _, children) ->
    1 + List.fold_left (fun acc c -> max acc (max_depth c)) 0 children
  | _ -> 1

let vm_hwm_kb () =
  try
    let ic = open_in "/proc/self/status" in
    let rec loop () =
      match input_line ic with
      | line ->
        if String.length line >= 6 && String.sub line 0 6 = "VmHWM:" then begin
          close_in ic; Some (String.trim (String.sub line 6 (String.length line - 6)))
        end else loop ()
      | exception End_of_file -> close_in ic; None
    in loop ()
  with Sys_error _ -> None

let hex_dump (s : string) : string =
  let buf = Buffer.create (String.length s * 3) in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02X " (Char.code c))) s;
  Buffer.contents buf

let rec dump_attrs_and_text (indent : string) (n : Parser_XML.xml_node) : unit =
  match n with
  | Parser_XML.XElement (tag, attrs, children) ->
    Printf.printf "%selem %s\n" indent tag;
    List.iter (fun (a : Parser_XML.xml_attribute) ->
        Printf.printf "%s  attr %s = %S  [hex: %s]\n" indent a.attr_name a.attr_value
          (hex_dump a.attr_value))
      attrs;
    List.iter (dump_attrs_and_text (indent ^ "  ")) children
  | Parser_XML.XText t ->
    Printf.printf "%stext %S  [hex: %s]\n" indent t (hex_dump t)
  | Parser_XML.XCDATA t -> Printf.printf "%scdata %S\n" indent t
  | Parser_XML.XComment t -> Printf.printf "%scomment %S\n" indent t
  | Parser_XML.XPI (tgt, data) -> Printf.printf "%spi %s %S\n" indent tgt data

let () =
  let bench = Array.length Sys.argv > 2 && Sys.argv.(2) = "-bench" in
  let dump = Array.length Sys.argv > 2 && Sys.argv.(2) = "-dump" in
  let path = Sys.argv.(1) in
  let input = read_file path in
  Printf.printf "file: %s (%d bytes)\n" path (String.length input);
  let t0 = Unix.gettimeofday () in
  let result = Parser_XML.parse_xml_document input in
  let t1 = Unix.gettimeofday () in
  (match result with
   | Some node ->
     Printf.printf "PARSED: root ok, node_count=%d max_depth=%d\n"
       (count_nodes node) (max_depth node);
     (match Parser_XML.element_tag node with
      | Some tag -> Printf.printf "root tag: %s\n" tag
      | None -> ());
     if dump then dump_attrs_and_text "" node
   | None ->
     Printf.printf "REJECTED (parse_xml_document returned None)\n");
  if bench then begin
    Printf.printf "parse_time_s: %.4f\n" (t1 -. t0);
    (match vm_hwm_kb () with
     | Some kb -> Printf.printf "VmHWM: %s\n" kb
     | None -> Printf.printf "VmHWM: unavailable\n")
  end;
  (* Namespace-layer check, informational, only if the parse succeeded. *)
  (match result with
   | Some node ->
     let ns_ok = XML_Namespaces.is_namespace_wellformed "1.0" node in
     Printf.printf "namespace_wellformed(1.0): %b\n" ns_ok;
     let ns_ok11 = XML_Namespaces.is_namespace_wellformed "1.1" node in
     Printf.printf "namespace_wellformed(1.1): %b\n" ns_ok11
   | None -> ())
