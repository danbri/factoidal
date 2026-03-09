(* SPARQL Results XML (SRX) parser — UNVERIFIED TEST INFRASTRUCTURE.
   Not extracted from F*. Minimal regex-based parser for .srx files. *)

open RDF_Graph_Executable

type srx_result =
  | SRX_Bindings of {
      vars : string list;
      rows : (string * rdf_term) list list;
    }
  | SRX_Boolean of bool

let xml_unescape s =
  let s = Str.global_replace (Str.regexp_string "&amp;") "&" s in
  let s = Str.global_replace (Str.regexp_string "&lt;") "<" s in
  let s = Str.global_replace (Str.regexp_string "&gt;") ">" s in
  let s = Str.global_replace (Str.regexp_string "&quot;") "\"" s in
  let s = Str.global_replace (Str.regexp_string "&apos;") "'" s in
  s

let parse_srx xml =
  (* Extract variable names *)
  let var_re = Str.regexp {|<variable name="\([^"]+\)"|} in
  let vars = ref [] in
  let pos = ref 0 in
  (try while true do
     let _ = Str.search_forward var_re xml !pos in
     vars := Str.matched_group 1 xml :: !vars;
     pos := Str.match_end ()
   done with Not_found -> ());
  let vars = List.rev !vars in

  (* Check for boolean result first *)
  let bool_re = Str.regexp {|<boolean>\(true\|false\)</boolean>|} in
  if (try ignore (Str.search_forward bool_re xml 0); true with Not_found -> false) then
    SRX_Boolean (Str.matched_group 1 xml = "true")
  else begin
    (* Extract result rows *)
    let result_re = Str.regexp {|<result>|} in
    let result_end_re = Str.regexp {|</result>|} in
    let rows = ref [] in
    pos := 0;
    (try while true do
       let start = Str.search_forward result_re xml !pos in
       let finish = Str.search_forward result_end_re xml start in
       let block = String.sub xml start (finish - start + 9) in
       pos := finish + 9;

       (* Extract bindings from this result block *)
       let binding_re = Str.regexp {|<binding name="\([^"]+\)">\([\x00-\xff]*?\)</binding>|} in
       let bindings = ref [] in
       let bpos = ref 0 in
       (try while true do
          let _ = Str.search_forward binding_re block !bpos in
          let name = Str.matched_group 1 block in
          let value_str = String.trim (Str.matched_group 2 block) in
          bpos := Str.match_end ();

          (* Parse the value *)
          let term =
            let uri_re = Str.regexp {|<uri>\([^<]*\)</uri>|} in
            let bnode_re = Str.regexp {|<bnode>\([^<]*\)</bnode>|} in
            let lit_re = Str.regexp {|<literal\([^>]*\)>\([\x00-\xff]*?\)</literal>|} in
            if (try ignore (Str.search_forward uri_re value_str 0); true with Not_found -> false) then
              T_IRI (xml_unescape (Str.matched_group 1 value_str))
            else if (try ignore (Str.search_forward bnode_re value_str 0); true with Not_found -> false) then
              T_BNode ("_:" ^ Str.matched_group 1 value_str)
            else if (try ignore (Str.search_forward lit_re value_str 0); true with Not_found -> false) then begin
              let attrs = Str.matched_group 1 value_str in
              let lex = xml_unescape (Str.matched_group 2 value_str) in
              let lang_re = Str.regexp {|xml:lang="\([^"]+\)"|} in
              let dt_re = Str.regexp {|datatype="\([^"]+\)"|} in
              let lang = try ignore (Str.search_forward lang_re attrs 0);
                         Some (Str.matched_group 1 attrs)
                         with Not_found -> None in
              let dt = try ignore (Str.search_forward dt_re attrs 0);
                       Some (xml_unescape (Str.matched_group 1 attrs))
                       with Not_found -> None in
              let datatype = match dt, lang with
                | Some d, _ -> d
                | None, Some _ -> rdf_lang_string
                | None, None -> xsd_string in
              T_Literal { lexical_form = lex; datatype; lang_tag = lang }
            end
            else
              (* Unbound or empty — skip *)
              T_Literal { lexical_form = ""; datatype = xsd_string; lang_tag = None }
          in
          bindings := (name, term) :: !bindings
        done with Not_found -> ());

       rows := List.rev !bindings :: !rows
     done with Not_found -> ());

    SRX_Bindings { vars; rows = List.rev !rows }
  end
