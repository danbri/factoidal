open Prims
type pstate = {
  inp: Prims.string ;
  pos: Prims.nat }
let __proj__Mkpstate__item__inp (projectee : pstate) : Prims.string=
  match projectee with | { inp; pos;_} -> inp
let __proj__Mkpstate__item__pos (projectee : pstate) : Prims.nat=
  match projectee with | { inp; pos;_} -> pos
let mk_pstate (s : Prims.string) : pstate= { inp = s; pos = Prims.int_zero }
let ps_eof (ps : pstate) : Prims.bool= ps.pos >= (FStar_String.strlen ps.inp)
let ps_peek (ps : pstate) : FStar_Char.char FStar_Pervasives_Native.option=
  if ps_eof ps
  then FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.Some (FStar_String.index ps.inp ps.pos)
let ps_advance (ps : pstate) (n : Prims.nat) : pstate=
  { inp = (ps.inp); pos = (ps.pos + n) }
let ps_remaining (ps : pstate) : Prims.string=
  if ps_eof ps
  then ""
  else FStar_String.sub ps.inp ps.pos ((FStar_String.strlen ps.inp) - ps.pos)
let ps_char_at (ps : pstate) (offset : Prims.nat) :
  FStar_Char.char FStar_Pervasives_Native.option=
  let i = ps.pos + offset in
  if i >= (FStar_String.strlen ps.inp)
  then FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.Some (FStar_String.index ps.inp i)
let is_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let rec skip_ws (ps : pstate) : pstate=
  match ps_peek ps with
  | FStar_Pervasives_Native.None -> ps
  | FStar_Pervasives_Native.Some c ->
      if is_ws c
      then skip_ws (ps_advance ps Prims.int_one)
      else
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x23))
        then skip_line_comment (ps_advance ps Prims.int_one)
        else ps
and skip_line_comment (ps : pstate) : pstate=
  match ps_peek ps with
  | FStar_Pervasives_Native.None -> ps
  | FStar_Pervasives_Native.Some c ->
      let code = FStar_Char.int_of_char c in
      if (code = (Prims.of_int (0x0A))) || (code = (Prims.of_int (0x0D)))
      then skip_ws (ps_advance ps Prims.int_one)
      else skip_line_comment (ps_advance ps Prims.int_one)
let ps_starts_with (ps : pstate) (s : Prims.string) : Prims.bool=
  let slen = FStar_String.strlen s in
  let ilen = FStar_String.strlen ps.inp in
  if (ps.pos + slen) > ilen
  then false
  else (FStar_String.sub ps.inp ps.pos slen) = s
let ps_starts_with_ci (ps : pstate) (s : Prims.string) : Prims.bool=
  let slen = FStar_String.strlen s in
  let ilen = FStar_String.strlen ps.inp in
  if (ps.pos + slen) > ilen
  then false
  else
    (FStar_String.lowercase (FStar_String.sub ps.inp ps.pos slen)) =
      (FStar_String.lowercase s)
let ps_consume (ps : pstate) (s : Prims.string) :
  pstate FStar_Pervasives_Native.option=
  if ps_starts_with_ci ps s
  then FStar_Pervasives_Native.Some (ps_advance ps (FStar_String.strlen s))
  else FStar_Pervasives_Native.None
let ps_expect (ps : pstate) (s : Prims.string) :
  pstate FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in ps_consume ps1 s
let is_alpha (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
    ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A))))
let is_digit (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let is_alnum (c : FStar_Char.char) : Prims.bool= (is_alpha c) || (is_digit c)
let is_pn_chars_base (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((is_alpha c) ||
      ((code >= (Prims.of_int (0xC0))) && (code <= (Prims.of_int (0xD6)))))
     || ((code >= (Prims.of_int (0xD8))) && (code <= (Prims.of_int (0xF6)))))
    || ((code >= (Prims.of_int (0xF8))) && (code <= (Prims.of_int (0x2FF))))
let is_pn_chars_u (c : FStar_Char.char) : Prims.bool=
  (is_pn_chars_base c) ||
    ((FStar_Char.int_of_char c) = (Prims.of_int (0x5F)))
let is_pn_chars (c : FStar_Char.char) : Prims.bool=
  ((((is_pn_chars_u c) || (is_digit c)) ||
      ((FStar_Char.int_of_char c) = (Prims.of_int (0x2D))))
     || ((FStar_Char.int_of_char c) = (Prims.of_int (0x2E))))
    || ((FStar_Char.int_of_char c) = (Prims.of_int (0xB7)))
let parse_iriref (ps : pstate) :
  (Prims.string * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x3C)) ->
      let ps2 = ps_advance ps1 Prims.int_one in
      let rec collect ps3 acc =
        match ps_peek ps3 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some c1 ->
            if (FStar_Char.int_of_char c1) = (Prims.of_int (0x3E))
            then
              FStar_Pervasives_Native.Some
                ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
                  (ps_advance ps3 Prims.int_one))
            else collect (ps_advance ps3 Prims.int_one) (c1 :: acc) in
      collect ps2 []
  | uu___ -> FStar_Pervasives_Native.None
let parse_variable (ps : pstate) :
  (Prims.string * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      ((FStar_Char.int_of_char c) = (Prims.of_int (0x3F))) ||
        ((FStar_Char.int_of_char c) = (Prims.of_int (0x24)))
      ->
      let ps2 = ps_advance ps1 Prims.int_one in
      let rec collect ps3 acc =
        match ps_peek ps3 with
        | FStar_Pervasives_Native.Some c1 when
            (is_pn_chars_u c1) || (is_digit c1) ->
            collect (ps_advance ps3 Prims.int_one) (c1 :: acc)
        | uu___ ->
            if Prims.uu___is_Nil acc
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
                  ps3) in
      collect ps2 []
  | uu___ -> FStar_Pervasives_Native.None
let parse_pname_ns (ps : pstate) :
  (Prims.string * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let rec collect ps2 acc =
    match ps_peek ps2 with
    | FStar_Pervasives_Native.Some c when
        (FStar_Char.int_of_char c) = (Prims.of_int (0x3A)) ->
        FStar_Pervasives_Native.Some
          ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
            (ps_advance ps2 Prims.int_one))
    | FStar_Pervasives_Native.Some c when is_pn_chars c ->
        collect (ps_advance ps2 Prims.int_one) (c :: acc)
    | uu___ ->
        if Prims.uu___is_Nil acc
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.None in
  collect ps1 []
let parse_pname_ln (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (RDF_Graph_Executable.wf_iri * pstate) FStar_Pervasives_Native.option=
  let ps_orig = ps in
  let ps1 = skip_ws ps in
  match parse_pname_ns ps1 with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (prefix, ps2) ->
      (match FStar_List_Tot_Base.assoc prefix prefixes with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some base_iri ->
           let rec collect ps3 acc =
             match ps_peek ps3 with
             | FStar_Pervasives_Native.Some c when is_pn_chars c ->
                 collect (ps_advance ps3 Prims.int_one) (c :: acc)
             | uu___ ->
                 ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
                   ps3) in
           let uu___ = collect ps2 [] in
           (match uu___ with
            | (local, ps3) ->
                let full_iri = Prims.strcat base_iri local in
                if RDF_Graph_Executable.is_iri full_iri
                then FStar_Pervasives_Native.Some (full_iri, ps3)
                else FStar_Pervasives_Native.None))
let resolve_relative_iri
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (iri : Prims.string) : Prims.string=
  if (FStar_String.strlen iri) = Prims.int_zero
  then
    match base with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None -> iri
  else
    (let chars = FStar_String.list_of_string iri in
     let rec has_scheme cs =
       match cs with
       | [] -> false
       | c::rest ->
           let code = FStar_Char.int_of_char c in
           if code = (Prims.of_int (0x3A))
           then true
           else
             if code = (Prims.of_int (0x2F))
             then false
             else
               if
                 ((((is_alpha c) || (is_digit c)) ||
                     (code = (Prims.of_int (0x2B))))
                    || (code = (Prims.of_int (0x2D))))
                   || (code = (Prims.of_int (0x2E)))
               then has_scheme rest
               else false in
     if has_scheme chars
     then iri
     else
       (match base with
        | FStar_Pervasives_Native.None -> iri
        | FStar_Pervasives_Native.Some b ->
            if
              ((FStar_String.strlen iri) > Prims.int_zero) &&
                ((FStar_String.sub iri Prims.int_zero Prims.int_one) = "#")
            then Prims.strcat b iri
            else
              (let blen = FStar_String.strlen b in
               let rec find_last_slash i =
                 if i = Prims.int_zero
                 then Prims.int_zero
                 else
                   if
                     (FStar_String.sub b (i - Prims.int_one) Prims.int_one) =
                       "/"
                   then i
                   else find_last_slash (i - Prims.int_one) in
               let prefix_str =
                 FStar_String.sub b Prims.int_zero (find_last_slash blen) in
               Prims.strcat prefix_str iri)))
let parse_iri (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (RDF_Graph_Executable.wf_iri * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x3C)) ->
      (match parse_iriref ps1 with
       | FStar_Pervasives_Native.Some (iri, ps2) ->
           if RDF_Graph_Executable.is_iri iri
           then FStar_Pervasives_Native.Some (iri, ps2)
           else
             (let base = FStar_List_Tot_Base.assoc "__base__" prefixes in
              let resolved = resolve_relative_iri base iri in
              if RDF_Graph_Executable.is_iri resolved
              then FStar_Pervasives_Native.Some (resolved, ps2)
              else FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> parse_pname_ln ps1 prefixes
let rec parse_string_literal (ps : pstate) :
  (Prims.string * pstate) FStar_Pervasives_Native.option=
  let ps0 = skip_ws ps in
  let c0 = ps_peek ps0 in
  if
    (c0 =
       (FStar_Pervasives_Native.Some
          (FStar_Char.char_of_int (Prims.of_int (0x22)))))
      ||
      (c0 =
         (FStar_Pervasives_Native.Some
            (FStar_Char.char_of_int (Prims.of_int (0x27)))))
  then
    let qcode =
      match c0 with
      | FStar_Pervasives_Native.Some c -> FStar_Char.int_of_char c
      | FStar_Pervasives_Native.None -> Prims.int_zero in
    parse_string_inner ps0 qcode
  else FStar_Pervasives_Native.None
and parse_string_inner (ps : pstate) (qcode : Prims.int) :
  (Prims.string * pstate) FStar_Pervasives_Native.option=
  let is_long =
    match ((ps_char_at ps Prims.int_one), (ps_char_at ps (Prims.of_int (2))))
    with
    | (FStar_Pervasives_Native.Some c1, FStar_Pervasives_Native.Some c2) ->
        ((FStar_Char.int_of_char c1) = qcode) &&
          ((FStar_Char.int_of_char c2) = qcode)
    | uu___ -> false in
  if is_long
  then
    let ps1 = ps_advance ps (Prims.of_int (3)) in
    let rec collect ps2 acc =
      match ps_peek ps2 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ch ->
          if (FStar_Char.int_of_char ch) = qcode
          then
            (match ((ps_char_at ps2 Prims.int_one),
                     (ps_char_at ps2 (Prims.of_int (2))))
             with
             | (FStar_Pervasives_Native.Some c1, FStar_Pervasives_Native.Some
                c2) when
                 ((FStar_Char.int_of_char c1) = qcode) &&
                   ((FStar_Char.int_of_char c2) = qcode)
                 ->
                 FStar_Pervasives_Native.Some
                   ((FStar_String.string_of_list
                       (FStar_List_Tot_Base.rev acc)),
                     (ps_advance ps2 (Prims.of_int (3))))
             | uu___ -> collect (ps_advance ps2 Prims.int_one) (ch :: acc))
          else
            if (FStar_Char.int_of_char ch) = (Prims.of_int (0x5C))
            then
              (match ps_char_at ps2 Prims.int_one with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some c2 ->
                   let escaped =
                     match FStar_Char.int_of_char c2 with
                     | uu___1 when uu___1 = (Prims.of_int (0x6E)) ->
                         FStar_Char.char_of_int (Prims.of_int (0x0A))
                     | uu___1 when uu___1 = (Prims.of_int (0x74)) ->
                         FStar_Char.char_of_int (Prims.of_int (0x09))
                     | uu___1 when uu___1 = (Prims.of_int (0x72)) ->
                         FStar_Char.char_of_int (Prims.of_int (0x0D))
                     | uu___1 -> c2 in
                   collect (ps_advance ps2 (Prims.of_int (2))) (escaped ::
                     acc))
            else collect (ps_advance ps2 Prims.int_one) (ch :: acc) in
    collect ps1 []
  else
    (let ps1 = ps_advance ps Prims.int_one in
     let rec collect ps2 acc =
       match ps_peek ps2 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ch ->
           if (FStar_Char.int_of_char ch) = qcode
           then
             FStar_Pervasives_Native.Some
               ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
                 (ps_advance ps2 Prims.int_one))
           else
             if (FStar_Char.int_of_char ch) = (Prims.of_int (0x5C))
             then
               (match ps_char_at ps2 Prims.int_one with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some c2 ->
                    let escaped =
                      match FStar_Char.int_of_char c2 with
                      | uu___2 when uu___2 = (Prims.of_int (0x6E)) ->
                          FStar_Char.char_of_int (Prims.of_int (0x0A))
                      | uu___2 when uu___2 = (Prims.of_int (0x74)) ->
                          FStar_Char.char_of_int (Prims.of_int (0x09))
                      | uu___2 when uu___2 = (Prims.of_int (0x72)) ->
                          FStar_Char.char_of_int (Prims.of_int (0x0D))
                      | uu___2 when uu___2 = (Prims.of_int (0x5C)) ->
                          FStar_Char.char_of_int (Prims.of_int (0x5C))
                      | uu___2 when uu___2 = (Prims.of_int (0x22)) ->
                          FStar_Char.char_of_int (Prims.of_int (0x22))
                      | uu___2 when uu___2 = (Prims.of_int (0x27)) ->
                          FStar_Char.char_of_int (Prims.of_int (0x27))
                      | uu___2 -> c2 in
                    collect (ps_advance ps2 (Prims.of_int (2))) (escaped ::
                      acc))
             else
               if
                 ((FStar_Char.int_of_char ch) = (Prims.of_int (0x0A))) ||
                   ((FStar_Char.int_of_char ch) = (Prims.of_int (0x0D)))
               then FStar_Pervasives_Native.None
               else collect (ps_advance ps2 Prims.int_one) (ch :: acc) in
     collect ps1 [])
let parse_rdf_literal (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (RDF_Graph_Executable.wf_literal * pstate) FStar_Pervasives_Native.option=
  match parse_string_literal ps with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (lex, ps1) ->
      (match ps_peek ps1 with
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x40)) ->
           let ps2 = ps_advance ps1 Prims.int_one in
           let rec collect ps3 acc =
             match ps_peek ps3 with
             | FStar_Pervasives_Native.Some c1 when
                 ((is_alpha c1) || (is_digit c1)) ||
                   ((FStar_Char.int_of_char c1) = (Prims.of_int (0x2D)))
                 -> collect (ps_advance ps3 Prims.int_one) (c1 :: acc)
             | uu___ ->
                 ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
                   ps3) in
           let uu___ = collect ps2 [] in
           (match uu___ with
            | (lang, ps3) ->
                if (FStar_String.strlen lang) = Prims.int_zero
                then FStar_Pervasives_Native.None
                else
                  (let lit =
                     {
                       RDF_Graph_Executable.lexical_form = lex;
                       RDF_Graph_Executable.datatype =
                         RDF_Graph_Executable.rdf_lang_string;
                       RDF_Graph_Executable.lang_tag =
                         (FStar_Pervasives_Native.Some lang)
                     } in
                   FStar_Pervasives_Native.Some (lit, ps3)))
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x5E)) ->
           (match ps_char_at ps1 Prims.int_one with
            | FStar_Pervasives_Native.Some c2 when
                (FStar_Char.int_of_char c2) = (Prims.of_int (0x5E)) ->
                let ps2 = ps_advance ps1 (Prims.of_int (2)) in
                (match parse_iri ps2 prefixes with
                 | FStar_Pervasives_Native.Some (dt, ps3) ->
                     let lit =
                       {
                         RDF_Graph_Executable.lexical_form = lex;
                         RDF_Graph_Executable.datatype = dt;
                         RDF_Graph_Executable.lang_tag =
                           FStar_Pervasives_Native.None
                       } in
                     FStar_Pervasives_Native.Some (lit, ps3)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | uu___ ->
                let lit =
                  {
                    RDF_Graph_Executable.lexical_form = lex;
                    RDF_Graph_Executable.datatype =
                      RDF_Graph_Executable.xsd_string;
                    RDF_Graph_Executable.lang_tag =
                      FStar_Pervasives_Native.None
                  } in
                FStar_Pervasives_Native.Some (lit, ps1))
       | uu___ ->
           let lit =
             {
               RDF_Graph_Executable.lexical_form = lex;
               RDF_Graph_Executable.datatype =
                 RDF_Graph_Executable.xsd_string;
               RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
             } in
           FStar_Pervasives_Native.Some (lit, ps1))
let parse_boolean (ps : pstate) :
  (Prims.bool * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "true" with
  | FStar_Pervasives_Native.Some ps2 ->
      FStar_Pervasives_Native.Some (true, ps2)
  | FStar_Pervasives_Native.None ->
      (match ps_consume ps1 "false" with
       | FStar_Pervasives_Native.Some ps2 ->
           FStar_Pervasives_Native.Some (false, ps2)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let parse_numeric (ps : pstate) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let start = ps1.pos in
  let ps2 =
    match ps_peek ps1 with
    | FStar_Pervasives_Native.Some c when
        ((FStar_Char.int_of_char c) = (Prims.of_int (0x2B))) ||
          ((FStar_Char.int_of_char c) = (Prims.of_int (0x2D)))
        -> ps_advance ps1 Prims.int_one
    | uu___ -> ps1 in
  let rec digits ps3 =
    match ps_peek ps3 with
    | FStar_Pervasives_Native.Some c when is_digit c ->
        digits (ps_advance ps3 Prims.int_one)
    | uu___ -> ps3 in
  let ps_after_int = digits ps2 in
  if
    (ps_after_int.pos = ps2.pos) &&
      (match ps_peek ps2 with
       | FStar_Pervasives_Native.Some c ->
           (FStar_Char.int_of_char c) <> (Prims.of_int (0x2E))
       | FStar_Pervasives_Native.None -> true)
  then FStar_Pervasives_Native.None
  else
    (match ps_peek ps_after_int with
     | FStar_Pervasives_Native.Some c when
         (FStar_Char.int_of_char c) = (Prims.of_int (0x2E)) ->
         let ps21 = digits (ps_advance ps_after_int Prims.int_one) in
         (match ps_peek ps21 with
          | FStar_Pervasives_Native.Some c1 when
              ((FStar_Char.int_of_char c1) = (Prims.of_int (0x45))) ||
                ((FStar_Char.int_of_char c1) = (Prims.of_int (0x65)))
              ->
              let ps3 = ps_advance ps21 Prims.int_one in
              let ps31 =
                match ps_peek ps3 with
                | FStar_Pervasives_Native.Some c2 when
                    ((FStar_Char.int_of_char c2) = (Prims.of_int (0x2B))) ||
                      ((FStar_Char.int_of_char c2) = (Prims.of_int (0x2D)))
                    -> ps_advance ps3 Prims.int_one
                | uu___1 -> ps3 in
              let ps32 = digits ps31 in
              let s = FStar_String.sub ps2.inp start (ps32.pos - start) in
              FStar_Pervasives_Native.Some
                ((SPARQL11_Algebra.E_DoubleLit s), ps32)
          | uu___1 ->
              let s = FStar_String.sub ps2.inp start (ps21.pos - start) in
              FStar_Pervasives_Native.Some
                ((SPARQL11_Algebra.E_DecimalLit s), ps21))
     | uu___1 ->
         if ps_after_int.pos > start
         then
           let s = FStar_String.sub ps2.inp start (ps_after_int.pos - start) in
           let chars = FStar_String.list_of_string s in
           let rec parse_int_chars cs neg acc =
             match cs with
             | [] -> if neg then Prims.int_zero - acc else acc
             | c::rest ->
                 let code = FStar_Char.int_of_char c in
                 if code = (Prims.of_int (0x2B))
                 then parse_int_chars rest false acc
                 else
                   if code = (Prims.of_int (0x2D))
                   then parse_int_chars rest true acc
                   else
                     parse_int_chars rest neg
                       ((acc * (Prims.of_int (10))) +
                          (code - (Prims.of_int (0x30)))) in
           let n = parse_int_chars chars false Prims.int_zero in
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.E_NumericLit n), ps_after_int)
         else FStar_Pervasives_Native.None)
let parse_prefix_decl (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option) :
  ((Prims.string * RDF_Graph_Executable.wf_iri) * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "PREFIX" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      (match parse_pname_ns ps3 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (prefix, ps4) ->
           let ps5 = skip_ws ps4 in
           (match parse_iriref ps5 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (iri, ps6) ->
                if RDF_Graph_Executable.is_iri iri
                then FStar_Pervasives_Native.Some ((prefix, iri), ps6)
                else
                  if (FStar_String.strlen iri) = Prims.int_zero
                  then
                    (match base with
                     | FStar_Pervasives_Native.Some b ->
                         FStar_Pervasives_Native.Some ((prefix, b), ps6)
                     | FStar_Pervasives_Native.None ->
                         let dummy = "urn:empty:" in
                         FStar_Pervasives_Native.Some ((prefix, dummy), ps6))
                  else FStar_Pervasives_Native.Some ((prefix, iri), ps6)))
let parse_base_decl (ps : pstate) :
  (RDF_Graph_Executable.wf_iri * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "BASE" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      (match parse_iriref ps3 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (iri, ps4) ->
           if RDF_Graph_Executable.is_iri iri
           then FStar_Pervasives_Native.Some (iri, ps4)
           else FStar_Pervasives_Native.None)
let rec parse_prologue (ps : pstate)
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option * (Prims.string
    * RDF_Graph_Executable.wf_iri) Prims.list * pstate)=
  let ps1 = skip_ws ps in
  match parse_base_decl ps1 with
  | FStar_Pervasives_Native.Some (iri, ps2) ->
      parse_prologue ps2 (FStar_Pervasives_Native.Some iri) prefixes
  | FStar_Pervasives_Native.None ->
      (match parse_prefix_decl ps1 prefixes base with
       | FStar_Pervasives_Native.Some ((prefix, raw_iri), ps2) ->
           let resolved = resolve_relative_iri base raw_iri in
           let iri =
             if RDF_Graph_Executable.is_iri resolved
             then resolved
             else raw_iri in
           parse_prologue ps2 base ((prefix, iri) :: prefixes)
       | FStar_Pervasives_Native.None -> (base, prefixes, ps1))
let parse_nat_digits_inline (ps : pstate) :
  (Prims.nat * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let start = ps1.pos in
  let rec skip_digits ps2 =
    match ps_peek ps2 with
    | FStar_Pervasives_Native.Some c when is_digit c ->
        skip_digits (ps_advance ps2 Prims.int_one)
    | uu___ -> ps2 in
  let ps2 = skip_digits ps1 in
  if ps2.pos = start
  then FStar_Pervasives_Native.None
  else
    (let s = FStar_String.sub ps1.inp start (ps2.pos - start) in
     let chars = FStar_String.list_of_string s in
     let rec to_int cs acc =
       match cs with
       | [] -> acc
       | c::rest ->
           to_int rest
             ((acc * (Prims.of_int (10))) +
                ((FStar_Char.int_of_char c) - (Prims.of_int (0x30)))) in
     let n = to_int chars Prims.int_zero in
     if n >= Prims.int_zero
     then FStar_Pervasives_Native.Some (n, ps2)
     else FStar_Pervasives_Native.None)
type pred_or_path =
  | Pred_Term of SPARQL11_Algebra.pattern_term 
  | Pred_Path of SPARQL11_Algebra.property_path 
let uu___is_Pred_Term (projectee : pred_or_path) : Prims.bool=
  match projectee with | Pred_Term _0 -> true | uu___ -> false
let __proj__Pred_Term__item___0 (projectee : pred_or_path) :
  SPARQL11_Algebra.pattern_term= match projectee with | Pred_Term _0 -> _0
let uu___is_Pred_Path (projectee : pred_or_path) : Prims.bool=
  match projectee with | Pred_Path _0 -> true | uu___ -> false
let __proj__Pred_Path__item___0 (projectee : pred_or_path) :
  SPARQL11_Algebra.property_path= match projectee with | Pred_Path _0 -> _0
let ggp_join (a : SPARQL11_Algebra.group_graph_pattern)
  (b : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  if a = SPARQL11_Algebra.GP_Empty
  then b
  else
    if b = SPARQL11_Algebra.GP_Empty
    then a
    else SPARQL11_Algebra.GP_Join (a, b)
let rec triples_to_ggp
  (pending_tps : SPARQL11_Algebra.triple_pattern Prims.list)
  (rest :
    (SPARQL11_Algebra.triple_pattern,
      (SPARQL11_Algebra.pattern_subject * SPARQL11_Algebra.property_path *
        SPARQL11_Algebra.pattern_term))
      FStar_Pervasives.either Prims.list)
  : SPARQL11_Algebra.group_graph_pattern=
  match rest with
  | [] ->
      if Prims.uu___is_Nil pending_tps
      then SPARQL11_Algebra.GP_Empty
      else SPARQL11_Algebra.GP_BGP (FStar_List_Tot_Base.rev pending_tps)
  | (FStar_Pervasives.Inl tp)::tl -> triples_to_ggp (tp :: pending_tps) tl
  | (FStar_Pervasives.Inr (s, pp, o))::tl ->
      let bgp_part =
        if Prims.uu___is_Nil pending_tps
        then SPARQL11_Algebra.GP_Empty
        else SPARQL11_Algebra.GP_BGP (FStar_List_Tot_Base.rev pending_tps) in
      let pp_part = SPARQL11_Algebra.GP_PropertyPath (s, pp, o) in
      ggp_join (ggp_join bgp_part pp_part) (triples_to_ggp [] tl)
let rec parse_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  parse_or_expr ps prefixes
and parse_or_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  match parse_and_expr ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (left, ps1) ->
      let rec loop left1 ps2 =
        let ps' = skip_ws ps2 in
        match ps_consume ps' "||" with
        | FStar_Pervasives_Native.Some ps'1 ->
            (match parse_and_expr ps'1 prefixes with
             | FStar_Pervasives_Native.Some (right, ps'2) ->
                 loop (SPARQL11_Algebra.E_Or (left1, right)) ps'2
             | FStar_Pervasives_Native.None -> (left1, ps2))
        | FStar_Pervasives_Native.None -> (left1, ps2) in
      FStar_Pervasives_Native.Some (loop left ps1)
and parse_and_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  match parse_relational_expr ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (left, ps1) ->
      let rec loop left1 ps2 =
        let ps' = skip_ws ps2 in
        match ps_consume ps' "&&" with
        | FStar_Pervasives_Native.Some ps'1 ->
            (match parse_relational_expr ps'1 prefixes with
             | FStar_Pervasives_Native.Some (right, ps'2) ->
                 loop (SPARQL11_Algebra.E_And (left1, right)) ps'2
             | FStar_Pervasives_Native.None -> (left1, ps2))
        | FStar_Pervasives_Native.None -> (left1, ps2) in
      FStar_Pervasives_Native.Some (loop left ps1)
and parse_relational_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  match parse_additive_expr ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (left, ps1) ->
      let ps' = skip_ws ps1 in
      (match ps_consume ps' "NOT" with
       | FStar_Pervasives_Native.Some ps2 ->
           let ps21 = skip_ws ps2 in
           (match ps_consume ps21 "IN" with
            | FStar_Pervasives_Native.Some ps22 ->
                (match parse_expr_list ps22 prefixes with
                 | FStar_Pervasives_Native.Some (args, ps23) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.E_NotIn (left, args)), ps23)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some (left, ps1))
            | FStar_Pervasives_Native.None ->
                parse_comparison left ps' prefixes)
       | FStar_Pervasives_Native.None ->
           (match ps_consume ps' "IN" with
            | FStar_Pervasives_Native.Some ps2 ->
                (match parse_expr_list ps2 prefixes with
                 | FStar_Pervasives_Native.Some (args, ps21) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.E_In (left, args)), ps21)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some (left, ps1))
            | FStar_Pervasives_Native.None ->
                parse_comparison left ps' prefixes))
and parse_comparison (left : SPARQL11_Algebra.expr) (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  match ps_consume ps "<=" with
  | FStar_Pervasives_Native.Some ps' ->
      (match parse_additive_expr ps' prefixes with
       | FStar_Pervasives_Native.Some (right, ps'1) ->
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.E_Compare
                 (SPARQL11_Algebra.CmpLe, left, right)), ps'1)
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (left, ps))
  | FStar_Pervasives_Native.None ->
      (match ps_consume ps ">=" with
       | FStar_Pervasives_Native.Some ps' ->
           (match parse_additive_expr ps' prefixes with
            | FStar_Pervasives_Native.Some (right, ps'1) ->
                FStar_Pervasives_Native.Some
                  ((SPARQL11_Algebra.E_Compare
                      (SPARQL11_Algebra.CmpGe, left, right)), ps'1)
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (left, ps))
       | FStar_Pervasives_Native.None ->
           (match ps_consume ps "!=" with
            | FStar_Pervasives_Native.Some ps' ->
                (match parse_additive_expr ps' prefixes with
                 | FStar_Pervasives_Native.Some (right, ps'1) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.E_Compare
                           (SPARQL11_Algebra.CmpNe, left, right)), ps'1)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some (left, ps))
            | FStar_Pervasives_Native.None ->
                (match ps_consume ps "=" with
                 | FStar_Pervasives_Native.Some ps' ->
                     (match parse_additive_expr ps' prefixes with
                      | FStar_Pervasives_Native.Some (right, ps'1) ->
                          FStar_Pervasives_Native.Some
                            ((SPARQL11_Algebra.E_Compare
                                (SPARQL11_Algebra.CmpEq, left, right)), ps'1)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some (left, ps))
                 | FStar_Pervasives_Native.None ->
                     (match ps_consume ps "<" with
                      | FStar_Pervasives_Native.Some ps' ->
                          (match parse_additive_expr ps' prefixes with
                           | FStar_Pervasives_Native.Some (right, ps'1) ->
                               FStar_Pervasives_Native.Some
                                 ((SPARQL11_Algebra.E_Compare
                                     (SPARQL11_Algebra.CmpLt, left, right)),
                                   ps'1)
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some (left, ps))
                      | FStar_Pervasives_Native.None ->
                          (match ps_consume ps ">" with
                           | FStar_Pervasives_Native.Some ps' ->
                               (match parse_additive_expr ps' prefixes with
                                | FStar_Pervasives_Native.Some (right, ps'1)
                                    ->
                                    FStar_Pervasives_Native.Some
                                      ((SPARQL11_Algebra.E_Compare
                                          (SPARQL11_Algebra.CmpGt, left,
                                            right)), ps'1)
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.Some (left, ps))
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some (left, ps))))))
and parse_additive_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  match parse_multiplicative_expr ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (left, ps1) ->
      let rec loop left1 ps2 =
        let ps' = skip_ws ps2 in
        match ps_peek ps' with
        | FStar_Pervasives_Native.Some c when
            (FStar_Char.int_of_char c) = (Prims.of_int (0x2B)) ->
            let ps'1 = ps_advance ps' Prims.int_one in
            (match parse_multiplicative_expr ps'1 prefixes with
             | FStar_Pervasives_Native.Some (right, ps'2) ->
                 loop
                   (SPARQL11_Algebra.E_Arith
                      (SPARQL11_Algebra.Add, left1, right)) ps'2
             | FStar_Pervasives_Native.None -> (left1, ps2))
        | FStar_Pervasives_Native.Some c when
            (FStar_Char.int_of_char c) = (Prims.of_int (0x2D)) ->
            let ps'1 = ps_advance ps' Prims.int_one in
            (match parse_multiplicative_expr ps'1 prefixes with
             | FStar_Pervasives_Native.Some (right, ps'2) ->
                 loop
                   (SPARQL11_Algebra.E_Arith
                      (SPARQL11_Algebra.Sub, left1, right)) ps'2
             | FStar_Pervasives_Native.None -> (left1, ps2))
        | uu___ -> (left1, ps2) in
      FStar_Pervasives_Native.Some (loop left ps1)
and parse_multiplicative_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  match parse_unary_expr ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (left, ps1) ->
      let rec loop left1 ps2 =
        let ps' = skip_ws ps2 in
        match ps_peek ps' with
        | FStar_Pervasives_Native.Some c when
            (FStar_Char.int_of_char c) = (Prims.of_int (0x2A)) ->
            let ps'1 = ps_advance ps' Prims.int_one in
            (match parse_unary_expr ps'1 prefixes with
             | FStar_Pervasives_Native.Some (right, ps'2) ->
                 loop
                   (SPARQL11_Algebra.E_Arith
                      (SPARQL11_Algebra.Mul, left1, right)) ps'2
             | FStar_Pervasives_Native.None -> (left1, ps2))
        | FStar_Pervasives_Native.Some c when
            (FStar_Char.int_of_char c) = (Prims.of_int (0x2F)) ->
            let ps'1 = ps_advance ps' Prims.int_one in
            (match parse_unary_expr ps'1 prefixes with
             | FStar_Pervasives_Native.Some (right, ps'2) ->
                 loop
                   (SPARQL11_Algebra.E_Arith
                      (SPARQL11_Algebra.Div, left1, right)) ps'2
             | FStar_Pervasives_Native.None -> (left1, ps2))
        | uu___ -> (left1, ps2) in
      FStar_Pervasives_Native.Some (loop left ps1)
and parse_unary_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x21)) ->
      (match ps_char_at ps1 Prims.int_one with
       | FStar_Pervasives_Native.Some c2 when
           (FStar_Char.int_of_char c2) = (Prims.of_int (0x3D)) ->
           parse_primary_expr ps1 prefixes
       | uu___ ->
           let ps2 = ps_advance ps1 Prims.int_one in
           (match parse_primary_expr ps2 prefixes with
            | FStar_Pervasives_Native.Some (e, ps3) ->
                FStar_Pervasives_Native.Some
                  ((SPARQL11_Algebra.E_Not e), ps3)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x2D)) ->
      let ps2 = ps_advance ps1 Prims.int_one in
      (match parse_primary_expr ps2 prefixes with
       | FStar_Pervasives_Native.Some (e, ps3) ->
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.E_UnaryMinus e), ps3)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x2B)) ->
      let ps2 = ps_advance ps1 Prims.int_one in
      parse_primary_expr ps2 prefixes
  | uu___ -> parse_primary_expr ps1 prefixes
and parse_primary_expr (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
      let ps2 = ps_advance ps1 Prims.int_one in
      (match parse_expr ps2 prefixes with
       | FStar_Pervasives_Native.Some (e, ps3) ->
           (match ps_expect ps3 ")" with
            | FStar_Pervasives_Native.Some ps4 ->
                FStar_Pervasives_Native.Some (e, ps4)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ ->
      (match parse_variable ps1 with
       | FStar_Pervasives_Native.Some (v, ps2) ->
           FStar_Pervasives_Native.Some ((SPARQL11_Algebra.E_Var v), ps2)
       | FStar_Pervasives_Native.None ->
           (match parse_builtin_call ps1 prefixes with
            | FStar_Pervasives_Native.Some r ->
                FStar_Pervasives_Native.Some r
            | FStar_Pervasives_Native.None ->
                (match parse_iri ps1 prefixes with
                 | FStar_Pervasives_Native.Some (iri, ps2) ->
                     let ps' = skip_ws ps2 in
                     (match ps_peek ps' with
                      | FStar_Pervasives_Native.Some c when
                          (FStar_Char.int_of_char c) = (Prims.of_int (0x28))
                          ->
                          (match parse_expr_list ps' prefixes with
                           | FStar_Pervasives_Native.Some (args, ps'1) ->
                               FStar_Pervasives_Native.Some
                                 ((SPARQL11_Algebra.E_FunctionCall
                                     (iri, args)), ps'1)
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some
                                 ((SPARQL11_Algebra.E_IRI iri), ps2))
                      | uu___1 ->
                          FStar_Pervasives_Native.Some
                            ((SPARQL11_Algebra.E_IRI iri), ps2))
                 | FStar_Pervasives_Native.None ->
                     (match parse_rdf_literal ps1 prefixes with
                      | FStar_Pervasives_Native.Some (lit, ps2) ->
                          FStar_Pervasives_Native.Some
                            ((SPARQL11_Algebra.E_Literal lit), ps2)
                      | FStar_Pervasives_Native.None ->
                          (match parse_boolean ps1 with
                           | FStar_Pervasives_Native.Some (b, ps2) ->
                               FStar_Pervasives_Native.Some
                                 ((SPARQL11_Algebra.E_BoolLit b), ps2)
                           | FStar_Pervasives_Native.None ->
                               parse_numeric ps1)))))
and parse_builtin_call (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let try_1arg kw mk =
    match ps_consume ps1 kw with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some ps2 ->
        let ps3 = skip_ws ps2 in
        (match ps_expect ps3 "(" with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some ps4 ->
             (match parse_expr ps4 prefixes with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (e, ps5) ->
                  (match ps_expect ps5 ")" with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some ps6 ->
                       FStar_Pervasives_Native.Some ((mk e), ps6)))) in
  let try_2arg kw mk =
    match ps_consume ps1 kw with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some ps2 ->
        let ps3 = skip_ws ps2 in
        (match ps_expect ps3 "(" with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some ps4 ->
             (match parse_expr ps4 prefixes with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (e1, ps5) ->
                  (match ps_expect ps5 "," with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some ps6 ->
                       (match parse_expr ps6 prefixes with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (e2, ps7) ->
                            (match ps_expect ps7 ")" with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some ps8 ->
                                 FStar_Pervasives_Native.Some
                                   ((mk e1 e2), ps8)))))) in
  match ps_consume ps1 "BOUND" with
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      (match ps_expect ps3 "(" with
       | FStar_Pervasives_Native.Some ps4 ->
           (match parse_variable ps4 with
            | FStar_Pervasives_Native.Some (v, ps5) ->
                (match ps_expect ps5 ")" with
                 | FStar_Pervasives_Native.Some ps6 ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.E_Bound v), ps6)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None ->
      (match ps_consume ps1 "REGEX" with
       | FStar_Pervasives_Native.Some ps2 ->
           let ps3 = skip_ws ps2 in
           (match ps_expect ps3 "(" with
            | FStar_Pervasives_Native.Some ps4 ->
                (match parse_expr ps4 prefixes with
                 | FStar_Pervasives_Native.Some (e1, ps5) ->
                     (match ps_expect ps5 "," with
                      | FStar_Pervasives_Native.Some ps6 ->
                          (match parse_expr ps6 prefixes with
                           | FStar_Pervasives_Native.Some (e2, ps7) ->
                               let ps' = skip_ws ps7 in
                               (match ps_consume ps' "," with
                                | FStar_Pervasives_Native.Some ps'1 ->
                                    (match parse_expr ps'1 prefixes with
                                     | FStar_Pervasives_Native.Some
                                         (e3, ps'2) ->
                                         (match ps_expect ps'2 ")" with
                                          | FStar_Pervasives_Native.Some ps'3
                                              ->
                                              FStar_Pervasives_Native.Some
                                                ((SPARQL11_Algebra.E_Regex
                                                    (e1, e2,
                                                      (FStar_Pervasives_Native.Some
                                                         e3))), ps'3)
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None)
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None)
                                | FStar_Pervasives_Native.None ->
                                    (match ps_expect ps7 ")" with
                                     | FStar_Pervasives_Native.Some ps8 ->
                                         FStar_Pervasives_Native.Some
                                           ((SPARQL11_Algebra.E_Regex
                                               (e1, e2,
                                                 FStar_Pervasives_Native.None)),
                                             ps8)
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None))
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None ->
           (match ps_consume ps1 "IF" with
            | FStar_Pervasives_Native.Some ps2 ->
                let ps3 = skip_ws ps2 in
                (match ps_expect ps3 "(" with
                 | FStar_Pervasives_Native.Some ps4 ->
                     (match parse_expr ps4 prefixes with
                      | FStar_Pervasives_Native.Some (e1, ps5) ->
                          (match ps_expect ps5 "," with
                           | FStar_Pervasives_Native.Some ps6 ->
                               (match parse_expr ps6 prefixes with
                                | FStar_Pervasives_Native.Some (e2, ps7) ->
                                    (match ps_expect ps7 "," with
                                     | FStar_Pervasives_Native.Some ps8 ->
                                         (match parse_expr ps8 prefixes with
                                          | FStar_Pervasives_Native.Some
                                              (e3, ps9) ->
                                              (match ps_expect ps9 ")" with
                                               | FStar_Pervasives_Native.Some
                                                   ps10 ->
                                                   FStar_Pervasives_Native.Some
                                                     ((SPARQL11_Algebra.E_If
                                                         (e1, e2, e3)), ps10)
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None)
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None)
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None)
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None)
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None ->
                (match ps_consume ps1 "EXISTS" with
                 | FStar_Pervasives_Native.Some ps2 ->
                     (match parse_group_graph_pattern ps2 prefixes with
                      | FStar_Pervasives_Native.Some (p, ps3) ->
                          FStar_Pervasives_Native.Some
                            ((SPARQL11_Algebra.E_Exists p), ps3)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.None ->
                     let ps0 = ps1 in
                     (match ps_consume ps1 "NOT" with
                      | FStar_Pervasives_Native.Some ps2 ->
                          let ps3 = skip_ws ps2 in
                          (match ps_consume ps3 "EXISTS" with
                           | FStar_Pervasives_Native.Some ps4 ->
                               (match parse_group_graph_pattern ps4 prefixes
                                with
                                | FStar_Pervasives_Native.Some (p, ps5) ->
                                    FStar_Pervasives_Native.Some
                                      ((SPARQL11_Algebra.E_NotExists p), ps5)
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None)
                           | FStar_Pervasives_Native.None ->
                               let ps4 = ps0 in
                               try_1arg_fallback ps4 prefixes)
                      | FStar_Pervasives_Native.None ->
                          try_1arg_fallback ps1 prefixes))))
and try_1arg_fallback (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  let try1 kw mk =
    match ps_consume ps kw with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some ps' ->
        let ps'1 = skip_ws ps' in
        (match ps_expect ps'1 "(" with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some ps'2 ->
             (match parse_expr ps'2 prefixes with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (e, ps'3) ->
                  (match ps_expect ps'3 ")" with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some ps'4 ->
                       FStar_Pervasives_Native.Some ((mk e), ps'4)))) in
  match try1 "ISIRI" (fun e -> SPARQL11_Algebra.E_IsIRI e) with
  | FStar_Pervasives_Native.Some r -> FStar_Pervasives_Native.Some r
  | FStar_Pervasives_Native.None ->
      (match try1 "ISURI" (fun e -> SPARQL11_Algebra.E_IsIRI e) with
       | FStar_Pervasives_Native.Some r -> FStar_Pervasives_Native.Some r
       | FStar_Pervasives_Native.None ->
           (match try1 "ISBLANK" (fun e -> SPARQL11_Algebra.E_IsBlank e) with
            | FStar_Pervasives_Native.Some r ->
                FStar_Pervasives_Native.Some r
            | FStar_Pervasives_Native.None ->
                (match try1 "ISLITERAL"
                         (fun e -> SPARQL11_Algebra.E_IsLiteral e)
                 with
                 | FStar_Pervasives_Native.Some r ->
                     FStar_Pervasives_Native.Some r
                 | FStar_Pervasives_Native.None ->
                     (match try1 "ISNUMERIC"
                              (fun e -> SPARQL11_Algebra.E_IsNumeric e)
                      with
                      | FStar_Pervasives_Native.Some r ->
                          FStar_Pervasives_Native.Some r
                      | FStar_Pervasives_Native.None ->
                          (match try1 "STR"
                                   (fun e -> SPARQL11_Algebra.E_Str e)
                           with
                           | FStar_Pervasives_Native.Some r ->
                               FStar_Pervasives_Native.Some r
                           | FStar_Pervasives_Native.None ->
                               (match try1 "LANG"
                                        (fun e -> SPARQL11_Algebra.E_Lang e)
                                with
                                | FStar_Pervasives_Native.Some r ->
                                    FStar_Pervasives_Native.Some r
                                | FStar_Pervasives_Native.None ->
                                    (match try1 "DATATYPE"
                                             (fun e ->
                                                SPARQL11_Algebra.E_Datatype e)
                                     with
                                     | FStar_Pervasives_Native.Some r ->
                                         FStar_Pervasives_Native.Some r
                                     | FStar_Pervasives_Native.None ->
                                         (match try1 "IRI"
                                                  (fun e ->
                                                     SPARQL11_Algebra.E_IRI_fn
                                                       e)
                                          with
                                          | FStar_Pervasives_Native.Some r ->
                                              FStar_Pervasives_Native.Some r
                                          | FStar_Pervasives_Native.None ->
                                              (match try1 "URI"
                                                       (fun e ->
                                                          SPARQL11_Algebra.E_IRI_fn
                                                            e)
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   r ->
                                                   FStar_Pervasives_Native.Some
                                                     r
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (match try1 "STRLEN"
                                                            (fun e ->
                                                               SPARQL11_Algebra.E_StrLen
                                                                 e)
                                                    with
                                                    | FStar_Pervasives_Native.Some
                                                        r ->
                                                        FStar_Pervasives_Native.Some
                                                          r
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        (match try1 "UCASE"
                                                                 (fun e ->
                                                                    SPARQL11_Algebra.E_UCase
                                                                    e)
                                                         with
                                                         | FStar_Pervasives_Native.Some
                                                             r ->
                                                             FStar_Pervasives_Native.Some
                                                               r
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             (match try1
                                                                    "LCASE"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_LCase
                                                                    e)
                                                              with
                                                              | FStar_Pervasives_Native.Some
                                                                  r ->
                                                                  FStar_Pervasives_Native.Some
                                                                    r
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  (match 
                                                                    try1
                                                                    "ENCODE_FOR_URI"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_EncodeForUri
                                                                    e)
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "ABS"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Abs
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "ROUND"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Round
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "CEIL"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Ceil
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "FLOOR"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Floor
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "MD5"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_MD5
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "SHA1"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_SHA1
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "SHA256"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_SHA256
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "SHA384"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_SHA384
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "SHA512"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_SHA512
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "YEAR"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Year
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "MONTH"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Month
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "DAY"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Day
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "HOURS"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Hours
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "MINUTES"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Minutes
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "SECONDS"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Seconds
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1
                                                                    "TIMEZONE"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Timezone
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try1 "TZ"
                                                                    (fun e ->
                                                                    SPARQL11_Algebra.E_Tz
                                                                    e)
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let try2
                                                                    kw mk =
                                                                    match 
                                                                    ps_consume
                                                                    ps kw
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    let ps'1
                                                                    =
                                                                    skip_ws
                                                                    ps' in
                                                                    (match 
                                                                    ps_expect
                                                                    ps'1 "("
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'2 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'2
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e1,
                                                                    ps'3) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'3 ","
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'4 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'4
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e2,
                                                                    ps'5) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'5 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((mk e1
                                                                    e2),
                                                                    ps'6)))))) in
                                                                    (match 
                                                                    try2
                                                                    "LANGMATCHES"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_FunctionCall
                                                                    ("sparql:langMatches",
                                                                    [a; b]))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "STRSTARTS"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_StrStarts
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "STRENDS"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_StrEnds
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "CONTAINS"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_Contains
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "STRBEFORE"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_StrBefore
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "STRAFTER"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_StrAfter
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "STRDT"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_StrDt
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "STRLANG"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_StrLang
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try2
                                                                    "SAMETERM"
                                                                    (fun a b
                                                                    ->
                                                                    SPARQL11_Algebra.E_SameTerm
                                                                    (a, b))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_consume
                                                                    ps
                                                                    "REPLACE"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    let ps'1
                                                                    =
                                                                    skip_ws
                                                                    ps' in
                                                                    (match 
                                                                    ps_expect
                                                                    ps'1 "("
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'2 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'2
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e1,
                                                                    ps'3) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'3 ","
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'4 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'4
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e2,
                                                                    ps'5) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'5 ","
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'6 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'6
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e3,
                                                                    ps'7) ->
                                                                    let ps''
                                                                    =
                                                                    skip_ws
                                                                    ps'7 in
                                                                    (match 
                                                                    ps_consume
                                                                    ps'' ","
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps''1 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps''1
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e4,
                                                                    ps''2) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps''2 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps''3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Replace
                                                                    (e1, e2,
                                                                    e3,
                                                                    (FStar_Pervasives_Native.Some
                                                                    e4))),
                                                                    ps''3)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'7 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'8 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Replace
                                                                    (e1, e2,
                                                                    e3,
                                                                    FStar_Pervasives_Native.None)),
                                                                    ps'8)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_consume
                                                                    ps "NOW"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    let ps'1
                                                                    =
                                                                    skip_ws
                                                                    ps' in
                                                                    (match 
                                                                    ps_expect
                                                                    ps'1 "("
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'2 ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'2 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (SPARQL11_Algebra.E_Now,
                                                                    ps'3)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_consume
                                                                    ps
                                                                    "BNODE"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    let ps'1
                                                                    =
                                                                    skip_ws
                                                                    ps' in
                                                                    (match 
                                                                    ps_expect
                                                                    ps'1 "("
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'2 ->
                                                                    let ps'3
                                                                    =
                                                                    skip_ws
                                                                    ps'2 in
                                                                    (match 
                                                                    ps_peek
                                                                    ps'3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c when
                                                                    (FStar_Char.int_of_char
                                                                    c) =
                                                                    (Prims.of_int (0x29))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_FunctionCall
                                                                    ("sparql:bnode",
                                                                    [])),
                                                                    (ps_advance
                                                                    ps'3
                                                                    Prims.int_one))
                                                                    | 
                                                                    uu___ ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'3
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e, ps'4)
                                                                    ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'4 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_FunctionCall
                                                                    ("sparql:bnode",
                                                                    [e])),
                                                                    ps'5)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_consume
                                                                    ps
                                                                    "SUBSTR"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    let ps'1
                                                                    =
                                                                    skip_ws
                                                                    ps' in
                                                                    (match 
                                                                    ps_expect
                                                                    ps'1 "("
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'2 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'2
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e1,
                                                                    ps'3) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'3 ","
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'4 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'4
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e2,
                                                                    ps'5) ->
                                                                    let ps''
                                                                    =
                                                                    skip_ws
                                                                    ps'5 in
                                                                    (match 
                                                                    ps_consume
                                                                    ps'' ","
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps''1 ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps''1
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e3,
                                                                    ps''2) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps''2 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps''3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Substr
                                                                    (e1, e2,
                                                                    (FStar_Pervasives_Native.Some
                                                                    e3))),
                                                                    ps''3)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'5 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Substr
                                                                    (e1, e2,
                                                                    FStar_Pervasives_Native.None)),
                                                                    ps'6)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_consume
                                                                    ps
                                                                    "COALESCE"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    (match 
                                                                    parse_expr_list
                                                                    ps'
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (args,
                                                                    ps'1) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Coalesce
                                                                    args),
                                                                    ps'1)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_consume
                                                                    ps
                                                                    "CONCAT"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    (match 
                                                                    parse_expr_list
                                                                    ps'
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (args,
                                                                    ps'1) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Concat
                                                                    args),
                                                                    ps'1)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let try_agg
                                                                    kw mk =
                                                                    match 
                                                                    ps_consume
                                                                    ps kw
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    let ps'1
                                                                    =
                                                                    skip_ws
                                                                    ps' in
                                                                    (match 
                                                                    ps_expect
                                                                    ps'1 "("
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'2 ->
                                                                    let ps'3
                                                                    =
                                                                    skip_ws
                                                                    ps'2 in
                                                                    let uu___
                                                                    =
                                                                    match 
                                                                    ps_consume
                                                                    ps'3
                                                                    "DISTINCT"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'4 ->
                                                                    (true,
                                                                    ps'4)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (false,
                                                                    ps'3) in
                                                                    (match uu___
                                                                    with
                                                                    | 
                                                                    (is_distinct,
                                                                    ps'4) ->
                                                                    let ps'5
                                                                    =
                                                                    skip_ws
                                                                    ps'4 in
                                                                    (match 
                                                                    ps_consume
                                                                    ps'5 "*"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'6 ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'6 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Aggregate
                                                                    (mk,
                                                                    is_distinct,
                                                                    (SPARQL11_Algebra.E_BoolLit
                                                                    true))),
                                                                    ps'7)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'5
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e, ps'6)
                                                                    ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'6 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Aggregate
                                                                    (mk,
                                                                    is_distinct,
                                                                    e)),
                                                                    ps'7)))))) in
                                                                    (match 
                                                                    try_agg
                                                                    "COUNT"
                                                                    SPARQL11_Algebra.Agg_Count
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try_agg
                                                                    "SUM"
                                                                    SPARQL11_Algebra.Agg_Sum
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try_agg
                                                                    "AVG"
                                                                    SPARQL11_Algebra.Agg_Avg
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try_agg
                                                                    "MIN"
                                                                    SPARQL11_Algebra.Agg_Min
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try_agg
                                                                    "MAX"
                                                                    SPARQL11_Algebra.Agg_Max
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    try_agg
                                                                    "SAMPLE"
                                                                    SPARQL11_Algebra.Agg_Sample
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_consume
                                                                    ps
                                                                    "GROUP_CONCAT"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps' ->
                                                                    let ps'1
                                                                    =
                                                                    skip_ws
                                                                    ps' in
                                                                    (match 
                                                                    ps_expect
                                                                    ps'1 "("
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'2 ->
                                                                    let ps'3
                                                                    =
                                                                    skip_ws
                                                                    ps'2 in
                                                                    let uu___
                                                                    =
                                                                    match 
                                                                    ps_consume
                                                                    ps'3
                                                                    "DISTINCT"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'4 ->
                                                                    (true,
                                                                    ps'4)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (false,
                                                                    ps'3) in
                                                                    (match uu___
                                                                    with
                                                                    | 
                                                                    (is_distinct,
                                                                    ps'4) ->
                                                                    (match 
                                                                    parse_expr
                                                                    ps'4
                                                                    prefixes
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (e, ps'5)
                                                                    ->
                                                                    let ps'6
                                                                    =
                                                                    skip_ws
                                                                    ps'5 in
                                                                    (match 
                                                                    ps_consume
                                                                    ps'6 ";"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'7 ->
                                                                    let ps'8
                                                                    =
                                                                    skip_ws
                                                                    ps'7 in
                                                                    (match 
                                                                    ps_consume
                                                                    ps'8
                                                                    "SEPARATOR"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'9 ->
                                                                    let ps'10
                                                                    =
                                                                    skip_ws
                                                                    ps'9 in
                                                                    (match 
                                                                    ps_consume
                                                                    ps'10 "="
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'11 ->
                                                                    let ps'12
                                                                    =
                                                                    skip_ws
                                                                    ps'11 in
                                                                    (match 
                                                                    parse_string_literal
                                                                    ps'12
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (sep,
                                                                    ps'13) ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'13 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'14 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Aggregate
                                                                    ((SPARQL11_Algebra.Agg_GroupConcat
                                                                    (FStar_Pervasives_Native.Some
                                                                    sep)),
                                                                    is_distinct,
                                                                    e)),
                                                                    ps'14)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    ps_expect
                                                                    ps'6 ")"
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ps'7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((SPARQL11_Algebra.E_Aggregate
                                                                    ((SPARQL11_Algebra.Agg_GroupConcat
                                                                    FStar_Pervasives_Native.None),
                                                                    is_distinct,
                                                                    e)),
                                                                    ps'7)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))))))))))))))))))))))))))))))))))))))))))))))))))
and parse_expr_list (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr Prims.list * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_expect ps1 "(" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      (match ps_peek ps3 with
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x29)) ->
           FStar_Pervasives_Native.Some ([], (ps_advance ps3 Prims.int_one))
       | uu___ ->
           (match parse_expr ps3 prefixes with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (e, ps4) ->
                let rec loop acc ps5 =
                  let ps6 = skip_ws ps5 in
                  match ps_consume ps6 "," with
                  | FStar_Pervasives_Native.Some ps7 ->
                      (match parse_expr ps7 prefixes with
                       | FStar_Pervasives_Native.Some (e1, ps8) ->
                           loop (e1 :: acc) ps8
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None ->
                      (match ps_expect ps6 ")" with
                       | FStar_Pervasives_Native.Some ps7 ->
                           FStar_Pervasives_Native.Some
                             ((FStar_List_Tot_Base.rev acc), ps7)
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None) in
                loop [e] ps4))
and parse_pattern_subject (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.pattern_subject * pstate) FStar_Pervasives_Native.option=
  match parse_variable ps with
  | FStar_Pervasives_Native.Some (v, ps1) ->
      FStar_Pervasives_Native.Some ((SPARQL11_Algebra.PS_Var v), ps1)
  | FStar_Pervasives_Native.None ->
      (match parse_iri ps prefixes with
       | FStar_Pervasives_Native.Some (iri, ps1) ->
           FStar_Pervasives_Native.Some ((SPARQL11_Algebra.PS_IRI iri), ps1)
       | FStar_Pervasives_Native.None ->
           let ps1 = skip_ws ps in
           (match ps_consume ps1 "_:" with
            | FStar_Pervasives_Native.Some ps2 ->
                let rec collect ps3 acc =
                  match ps_peek ps3 with
                  | FStar_Pervasives_Native.Some c when is_pn_chars c ->
                      collect (ps_advance ps3 Prims.int_one) (c :: acc)
                  | uu___ ->
                      ((FStar_String.string_of_list
                          (FStar_List_Tot_Base.rev acc)), ps3) in
                let uu___ = collect ps2 [] in
                (match uu___ with
                 | (label, ps3) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.PS_Var (Prims.strcat "?_:" label)),
                         ps3))
            | FStar_Pervasives_Native.None ->
                (match ps_consume ps1 "[" with
                 | FStar_Pervasives_Native.Some ps2 ->
                     let ps3 = skip_ws ps2 in
                     (match ps_consume ps3 "]" with
                      | FStar_Pervasives_Native.Some ps4 ->
                          FStar_Pervasives_Native.Some
                            ((SPARQL11_Algebra.PS_Var
                                (Prims.strcat "?_anon"
                                   (Prims.string_of_int ps4.pos))), ps4)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.None ->
                     let ps2 = skip_ws ps1 in
                     (match ps_consume ps2 "()" with
                      | FStar_Pervasives_Native.Some ps3 ->
                          let rdf_nil =
                            "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
                          FStar_Pervasives_Native.Some
                            ((SPARQL11_Algebra.PS_IRI rdf_nil), ps3)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None))))
and parse_pattern_term (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.pattern_term * pstate) FStar_Pervasives_Native.option=
  match parse_variable ps with
  | FStar_Pervasives_Native.Some (v, ps1) ->
      FStar_Pervasives_Native.Some ((SPARQL11_Algebra.PT_Var v), ps1)
  | FStar_Pervasives_Native.None ->
      (match parse_iri ps prefixes with
       | FStar_Pervasives_Native.Some (iri, ps1) ->
           FStar_Pervasives_Native.Some ((SPARQL11_Algebra.PT_IRI iri), ps1)
       | FStar_Pervasives_Native.None ->
           (match parse_rdf_literal ps prefixes with
            | FStar_Pervasives_Native.Some (lit, ps1) ->
                FStar_Pervasives_Native.Some
                  ((SPARQL11_Algebra.PT_Literal lit), ps1)
            | FStar_Pervasives_Native.None ->
                (match parse_boolean ps with
                 | FStar_Pervasives_Native.Some (b, ps1) ->
                     let lit =
                       {
                         RDF_Graph_Executable.lexical_form =
                           (if b then "true" else "false");
                         RDF_Graph_Executable.datatype =
                           RDF_Graph_Executable.xsd_boolean;
                         RDF_Graph_Executable.lang_tag =
                           FStar_Pervasives_Native.None
                       } in
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.PT_Literal lit), ps1)
                 | FStar_Pervasives_Native.None ->
                     let ps_start = ps in
                     let ps1 = skip_ws ps in
                     let start = ps1.pos in
                     let has_sign =
                       match ps_peek ps1 with
                       | FStar_Pervasives_Native.Some c ->
                           ((FStar_Char.int_of_char c) =
                              (Prims.of_int (0x2B)))
                             ||
                             ((FStar_Char.int_of_char c) =
                                (Prims.of_int (0x2D)))
                       | FStar_Pervasives_Native.None -> false in
                     let ps2 =
                       if has_sign then ps_advance ps1 Prims.int_one else ps1 in
                     let rec digits ps3 =
                       match ps_peek ps3 with
                       | FStar_Pervasives_Native.Some c when is_digit c ->
                           digits (ps_advance ps3 Prims.int_one)
                       | uu___ -> ps3 in
                     let ps_d = digits ps2 in
                     if
                       (ps_d.pos > ps2.pos) ||
                         ((match ps_peek ps2 with
                           | FStar_Pervasives_Native.Some c ->
                               (FStar_Char.int_of_char c) =
                                 (Prims.of_int (0x2E))
                           | FStar_Pervasives_Native.None -> false))
                     then
                       (match ps_peek ps_d with
                        | FStar_Pervasives_Native.Some c when
                            (FStar_Char.int_of_char c) =
                              (Prims.of_int (0x2E))
                            ->
                            let ps21 = digits (ps_advance ps_d Prims.int_one) in
                            let s =
                              FStar_String.sub ps_start.inp start
                                (ps21.pos - start) in
                            let lit =
                              {
                                RDF_Graph_Executable.lexical_form = s;
                                RDF_Graph_Executable.datatype =
                                  RDF_Graph_Executable.xsd_decimal;
                                RDF_Graph_Executable.lang_tag =
                                  FStar_Pervasives_Native.None
                              } in
                            FStar_Pervasives_Native.Some
                              ((SPARQL11_Algebra.PT_Literal lit), ps21)
                        | uu___ ->
                            let s =
                              FStar_String.sub ps_start.inp start
                                (ps_d.pos - start) in
                            let lit =
                              {
                                RDF_Graph_Executable.lexical_form = s;
                                RDF_Graph_Executable.datatype =
                                  RDF_Graph_Executable.xsd_integer;
                                RDF_Graph_Executable.lang_tag =
                                  FStar_Pervasives_Native.None
                              } in
                            FStar_Pervasives_Native.Some
                              ((SPARQL11_Algebra.PT_Literal lit), ps_d))
                     else
                       (match ps_consume ps_start "_:" with
                        | FStar_Pervasives_Native.Some ps3 ->
                            let uu___1 =
                              let rec collect ps4 acc =
                                match ps_peek ps4 with
                                | FStar_Pervasives_Native.Some c when
                                    is_pn_chars c ->
                                    collect (ps_advance ps4 Prims.int_one) (c
                                      :: acc)
                                | uu___2 ->
                                    ((FStar_String.string_of_list
                                        (FStar_List_Tot_Base.rev acc)), ps4) in
                              collect ps3 [] in
                            (match uu___1 with
                             | (label, ps4) ->
                                 FStar_Pervasives_Native.Some
                                   ((SPARQL11_Algebra.PT_Var
                                       (Prims.strcat "?_:" label)), ps4))
                        | FStar_Pervasives_Native.None ->
                            let ps0 = skip_ws ps_start in
                            (match ps_consume ps0 "()" with
                             | FStar_Pervasives_Native.Some ps01 ->
                                 let rdf_nil =
                                   "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
                                 FStar_Pervasives_Native.Some
                                   ((SPARQL11_Algebra.PT_IRI rdf_nil), ps01)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None)))))
and parse_property_path (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.property_path * pstate) FStar_Pervasives_Native.option=
  parse_path_alternative ps prefixes
and parse_path_alternative (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.property_path * pstate) FStar_Pervasives_Native.option=
  match parse_path_sequence ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (p, ps1) ->
      let rec loop acc ps2 =
        let ps3 = skip_ws ps2 in
        match ps_consume ps3 "|" with
        | FStar_Pervasives_Native.Some ps4 ->
            let ps5 = skip_ws ps4 in
            (match parse_path_sequence ps5 prefixes with
             | FStar_Pervasives_Native.Some (p2, ps6) ->
                 loop (SPARQL11_Algebra.PP_Alternative (acc, p2)) ps6
             | FStar_Pervasives_Native.None -> (acc, ps5))
        | FStar_Pervasives_Native.None -> (acc, ps3) in
      let uu___ = loop p ps1 in
      (match uu___ with
       | (result, ps2) -> FStar_Pervasives_Native.Some (result, ps2))
and parse_path_sequence (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.property_path * pstate) FStar_Pervasives_Native.option=
  match parse_path_elt_or_inverse ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (p, ps1) ->
      let rec loop acc ps2 =
        let ps3 = skip_ws ps2 in
        match ps_consume ps3 "/" with
        | FStar_Pervasives_Native.Some ps4 ->
            let ps5 = skip_ws ps4 in
            (match parse_path_elt_or_inverse ps5 prefixes with
             | FStar_Pervasives_Native.Some (p2, ps6) ->
                 loop (SPARQL11_Algebra.PP_Sequence (acc, p2)) ps6
             | FStar_Pervasives_Native.None -> (acc, ps5))
        | FStar_Pervasives_Native.None -> (acc, ps3) in
      let uu___ = loop p ps1 in
      (match uu___ with
       | (result, ps2) -> FStar_Pervasives_Native.Some (result, ps2))
and parse_path_elt_or_inverse (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.property_path * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "^" with
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      (match parse_path_elt ps3 prefixes with
       | FStar_Pervasives_Native.Some (p, ps4) ->
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.PP_Inverse p), ps4)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None -> parse_path_elt ps1 prefixes
and parse_path_elt (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.property_path * pstate) FStar_Pervasives_Native.option=
  match parse_path_primary ps prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (p, ps1) ->
      let ps_nows = ps1 in
      (match ps_peek ps1 with
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x2A)) ->
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.PP_ZeroOrMore p),
               (ps_advance ps1 Prims.int_one))
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x2B)) ->
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.PP_OneOrMore p),
               (ps_advance ps1 Prims.int_one))
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x3F)) ->
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.PP_ZeroOrOne p),
               (ps_advance ps1 Prims.int_one))
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x7B)) ->
           let ps2 = ps_advance ps1 Prims.int_one in
           let ps3 = skip_ws ps2 in
           (match parse_nat_digits_inline ps3 with
            | FStar_Pervasives_Native.Some (n, ps4) ->
                let ps5 = skip_ws ps4 in
                (match ps_consume ps5 "," with
                 | FStar_Pervasives_Native.Some ps6 ->
                     let ps7 = skip_ws ps6 in
                     (match parse_nat_digits_inline ps7 with
                      | FStar_Pervasives_Native.Some (m, ps8) ->
                          let ps9 = skip_ws ps8 in
                          (match ps_consume ps9 "}" with
                           | FStar_Pervasives_Native.Some ps10 ->
                               if
                                 (n = Prims.int_zero) && (m = Prims.int_zero)
                               then
                                 FStar_Pervasives_Native.Some
                                   (SPARQL11_Algebra.PP_ZeroLength, ps10)
                               else
                                 if
                                   (n = Prims.int_zero) &&
                                     (m = Prims.int_one)
                                 then
                                   FStar_Pervasives_Native.Some
                                     ((SPARQL11_Algebra.PP_ZeroOrOne p),
                                       ps10)
                                 else
                                   FStar_Pervasives_Native.Some
                                     ((SPARQL11_Algebra.PP_ZeroOrMore p),
                                       ps10)
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some (p, ps_nows))
                      | FStar_Pervasives_Native.None ->
                          (match ps_consume ps7 "}" with
                           | FStar_Pervasives_Native.Some ps8 ->
                               FStar_Pervasives_Native.Some
                                 ((SPARQL11_Algebra.PP_ZeroOrMore p), ps8)
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some (p, ps_nows)))
                 | FStar_Pervasives_Native.None ->
                     (match ps_consume ps5 "}" with
                      | FStar_Pervasives_Native.Some ps6 ->
                          if n = Prims.int_zero
                          then
                            FStar_Pervasives_Native.Some
                              (SPARQL11_Algebra.PP_ZeroLength, ps6)
                          else FStar_Pervasives_Native.Some (p, ps6)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some (p, ps_nows)))
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (p, ps_nows))
       | uu___ -> FStar_Pervasives_Native.Some (p, ps_nows))
and parse_path_primary (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.property_path * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
      let ps2 = ps_advance ps1 Prims.int_one in
      (match parse_property_path ps2 prefixes with
       | FStar_Pervasives_Native.Some (p, ps3) ->
           let ps4 = skip_ws ps3 in
           (match ps_consume ps4 ")" with
            | FStar_Pervasives_Native.Some ps5 ->
                FStar_Pervasives_Native.Some (p, ps5)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x21)) ->
      let ps2 = ps_advance ps1 Prims.int_one in
      let ps3 = skip_ws ps2 in
      (match ps_consume ps3 "(" with
       | FStar_Pervasives_Native.Some ps4 ->
           let rec parse_neg_set acc ps5 =
             let ps6 = skip_ws ps5 in
             match ps_consume ps6 ")" with
             | FStar_Pervasives_Native.Some ps7 ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List_Tot_Base.rev acc), ps7)
             | FStar_Pervasives_Native.None ->
                 let ps7 =
                   if Prims.op_Negation (Prims.uu___is_Nil acc)
                   then
                     match ps_consume ps6 "|" with
                     | FStar_Pervasives_Native.Some ps8 -> ps8
                     | FStar_Pervasives_Native.None -> ps6
                   else ps6 in
                 let ps8 = skip_ws ps7 in
                 (match ps_consume ps8 "^" with
                  | FStar_Pervasives_Native.Some ps9 ->
                      (match parse_iri ps9 prefixes with
                       | FStar_Pervasives_Native.Some (iri, ps10) ->
                           parse_neg_set
                             ((SPARQL11_Algebra.PP_Inverse
                                 (SPARQL11_Algebra.PP_IRI iri)) :: acc) ps10
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None ->
                      (match parse_iri ps8 prefixes with
                       | FStar_Pervasives_Native.Some (iri, ps9) ->
                           parse_neg_set ((SPARQL11_Algebra.PP_IRI iri) ::
                             acc) ps9
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None)) in
           (match parse_neg_set [] ps4 with
            | FStar_Pervasives_Native.Some (paths, ps5) ->
                FStar_Pervasives_Native.Some
                  ((SPARQL11_Algebra.PP_NegatedSet paths), ps5)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None ->
           (match ps_consume ps3 "^" with
            | FStar_Pervasives_Native.Some ps4 ->
                (match parse_iri ps4 prefixes with
                 | FStar_Pervasives_Native.Some (iri, ps5) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.PP_NegatedSet
                           [SPARQL11_Algebra.PP_Inverse
                              (SPARQL11_Algebra.PP_IRI iri)]), ps5)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None ->
                (match parse_iri ps3 prefixes with
                 | FStar_Pervasives_Native.Some (iri, ps4) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.PP_NegatedSet
                           [SPARQL11_Algebra.PP_IRI iri]), ps4)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)))
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x61)) ->
      (match ps_char_at ps1 Prims.int_one with
       | FStar_Pervasives_Native.Some c2 when is_pn_chars c2 ->
           (match parse_iri ps1 prefixes with
            | FStar_Pervasives_Native.Some (iri, ps2) ->
                FStar_Pervasives_Native.Some
                  ((SPARQL11_Algebra.PP_IRI iri), ps2)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | uu___ ->
           let rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in
           FStar_Pervasives_Native.Some
             ((SPARQL11_Algebra.PP_IRI rdf_type),
               (ps_advance ps1 Prims.int_one)))
  | uu___ ->
      (match parse_iri ps1 prefixes with
       | FStar_Pervasives_Native.Some (iri, ps2) ->
           FStar_Pervasives_Native.Some ((SPARQL11_Algebra.PP_IRI iri), ps2)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
and parse_path_object_list (subj : SPARQL11_Algebra.pattern_subject)
  (path : SPARQL11_Algebra.property_path) (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match parse_pattern_term ps1 prefixes with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (obj, ps2) ->
      let pp = SPARQL11_Algebra.GP_PropertyPath (subj, path, obj) in
      let ps' = skip_ws ps2 in
      (match ps_consume ps' "," with
       | FStar_Pervasives_Native.Some ps'1 ->
           (match parse_path_object_list subj path ps'1 prefixes with
            | FStar_Pervasives_Native.Some (more, ps'2) ->
                FStar_Pervasives_Native.Some ((ggp_join pp more), ps'2)
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (pp, ps2))
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (pp, ps2))
and parse_pred_object_with_path (subj : SPARQL11_Algebra.pattern_subject)
  (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match parse_property_path ps1 prefixes with
  | FStar_Pervasives_Native.Some (path, ps2) ->
      (match path with
       | SPARQL11_Algebra.PP_IRI iri ->
           (match parse_object_list subj (SPARQL11_Algebra.PT_IRI iri) ps2
                    prefixes
            with
            | FStar_Pervasives_Native.Some (tps, ps3) ->
                if Prims.uu___is_Nil tps
                then
                  FStar_Pervasives_Native.Some
                    (SPARQL11_Algebra.GP_Empty, ps3)
                else
                  FStar_Pervasives_Native.Some
                    ((SPARQL11_Algebra.GP_BGP tps), ps3)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | uu___ -> parse_path_object_list subj path ps2 prefixes)
  | FStar_Pervasives_Native.None ->
      let ps_bk = ps1 in
      (match ps_peek ps1 with
       | FStar_Pervasives_Native.Some c when
           (FStar_Char.int_of_char c) = (Prims.of_int (0x61)) ->
           (match ps_char_at ps1 Prims.int_one with
            | FStar_Pervasives_Native.Some c2 when is_pn_chars c2 ->
                (match parse_pattern_term ps1 prefixes with
                 | FStar_Pervasives_Native.Some (pred, ps2) ->
                     (match parse_object_list subj pred ps2 prefixes with
                      | FStar_Pervasives_Native.Some (tps, ps3) ->
                          FStar_Pervasives_Native.Some
                            ((SPARQL11_Algebra.GP_BGP tps), ps3)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some
                       (SPARQL11_Algebra.GP_Empty, ps_bk))
            | uu___ ->
                let rdf_type =
                  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in
                let ps2 = ps_advance ps1 Prims.int_one in
                (match parse_object_list subj
                         (SPARQL11_Algebra.PT_IRI rdf_type) ps2 prefixes
                 with
                 | FStar_Pervasives_Native.Some (tps, ps3) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.GP_BGP tps), ps3)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None))
       | uu___ ->
           (match parse_pattern_term ps1 prefixes with
            | FStar_Pervasives_Native.Some (pred, ps2) ->
                (match parse_object_list subj pred ps2 prefixes with
                 | FStar_Pervasives_Native.Some (tps, ps3) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.GP_BGP tps), ps3)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some
                  (SPARQL11_Algebra.GP_Empty, ps_bk)))
and parse_predicate_object_list_pp (subj : SPARQL11_Algebra.pattern_subject)
  (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  match parse_pred_object_with_path subj ps prefixes with
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.GP_Empty, ps)
  | FStar_Pervasives_Native.Some (result, ps1) ->
      if result = SPARQL11_Algebra.GP_Empty
      then FStar_Pervasives_Native.Some (SPARQL11_Algebra.GP_Empty, ps1)
      else
        (let ps' = skip_ws ps1 in
         match ps_consume ps' ";" with
         | FStar_Pervasives_Native.Some ps'1 ->
             let ps'2 = skip_ws ps'1 in
             (match ps_peek ps'2 with
              | FStar_Pervasives_Native.Some c when
                  ((FStar_Char.int_of_char c) = (Prims.of_int (0x7D))) ||
                    ((FStar_Char.int_of_char c) = (Prims.of_int (0x2E)))
                  -> FStar_Pervasives_Native.Some (result, ps'2)
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some (result, ps'2)
              | uu___1 ->
                  (match parse_predicate_object_list_pp subj ps'2 prefixes
                   with
                   | FStar_Pervasives_Native.Some (more, ps'3) ->
                       if more = SPARQL11_Algebra.GP_Empty
                       then FStar_Pervasives_Native.Some (result, ps'3)
                       else
                         FStar_Pervasives_Native.Some
                           ((ggp_join result more), ps'3)
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.Some (result, ps'2)))
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some (result, ps1))
and parse_triples_block_pp (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x5B)) ->
      let ps_bk = ps1 in
      let ps' = ps_advance ps1 Prims.int_one in
      let ps'1 = skip_ws ps' in
      (match ps_peek ps'1 with
       | FStar_Pervasives_Native.Some c1 when
           (FStar_Char.int_of_char c1) = (Prims.of_int (0x5D)) ->
           let ps'2 = ps_advance ps'1 Prims.int_one in
           let bnode_var =
             Prims.strcat "?_anon" (Prims.string_of_int ps_bk.pos) in
           parse_predicate_object_list_pp (SPARQL11_Algebra.PS_Var bnode_var)
             ps'2 prefixes
       | FStar_Pervasives_Native.Some uu___ ->
           let bnode_var =
             Prims.strcat "?_bpl" (Prims.string_of_int ps_bk.pos) in
           let bnode_subj = SPARQL11_Algebra.PS_Var bnode_var in
           (match parse_predicate_object_list_pp bnode_subj ps'1 prefixes
            with
            | FStar_Pervasives_Native.Some (bnode_pat, ps'2) ->
                let ps'3 = skip_ws ps'2 in
                (match ps_consume ps'3 "]" with
                 | FStar_Pervasives_Native.Some ps'4 ->
                     let ps'5 = skip_ws ps'4 in
                     (match parse_predicate_object_list_pp bnode_subj ps'5
                              prefixes
                      with
                      | FStar_Pervasives_Native.Some (more, ps'6) ->
                          if more = SPARQL11_Algebra.GP_Empty
                          then FStar_Pervasives_Native.Some (bnode_pat, ps'6)
                          else
                            FStar_Pervasives_Native.Some
                              ((ggp_join bnode_pat more), ps'6)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some (bnode_pat, ps'5))
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ ->
      (match parse_pattern_subject ps1 prefixes with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (SPARQL11_Algebra.GP_Empty, ps1)
       | FStar_Pervasives_Native.Some (subj, ps2) ->
           parse_predicate_object_list_pp subj ps2 prefixes)
and parse_triples_block (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.triple_pattern Prims.list * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x5B)) ->
      let ps_bk = ps1 in
      let ps' = ps_advance ps1 Prims.int_one in
      let ps'1 = skip_ws ps' in
      (match ps_peek ps'1 with
       | FStar_Pervasives_Native.Some c1 when
           (FStar_Char.int_of_char c1) = (Prims.of_int (0x5D)) ->
           let ps'2 = ps_advance ps'1 Prims.int_one in
           let bnode_var =
             Prims.strcat "?_anon" (Prims.string_of_int ps_bk.pos) in
           parse_predicate_object_list (SPARQL11_Algebra.PS_Var bnode_var)
             ps'2 prefixes
       | FStar_Pervasives_Native.Some uu___ ->
           let bnode_var =
             Prims.strcat "?_bpl" (Prims.string_of_int ps_bk.pos) in
           let bnode_subj = SPARQL11_Algebra.PS_Var bnode_var in
           (match parse_predicate_object_list bnode_subj ps'1 prefixes with
            | FStar_Pervasives_Native.Some (bnode_triples, ps'2) ->
                let ps'3 = skip_ws ps'2 in
                (match ps_consume ps'3 "]" with
                 | FStar_Pervasives_Native.Some ps'4 ->
                     let ps'5 = skip_ws ps'4 in
                     (match parse_predicate_object_list bnode_subj ps'5
                              prefixes
                      with
                      | FStar_Pervasives_Native.Some (more, ps'6) ->
                          FStar_Pervasives_Native.Some
                            ((FStar_List_Tot_Base.op_At bnode_triples more),
                              ps'6)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some (bnode_triples, ps'5))
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ ->
      (match parse_pattern_subject ps1 prefixes with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some ([], ps1)
       | FStar_Pervasives_Native.Some (subj, ps2) ->
           parse_predicate_object_list subj ps2 prefixes)
and parse_predicate_object_list (subj : SPARQL11_Algebra.pattern_subject)
  (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.triple_pattern Prims.list * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let parse_pred ps2 =
    let ps3 = skip_ws ps2 in
    match ps_peek ps3 with
    | FStar_Pervasives_Native.Some c when
        (FStar_Char.int_of_char c) = (Prims.of_int (0x61)) ->
        (match ps_char_at ps3 Prims.int_one with
         | FStar_Pervasives_Native.Some c2 when is_pn_chars c2 ->
             parse_pattern_term ps3 prefixes
         | uu___ ->
             let rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in
             FStar_Pervasives_Native.Some
               ((SPARQL11_Algebra.PT_IRI rdf_type),
                 (ps_advance ps3 Prims.int_one)))
    | uu___ -> parse_pattern_term ps3 prefixes in
  match parse_pred ps1 with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ([], ps1)
  | FStar_Pervasives_Native.Some (pred, ps2) ->
      (match parse_object_list subj pred ps2 prefixes with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (triples, ps3) ->
           let ps' = skip_ws ps3 in
           (match ps_consume ps' ";" with
            | FStar_Pervasives_Native.Some ps'1 ->
                let ps'2 = skip_ws ps'1 in
                (match ps_peek ps'2 with
                 | FStar_Pervasives_Native.Some c when
                     ((FStar_Char.int_of_char c) = (Prims.of_int (0x7D))) ||
                       ((FStar_Char.int_of_char c) = (Prims.of_int (0x2E)))
                     -> FStar_Pervasives_Native.Some (triples, ps'2)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some (triples, ps'2)
                 | uu___ ->
                     (match parse_predicate_object_list subj ps'2 prefixes
                      with
                      | FStar_Pervasives_Native.Some (more, ps'3) ->
                          FStar_Pervasives_Native.Some
                            ((FStar_List_Tot_Base.op_At triples more), ps'3)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some (triples, ps'2)))
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (triples, ps3)))
and parse_object_list (subj : SPARQL11_Algebra.pattern_subject)
  (pred : SPARQL11_Algebra.pattern_term) (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.triple_pattern Prims.list * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x5B)) ->
      let ps_bk = ps1 in
      let ps2 = ps_advance ps1 Prims.int_one in
      let ps3 = skip_ws ps2 in
      (match ps_peek ps3 with
       | FStar_Pervasives_Native.Some c1 when
           (FStar_Char.int_of_char c1) = (Prims.of_int (0x5D)) ->
           let bnode_var =
             Prims.strcat "?_anon" (Prims.string_of_int ps_bk.pos) in
           let obj = SPARQL11_Algebra.PT_Var bnode_var in
           let tp =
             {
               SPARQL11_Algebra.tp_s = subj;
               SPARQL11_Algebra.tp_p = pred;
               SPARQL11_Algebra.tp_o = obj
             } in
           let ps4 = ps_advance ps3 Prims.int_one in
           let ps' = skip_ws ps4 in
           (match ps_consume ps' "," with
            | FStar_Pervasives_Native.Some ps'1 ->
                (match parse_object_list subj pred ps'1 prefixes with
                 | FStar_Pervasives_Native.Some (more, ps'2) ->
                     FStar_Pervasives_Native.Some ((tp :: more), ps'2)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some ([tp], ps4))
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some ([tp], ps4))
       | uu___ ->
           let bnode_var =
             Prims.strcat "?_bpl" (Prims.string_of_int ps_bk.pos) in
           let bnode_subj = SPARQL11_Algebra.PS_Var bnode_var in
           (match parse_predicate_object_list bnode_subj ps3 prefixes with
            | FStar_Pervasives_Native.Some (bnode_triples, ps4) ->
                let ps5 = skip_ws ps4 in
                (match ps_consume ps5 "]" with
                 | FStar_Pervasives_Native.Some ps6 ->
                     let obj = SPARQL11_Algebra.PT_Var bnode_var in
                     let tp =
                       {
                         SPARQL11_Algebra.tp_s = subj;
                         SPARQL11_Algebra.tp_p = pred;
                         SPARQL11_Algebra.tp_o = obj
                       } in
                     let ps' = skip_ws ps6 in
                     (match ps_consume ps' "," with
                      | FStar_Pervasives_Native.Some ps'1 ->
                          (match parse_object_list subj pred ps'1 prefixes
                           with
                           | FStar_Pervasives_Native.Some (more, ps'2) ->
                               FStar_Pervasives_Native.Some
                                 ((FStar_List_Tot_Base.op_At (tp ::
                                     bnode_triples) more), ps'2)
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some
                                 ((tp :: bnode_triples), ps6))
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some
                            ((tp :: bnode_triples), ps6))
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
      let ps_bk = ps1 in
      let ps2 = ps_advance ps1 Prims.int_one in
      let ps3 = skip_ws ps2 in
      (match ps_peek ps3 with
       | FStar_Pervasives_Native.Some c1 when
           (FStar_Char.int_of_char c1) = (Prims.of_int (0x29)) ->
           let obj =
             SPARQL11_Algebra.PT_IRI
               "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
           let tp =
             {
               SPARQL11_Algebra.tp_s = subj;
               SPARQL11_Algebra.tp_p = pred;
               SPARQL11_Algebra.tp_o = obj
             } in
           let ps4 = ps_advance ps3 Prims.int_one in
           let ps' = skip_ws ps4 in
           (match ps_consume ps' "," with
            | FStar_Pervasives_Native.Some ps'1 ->
                (match parse_object_list subj pred ps'1 prefixes with
                 | FStar_Pervasives_Native.Some (more, ps'2) ->
                     FStar_Pervasives_Native.Some ((tp :: more), ps'2)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some ([tp], ps4))
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some ([tp], ps4))
       | uu___ ->
           let rdf_first = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first" in
           let rdf_rest = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest" in
           let rdf_nil = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
           let rec parse_list_items ps4 counter =
             let ps5 = skip_ws ps4 in
             match ps_peek ps5 with
             | FStar_Pervasives_Native.Some c1 when
                 (FStar_Char.int_of_char c1) = (Prims.of_int (0x29)) ->
                 FStar_Pervasives_Native.Some
                   ((SPARQL11_Algebra.PT_IRI rdf_nil), [],
                     (ps_advance ps5 Prims.int_one))
             | uu___1 ->
                 (match parse_pattern_term ps5 prefixes with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (item, ps6) ->
                      let node_var =
                        Prims.strcat "?_list"
                          (Prims.strcat (Prims.string_of_int ps_bk.pos)
                             (Prims.strcat "_" (Prims.string_of_int counter))) in
                      (match parse_list_items ps6 (counter + Prims.int_one)
                       with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some
                           (rest_term, rest_triples, ps7) ->
                           let first_tp =
                             {
                               SPARQL11_Algebra.tp_s =
                                 (SPARQL11_Algebra.PS_Var node_var);
                               SPARQL11_Algebra.tp_p =
                                 (SPARQL11_Algebra.PT_IRI rdf_first);
                               SPARQL11_Algebra.tp_o = item
                             } in
                           let rest_tp =
                             {
                               SPARQL11_Algebra.tp_s =
                                 (SPARQL11_Algebra.PS_Var node_var);
                               SPARQL11_Algebra.tp_p =
                                 (SPARQL11_Algebra.PT_IRI rdf_rest);
                               SPARQL11_Algebra.tp_o = rest_term
                             } in
                           FStar_Pervasives_Native.Some
                             ((SPARQL11_Algebra.PT_Var node_var), (first_tp
                               :: rest_tp :: rest_triples), ps7))) in
           (match parse_list_items ps3 Prims.int_zero with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (list_head, list_triples, ps4) ->
                let tp =
                  {
                    SPARQL11_Algebra.tp_s = subj;
                    SPARQL11_Algebra.tp_p = pred;
                    SPARQL11_Algebra.tp_o = list_head
                  } in
                let ps' = skip_ws ps4 in
                (match ps_consume ps' "," with
                 | FStar_Pervasives_Native.Some ps'1 ->
                     (match parse_object_list subj pred ps'1 prefixes with
                      | FStar_Pervasives_Native.Some (more, ps'2) ->
                          FStar_Pervasives_Native.Some
                            ((FStar_List_Tot_Base.op_At (tp :: list_triples)
                                more), ps'2)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some
                            ((tp :: list_triples), ps4))
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some ((tp :: list_triples), ps4))))
  | uu___ ->
      (match parse_pattern_term ps1 prefixes with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (obj, ps2) ->
           let tp =
             {
               SPARQL11_Algebra.tp_s = subj;
               SPARQL11_Algebra.tp_p = pred;
               SPARQL11_Algebra.tp_o = obj
             } in
           let ps' = skip_ws ps2 in
           (match ps_consume ps' "," with
            | FStar_Pervasives_Native.Some ps'1 ->
                (match parse_object_list subj pred ps'1 prefixes with
                 | FStar_Pervasives_Native.Some (more, ps'2) ->
                     FStar_Pervasives_Native.Some ((tp :: more), ps'2)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some ([tp], ps2))
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some ([tp], ps2)))
and parse_group_graph_pattern (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "{" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      (match parse_ggp_body ps2 prefixes with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (pattern, ps3) ->
           (match ps_expect ps3 "}" with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ps4 ->
                FStar_Pervasives_Native.Some (pattern, ps4)))
and parse_ggp_body (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x7D)) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.GP_Empty, ps1)
  | uu___ ->
      if ps_starts_with_ci ps1 "SELECT"
      then parse_sub_select_inline ps1 prefixes
      else parse_ggp_elements ps1 prefixes SPARQL11_Algebra.GP_Empty []
and parse_sub_select_inline (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  match ps_consume ps "SELECT" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps1 ->
      let ps2 = skip_ws ps1 in
      let uu___ =
        match ps_consume ps2 "DISTINCT" with
        | FStar_Pervasives_Native.Some ps3 -> (true, false, ps3)
        | FStar_Pervasives_Native.None ->
            (match ps_consume ps2 "REDUCED" with
             | FStar_Pervasives_Native.Some ps3 -> (false, true, ps3)
             | FStar_Pervasives_Native.None -> (false, false, ps2)) in
      (match uu___ with
       | (is_distinct, is_reduced, ps3) ->
           let ps4 = skip_ws ps3 in
           let parse_sel_items ps5 =
             match ps_consume ps5 "*" with
             | FStar_Pervasives_Native.Some ps6 ->
                 FStar_Pervasives_Native.Some
                   (SPARQL11_Algebra.Select_All, ps6)
             | FStar_Pervasives_Native.None ->
                 let rec parse_items acc ps6 =
                   let ps7 = skip_ws ps6 in
                   match ps_peek ps7 with
                   | FStar_Pervasives_Native.Some c when
                       (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
                       let ps' = ps_advance ps7 Prims.int_one in
                       (match parse_expr ps' prefixes with
                        | FStar_Pervasives_Native.Some (e, ps'1) ->
                            let ps'2 = skip_ws ps'1 in
                            (match ps_consume ps'2 "AS" with
                             | FStar_Pervasives_Native.Some ps'3 ->
                                 (match parse_variable ps'3 with
                                  | FStar_Pervasives_Native.Some (v, ps'4) ->
                                      (match ps_expect ps'4 ")" with
                                       | FStar_Pervasives_Native.Some ps'5 ->
                                           parse_items
                                             ((SPARQL11_Algebra.SI_Expr
                                                 (e, v)) :: acc) ps'5
                                       | FStar_Pervasives_Native.None ->
                                           if Prims.uu___is_Nil acc
                                           then FStar_Pervasives_Native.None
                                           else
                                             FStar_Pervasives_Native.Some
                                               ((FStar_List_Tot_Base.rev acc),
                                                 ps7))
                                  | FStar_Pervasives_Native.None ->
                                      if Prims.uu___is_Nil acc
                                      then FStar_Pervasives_Native.None
                                      else
                                        FStar_Pervasives_Native.Some
                                          ((FStar_List_Tot_Base.rev acc),
                                            ps7))
                             | FStar_Pervasives_Native.None ->
                                 if Prims.uu___is_Nil acc
                                 then FStar_Pervasives_Native.None
                                 else
                                   FStar_Pervasives_Native.Some
                                     ((FStar_List_Tot_Base.rev acc), ps7))
                        | FStar_Pervasives_Native.None ->
                            if Prims.uu___is_Nil acc
                            then FStar_Pervasives_Native.None
                            else
                              FStar_Pervasives_Native.Some
                                ((FStar_List_Tot_Base.rev acc), ps7))
                   | uu___1 ->
                       (match parse_variable ps7 with
                        | FStar_Pervasives_Native.Some (v, ps8) ->
                            parse_items ((SPARQL11_Algebra.SI_Var v) :: acc)
                              ps8
                        | FStar_Pervasives_Native.None ->
                            if Prims.uu___is_Nil acc
                            then FStar_Pervasives_Native.None
                            else
                              FStar_Pervasives_Native.Some
                                ((FStar_List_Tot_Base.rev acc), ps7)) in
                 (match parse_items [] ps5 with
                  | FStar_Pervasives_Native.Some (items, ps6) ->
                      FStar_Pervasives_Native.Some
                        ((SPARQL11_Algebra.Select_Vars items), ps6)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None) in
           (match parse_sel_items ps4 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (sel, ps5) ->
                let ps6 = skip_ws ps5 in
                let ps7 =
                  match ps_consume ps6 "WHERE" with
                  | FStar_Pervasives_Native.Some ps8 -> ps8
                  | FStar_Pervasives_Native.None -> ps6 in
                (match parse_group_graph_pattern ps7 prefixes with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (pattern, ps8) ->
                     let ps9 = skip_ws ps8 in
                     let uu___1 =
                       if ps_starts_with_ci ps9 "GROUP"
                       then
                         let ps_bk = ps9 in
                         match ps_consume ps9 "GROUP" with
                         | FStar_Pervasives_Native.Some ps10 ->
                             let ps11 = skip_ws ps10 in
                             (match ps_consume ps11 "BY" with
                              | FStar_Pervasives_Native.Some ps12 ->
                                  let rec parse_gc acc ps13 =
                                    let ps14 = skip_ws ps13 in
                                    match parse_variable ps14 with
                                    | FStar_Pervasives_Native.Some (v, ps15)
                                        ->
                                        parse_gc ((SPARQL11_Algebra.GC_Var v)
                                          :: acc) ps15
                                    | FStar_Pervasives_Native.None ->
                                        (match ps_peek ps14 with
                                         | FStar_Pervasives_Native.Some c
                                             when
                                             (FStar_Char.int_of_char c) =
                                               (Prims.of_int (0x28))
                                             ->
                                             let ps' =
                                               ps_advance ps14 Prims.int_one in
                                             (match parse_expr ps' prefixes
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  (e, ps'1) ->
                                                  let ps'2 = skip_ws ps'1 in
                                                  (match ps_consume ps'2 "AS"
                                                   with
                                                   | FStar_Pervasives_Native.Some
                                                       ps'3 ->
                                                       (match parse_variable
                                                                ps'3
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            (v, ps'4) ->
                                                            (match ps_expect
                                                                    ps'4 ")"
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 ps'5 ->
                                                                 parse_gc
                                                                   ((
                                                                   SPARQL11_Algebra.GC_Expr
                                                                    (e,
                                                                    (FStar_Pervasives_Native.Some
                                                                    v))) ::
                                                                   acc) ps'5
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 ((FStar_List_Tot_Base.rev
                                                                    acc),
                                                                   ps14))
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            ((FStar_List_Tot_Base.rev
                                                                acc), ps14))
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       (match ps_expect ps'2
                                                                ")"
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            ps'3 ->
                                                            parse_gc
                                                              ((SPARQL11_Algebra.GC_Expr
                                                                  (e,
                                                                    FStar_Pervasives_Native.None))
                                                              :: acc) ps'3
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            ((FStar_List_Tot_Base.rev
                                                                acc), ps14)))
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  ((FStar_List_Tot_Base.rev
                                                      acc), ps14))
                                         | uu___2 ->
                                             ((FStar_List_Tot_Base.rev acc),
                                               ps14)) in
                                  let uu___2 = parse_gc [] ps12 in
                                  (match uu___2 with
                                   | (gc, ps13) ->
                                       if Prims.uu___is_Nil gc
                                       then
                                         (FStar_Pervasives_Native.None,
                                           ps_bk)
                                       else
                                         ((FStar_Pervasives_Native.Some gc),
                                           ps13))
                              | FStar_Pervasives_Native.None ->
                                  (FStar_Pervasives_Native.None, ps_bk))
                         | FStar_Pervasives_Native.None ->
                             (FStar_Pervasives_Native.None, ps_bk)
                       else (FStar_Pervasives_Native.None, ps9) in
                     (match uu___1 with
                      | (gb, ps10) ->
                          let ps11 = skip_ws ps10 in
                          let uu___2 =
                            if ps_starts_with_ci ps11 "HAVING"
                            then
                              match ps_consume ps11 "HAVING" with
                              | FStar_Pervasives_Native.Some ps12 ->
                                  let rec parse_hc acc ps13 =
                                    let ps14 = skip_ws ps13 in
                                    match ps_peek ps14 with
                                    | FStar_Pervasives_Native.Some c when
                                        (FStar_Char.int_of_char c) =
                                          (Prims.of_int (0x28))
                                        ->
                                        let ps' =
                                          ps_advance ps14 Prims.int_one in
                                        (match parse_expr ps' prefixes with
                                         | FStar_Pervasives_Native.Some
                                             (e, ps'1) ->
                                             (match ps_expect ps'1 ")" with
                                              | FStar_Pervasives_Native.Some
                                                  ps'2 ->
                                                  parse_hc (e :: acc) ps'2
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  ((FStar_List_Tot_Base.rev
                                                      acc), ps14))
                                         | FStar_Pervasives_Native.None ->
                                             ((FStar_List_Tot_Base.rev acc),
                                               ps14))
                                    | uu___3 ->
                                        ((FStar_List_Tot_Base.rev acc), ps14) in
                                  let uu___3 = parse_hc [] ps12 in
                                  (match uu___3 with
                                   | (hc, ps13) ->
                                       if Prims.uu___is_Nil hc
                                       then
                                         (FStar_Pervasives_Native.None, ps13)
                                       else
                                         ((FStar_Pervasives_Native.Some hc),
                                           ps13))
                              | FStar_Pervasives_Native.None ->
                                  (FStar_Pervasives_Native.None, ps11)
                            else (FStar_Pervasives_Native.None, ps11) in
                          (match uu___2 with
                           | (hv, ps12) ->
                               let ps13 = skip_ws ps12 in
                               let uu___3 =
                                 if ps_starts_with_ci ps13 "ORDER"
                                 then
                                   match ps_consume ps13 "ORDER" with
                                   | FStar_Pervasives_Native.Some ps14 ->
                                       let ps15 = skip_ws ps14 in
                                       (match ps_consume ps15 "BY" with
                                        | FStar_Pervasives_Native.Some ps16
                                            ->
                                            let rec parse_oc acc ps17 =
                                              let ps18 = skip_ws ps17 in
                                              match ps_consume ps18 "ASC"
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  ps' ->
                                                  let ps'1 = skip_ws ps' in
                                                  (match ps_expect ps'1 "("
                                                   with
                                                   | FStar_Pervasives_Native.Some
                                                       ps'2 ->
                                                       (match parse_expr ps'2
                                                                prefixes
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            (e, ps'3) ->
                                                            (match ps_expect
                                                                    ps'3 ")"
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 ps'4 ->
                                                                 parse_oc
                                                                   ((
                                                                   SPARQL11_Algebra.OC_Asc
                                                                    e) ::
                                                                   acc) ps'4
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 ((FStar_List_Tot_Base.rev
                                                                    acc),
                                                                   ps18))
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            ((FStar_List_Tot_Base.rev
                                                                acc), ps18))
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       ((FStar_List_Tot_Base.rev
                                                           acc), ps18))
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  (match ps_consume ps18
                                                           "DESC"
                                                   with
                                                   | FStar_Pervasives_Native.Some
                                                       ps' ->
                                                       let ps'1 = skip_ws ps' in
                                                       (match ps_expect ps'1
                                                                "("
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            ps'2 ->
                                                            (match parse_expr
                                                                    ps'2
                                                                    prefixes
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 (e, ps'3) ->
                                                                 (match 
                                                                    ps_expect
                                                                    ps'3 ")"
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    ps'4 ->
                                                                    parse_oc
                                                                    ((SPARQL11_Algebra.OC_Desc
                                                                    e) ::
                                                                    acc) ps'4
                                                                  | FStar_Pervasives_Native.None
                                                                    ->
                                                                    ((FStar_List_Tot_Base.rev
                                                                    acc),
                                                                    ps18))
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 ((FStar_List_Tot_Base.rev
                                                                    acc),
                                                                   ps18))
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            ((FStar_List_Tot_Base.rev
                                                                acc), ps18))
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       (match parse_expr ps18
                                                                prefixes
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            (e, ps19) ->
                                                            parse_oc
                                                              ((SPARQL11_Algebra.OC_Asc
                                                                  e) :: acc)
                                                              ps19
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            ((FStar_List_Tot_Base.rev
                                                                acc), ps18))) in
                                            let uu___4 = parse_oc [] ps16 in
                                            (match uu___4 with
                                             | (oc, ps17) ->
                                                 if Prims.uu___is_Nil oc
                                                 then
                                                   (FStar_Pervasives_Native.None,
                                                     ps17)
                                                 else
                                                   ((FStar_Pervasives_Native.Some
                                                       oc), ps17))
                                        | FStar_Pervasives_Native.None ->
                                            (FStar_Pervasives_Native.None,
                                              ps15))
                                   | FStar_Pervasives_Native.None ->
                                       (FStar_Pervasives_Native.None, ps13)
                                 else (FStar_Pervasives_Native.None, ps13) in
                               (match uu___3 with
                                | (ob, ps14) ->
                                    let ps15 = skip_ws ps14 in
                                    let uu___4 =
                                      if ps_starts_with_ci ps15 "LIMIT"
                                      then
                                        match ps_consume ps15 "LIMIT" with
                                        | FStar_Pervasives_Native.Some ps16
                                            ->
                                            let ps17 = skip_ws ps16 in
                                            (match parse_nat_digits_inline
                                                     ps17
                                             with
                                             | FStar_Pervasives_Native.Some
                                                 (n, ps18) ->
                                                 ((FStar_Pervasives_Native.Some
                                                     n), ps18)
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 (FStar_Pervasives_Native.None,
                                                   ps17))
                                        | FStar_Pervasives_Native.None ->
                                            (FStar_Pervasives_Native.None,
                                              ps15)
                                      else
                                        (FStar_Pervasives_Native.None, ps15) in
                                    (match uu___4 with
                                     | (l, ps16) ->
                                         let ps17 = skip_ws ps16 in
                                         let uu___5 =
                                           if ps_starts_with_ci ps17 "OFFSET"
                                           then
                                             match ps_consume ps17 "OFFSET"
                                             with
                                             | FStar_Pervasives_Native.Some
                                                 ps18 ->
                                                 let ps19 = skip_ws ps18 in
                                                 (match parse_nat_digits_inline
                                                          ps19
                                                  with
                                                  | FStar_Pervasives_Native.Some
                                                      (n, ps20) ->
                                                      ((FStar_Pervasives_Native.Some
                                                          n), ps20)
                                                  | FStar_Pervasives_Native.None
                                                      ->
                                                      (FStar_Pervasives_Native.None,
                                                        ps19))
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 (FStar_Pervasives_Native.None,
                                                   ps17)
                                           else
                                             (FStar_Pervasives_Native.None,
                                               ps17) in
                                         (match uu___5 with
                                          | (o, ps18) ->
                                              let sub_q =
                                                {
                                                  SPARQL11_Algebra.q_base =
                                                    FStar_Pervasives_Native.None;
                                                  SPARQL11_Algebra.q_prefixes
                                                    = prefixes;
                                                  SPARQL11_Algebra.q_form =
                                                    (SPARQL11_Algebra.QF_Select
                                                       sel);
                                                  SPARQL11_Algebra.q_dataset
                                                    = [];
                                                  SPARQL11_Algebra.q_pattern
                                                    = pattern;
                                                  SPARQL11_Algebra.q_group_by
                                                    = gb;
                                                  SPARQL11_Algebra.q_having =
                                                    hv;
                                                  SPARQL11_Algebra.q_modifier
                                                    =
                                                    {
                                                      SPARQL11_Algebra.sm_order_by
                                                        = ob;
                                                      SPARQL11_Algebra.sm_distinct
                                                        = is_distinct;
                                                      SPARQL11_Algebra.sm_reduced
                                                        = is_reduced;
                                                      SPARQL11_Algebra.sm_offset
                                                        = o;
                                                      SPARQL11_Algebra.sm_limit
                                                        = l
                                                    }
                                                } in
                                              FStar_Pervasives_Native.Some
                                                ((SPARQL11_Algebra.GP_SubSelect
                                                    sub_q), ps18)))))))))
and parse_ggp_elements (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list)
  (acc : SPARQL11_Algebra.group_graph_pattern)
  (filters : SPARQL11_Algebra.expr Prims.list) :
  (SPARQL11_Algebra.group_graph_pattern * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let apply_filters pat fs =
    FStar_List_Tot_Base.fold_left
      (fun p f -> SPARQL11_Algebra.GP_Filter (f, p)) pat fs in
  match ps_peek ps1 with
  | FStar_Pervasives_Native.None ->
      FStar_Pervasives_Native.Some ((apply_filters acc filters), ps1)
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x7D)) ->
      FStar_Pervasives_Native.Some ((apply_filters acc filters), ps1)
  | uu___ ->
      (match ps_consume ps1 "OPTIONAL" with
       | FStar_Pervasives_Native.Some ps_after ->
           (match parse_group_graph_pattern ps_after prefixes with
            | FStar_Pervasives_Native.Some (opt_pat, ps') ->
                let rec extract_filters p acc_f =
                  match p with
                  | SPARQL11_Algebra.GP_Filter (f, inner) ->
                      extract_filters inner (f :: acc_f)
                  | uu___1 -> (p, acc_f) in
                let uu___1 = extract_filters opt_pat [] in
                (match uu___1 with
                 | (inner_pat, opt_filters) ->
                     let combined_filter =
                       match opt_filters with
                       | [] -> SPARQL11_Algebra.E_BoolLit true
                       | f::[] -> f
                       | f::rest ->
                           FStar_List_Tot_Base.fold_left
                             (fun a b -> SPARQL11_Algebra.E_And (a, b)) f
                             rest in
                     let new_acc =
                       SPARQL11_Algebra.GP_LeftJoin
                         (acc, inner_pat, combined_filter) in
                     let ps'1 = skip_ws ps' in
                     let ps'2 =
                       match ps_consume ps'1 "." with
                       | FStar_Pervasives_Native.Some p -> p
                       | FStar_Pervasives_Native.None -> ps'1 in
                     parse_ggp_elements ps'2 prefixes new_acc filters)
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some
                  ((apply_filters acc filters), ps1))
       | FStar_Pervasives_Native.None ->
           (match ps_consume ps1 "GRAPH" with
            | FStar_Pervasives_Native.Some ps_after ->
                let ps_after1 = skip_ws ps_after in
                let graph_term_opt =
                  if
                    (ps_starts_with ps_after1 "?") ||
                      (ps_starts_with ps_after1 "$")
                  then
                    match parse_variable ps_after1 with
                    | FStar_Pervasives_Native.Some (v, ps') ->
                        FStar_Pervasives_Native.Some
                          ((SPARQL11_Algebra.PT_Var v), ps')
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                  else
                    (match parse_iri ps_after1 prefixes with
                     | FStar_Pervasives_Native.Some (iri, ps') ->
                         FStar_Pervasives_Native.Some
                           ((SPARQL11_Algebra.PT_IRI iri), ps')
                     | FStar_Pervasives_Native.None ->
                         (match parse_iriref ps_after1 with
                          | FStar_Pervasives_Native.Some (raw, ps') ->
                              let as_iri = Prims.strcat "file:" raw in
                              if RDF_Graph_Executable.is_iri as_iri
                              then
                                FStar_Pervasives_Native.Some
                                  ((SPARQL11_Algebra.PT_IRI as_iri), ps')
                              else FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None)) in
                (match graph_term_opt with
                 | FStar_Pervasives_Native.Some (gt, ps') ->
                     let ps'1 = skip_ws ps' in
                     (match parse_group_graph_pattern ps'1 prefixes with
                      | FStar_Pervasives_Native.Some (graph_pat, ps'') ->
                          let graph_node =
                            SPARQL11_Algebra.GP_Graph (gt, graph_pat) in
                          let new_acc =
                            if acc = SPARQL11_Algebra.GP_Empty
                            then graph_node
                            else SPARQL11_Algebra.GP_Join (acc, graph_node) in
                          let ps''1 = skip_ws ps'' in
                          let ps''2 =
                            match ps_consume ps''1 "." with
                            | FStar_Pervasives_Native.Some p -> p
                            | FStar_Pervasives_Native.None -> ps''1 in
                          parse_ggp_elements ps''2 prefixes new_acc filters
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some
                            ((apply_filters acc filters), ps1))
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some
                       ((apply_filters acc filters), ps1))
            | FStar_Pervasives_Native.None ->
                (match ps_consume ps1 "FILTER" with
                 | FStar_Pervasives_Native.Some ps_after ->
                     let ps_after1 = skip_ws ps_after in
                     (match parse_filter_constraint ps_after1 prefixes with
                      | FStar_Pervasives_Native.Some (filter_expr, ps') ->
                          let ps'1 = skip_ws ps' in
                          let ps'2 =
                            match ps_consume ps'1 "." with
                            | FStar_Pervasives_Native.Some ps'3 -> ps'3
                            | FStar_Pervasives_Native.None -> ps'1 in
                          parse_ggp_elements ps'2 prefixes acc (filter_expr
                            :: filters)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some
                            ((apply_filters acc filters), ps1))
                 | FStar_Pervasives_Native.None ->
                     (match ps_consume ps1 "UNION" with
                      | FStar_Pervasives_Native.Some ps_after ->
                          (match parse_group_graph_pattern ps_after prefixes
                           with
                           | FStar_Pervasives_Native.Some (right, ps') ->
                               let new_acc =
                                 SPARQL11_Algebra.GP_Union (acc, right) in
                               parse_ggp_elements ps' prefixes new_acc
                                 filters
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some
                                 ((apply_filters acc filters), ps1))
                      | FStar_Pervasives_Native.None ->
                          (match ps_consume ps1 "MINUS" with
                           | FStar_Pervasives_Native.Some ps_after ->
                               (match parse_group_graph_pattern ps_after
                                        prefixes
                                with
                                | FStar_Pervasives_Native.Some
                                    (minus_pat, ps') ->
                                    let new_acc =
                                      SPARQL11_Algebra.GP_Minus
                                        (acc, minus_pat) in
                                    parse_ggp_elements ps' prefixes new_acc
                                      filters
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.Some
                                      ((apply_filters acc filters), ps1))
                           | FStar_Pervasives_Native.None ->
                               (match ps_consume ps1 "BIND" with
                                | FStar_Pervasives_Native.Some ps_after ->
                                    let ps_after1 = skip_ws ps_after in
                                    (match ps_expect ps_after1 "(" with
                                     | FStar_Pervasives_Native.Some ps' ->
                                         (match parse_expr ps' prefixes with
                                          | FStar_Pervasives_Native.Some
                                              (e, ps'1) ->
                                              let ps'2 = skip_ws ps'1 in
                                              (match ps_consume ps'2 "AS"
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   ps'3 ->
                                                   (match parse_variable ps'3
                                                    with
                                                    | FStar_Pervasives_Native.Some
                                                        (v, ps'4) ->
                                                        (match ps_expect ps'4
                                                                 ")"
                                                         with
                                                         | FStar_Pervasives_Native.Some
                                                             ps'5 ->
                                                             let new_acc =
                                                               SPARQL11_Algebra.GP_Bind
                                                                 (e, v, acc) in
                                                             let ps'6 =
                                                               skip_ws ps'5 in
                                                             let ps'7 =
                                                               match 
                                                                 ps_consume
                                                                   ps'6 "."
                                                               with
                                                               | FStar_Pervasives_Native.Some
                                                                   p -> p
                                                               | FStar_Pervasives_Native.None
                                                                   -> ps'6 in
                                                             parse_ggp_elements
                                                               ps'7 prefixes
                                                               new_acc
                                                               filters
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             FStar_Pervasives_Native.Some
                                                               ((apply_filters
                                                                   acc
                                                                   filters),
                                                                 ps1))
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        FStar_Pervasives_Native.Some
                                                          ((apply_filters acc
                                                              filters), ps1))
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.Some
                                                     ((apply_filters acc
                                                         filters), ps1))
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.Some
                                                ((apply_filters acc filters),
                                                  ps1))
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.Some
                                           ((apply_filters acc filters), ps1))
                                | FStar_Pervasives_Native.None ->
                                    (match ps_consume ps1 "VALUES" with
                                     | FStar_Pervasives_Native.Some ps_after
                                         ->
                                         (match parse_values_clause ps_after
                                                  prefixes
                                          with
                                          | FStar_Pervasives_Native.Some
                                              (vars, rows, ps') ->
                                              let new_acc =
                                                if
                                                  acc =
                                                    SPARQL11_Algebra.GP_Empty
                                                then
                                                  SPARQL11_Algebra.GP_Values
                                                    (vars, rows)
                                                else
                                                  SPARQL11_Algebra.GP_Join
                                                    (acc,
                                                      (SPARQL11_Algebra.GP_Values
                                                         (vars, rows))) in
                                              parse_ggp_elements ps' prefixes
                                                new_acc filters
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.Some
                                                ((apply_filters acc filters),
                                                  ps1))
                                     | FStar_Pervasives_Native.None ->
                                         (match ps_peek ps1 with
                                          | FStar_Pervasives_Native.Some c
                                              when
                                              (FStar_Char.int_of_char c) =
                                                (Prims.of_int (0x7B))
                                              ->
                                              (match parse_group_graph_pattern
                                                       ps1 prefixes
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   (sub, ps') ->
                                                   let ps'1 = skip_ws ps' in
                                                   (match ps_consume ps'1
                                                            "UNION"
                                                    with
                                                    | FStar_Pervasives_Native.Some
                                                        ps'' ->
                                                        let rec parse_union_chain
                                                          left ps2 =
                                                          match parse_group_graph_pattern
                                                                  ps2
                                                                  prefixes
                                                          with
                                                          | FStar_Pervasives_Native.Some
                                                              (right, ps'2)
                                                              ->
                                                              let union_pat =
                                                                SPARQL11_Algebra.GP_Union
                                                                  (left,
                                                                    right) in
                                                              let ps'3 =
                                                                skip_ws ps'2 in
                                                              (match 
                                                                 ps_consume
                                                                   ps'3
                                                                   "UNION"
                                                               with
                                                               | FStar_Pervasives_Native.Some
                                                                   ps''1 ->
                                                                   parse_union_chain
                                                                    union_pat
                                                                    ps''1
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   FStar_Pervasives_Native.Some
                                                                    (union_pat,
                                                                    ps'3))
                                                          | FStar_Pervasives_Native.None
                                                              ->
                                                              FStar_Pervasives_Native.Some
                                                                (left, ps2) in
                                                        (match parse_union_chain
                                                                 sub ps''
                                                         with
                                                         | FStar_Pervasives_Native.Some
                                                             (union_pat,
                                                              ps'2)
                                                             ->
                                                             let new_acc =
                                                               if
                                                                 acc =
                                                                   SPARQL11_Algebra.GP_Empty
                                                               then union_pat
                                                               else
                                                                 SPARQL11_Algebra.GP_Join
                                                                   (acc,
                                                                    union_pat) in
                                                             parse_ggp_elements
                                                               ps'2 prefixes
                                                               new_acc
                                                               filters
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             let new_acc =
                                                               if
                                                                 acc =
                                                                   SPARQL11_Algebra.GP_Empty
                                                               then sub
                                                               else
                                                                 SPARQL11_Algebra.GP_Join
                                                                   (acc, sub) in
                                                             parse_ggp_elements
                                                               ps'1 prefixes
                                                               new_acc
                                                               filters)
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        let new_acc =
                                                          if
                                                            acc =
                                                              SPARQL11_Algebra.GP_Empty
                                                          then sub
                                                          else
                                                            SPARQL11_Algebra.GP_Join
                                                              (acc, sub) in
                                                        parse_ggp_elements
                                                          ps'1 prefixes
                                                          new_acc filters)
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.Some
                                                     ((apply_filters acc
                                                         filters), ps1))
                                          | uu___1 ->
                                              (match parse_triples_block_pp
                                                       ps1 prefixes
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   (pat, ps') when
                                                   Prims.op_Negation
                                                     (pat =
                                                        SPARQL11_Algebra.GP_Empty)
                                                   ->
                                                   let new_acc =
                                                     ggp_join acc pat in
                                                   let ps'1 = skip_ws ps' in
                                                   let ps'2 =
                                                     match ps_consume ps'1
                                                             "."
                                                     with
                                                     | FStar_Pervasives_Native.Some
                                                         p -> p
                                                     | FStar_Pervasives_Native.None
                                                         -> ps'1 in
                                                   parse_ggp_elements ps'2
                                                     prefixes new_acc filters
                                               | uu___2 ->
                                                   FStar_Pervasives_Native.Some
                                                     ((apply_filters acc
                                                         filters), ps1))))))))))
and parse_filter_constraint (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.expr * pstate) FStar_Pervasives_Native.option=
  match ps_peek ps with
  | FStar_Pervasives_Native.Some c when
      (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
      let ps1 = ps_advance ps Prims.int_one in
      (match parse_expr ps1 prefixes with
       | FStar_Pervasives_Native.Some (e, ps2) ->
           (match ps_expect ps2 ")" with
            | FStar_Pervasives_Native.Some ps3 ->
                FStar_Pervasives_Native.Some (e, ps3)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> parse_builtin_call ps prefixes
and parse_values_clause (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.var_name Prims.list * RDF_Graph_Executable.rdf_term
    FStar_Pervasives_Native.option Prims.list Prims.list * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let parse_var_list ps2 =
    match ps_consume ps2 "(" with
    | FStar_Pervasives_Native.Some ps3 ->
        let rec loop acc ps4 =
          let ps5 = skip_ws ps4 in
          match parse_variable ps5 with
          | FStar_Pervasives_Native.Some (v, ps6) -> loop (v :: acc) ps6
          | FStar_Pervasives_Native.None ->
              (match ps_expect ps5 ")" with
               | FStar_Pervasives_Native.Some ps6 ->
                   FStar_Pervasives_Native.Some
                     ((FStar_List_Tot_Base.rev acc), ps6)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None) in
        loop [] ps3
    | FStar_Pervasives_Native.None ->
        (match parse_variable ps2 with
         | FStar_Pervasives_Native.Some (v, ps3) ->
             FStar_Pervasives_Native.Some ([v], ps3)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None) in
  match parse_var_list ps1 with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (vars, ps2) ->
      let ps3 = skip_ws ps2 in
      (match ps_consume ps3 "{" with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ps4 ->
           let n_vars = FStar_List_Tot_Base.length vars in
           let parse_one_term ps5 =
             let ps6 = skip_ws ps5 in
             match ps_consume ps6 "UNDEF" with
             | FStar_Pervasives_Native.Some ps7 ->
                 FStar_Pervasives_Native.Some
                   (FStar_Pervasives_Native.None, ps7)
             | FStar_Pervasives_Native.None ->
                 (match parse_iri ps6 prefixes with
                  | FStar_Pervasives_Native.Some (iri, ps7) ->
                      FStar_Pervasives_Native.Some
                        ((FStar_Pervasives_Native.Some
                            (RDF_Graph_Executable.T_IRI iri)), ps7)
                  | FStar_Pervasives_Native.None ->
                      (match parse_rdf_literal ps6 prefixes with
                       | FStar_Pervasives_Native.Some (lit, ps7) ->
                           FStar_Pervasives_Native.Some
                             ((FStar_Pervasives_Native.Some
                                 (RDF_Graph_Executable.T_Literal lit)), ps7)
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None)) in
           let rec parse_rows acc ps5 =
             let ps6 = skip_ws ps5 in
             match ps_consume ps6 "}" with
             | FStar_Pervasives_Native.Some ps7 ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List_Tot_Base.rev acc), ps7)
             | FStar_Pervasives_Native.None ->
                 (match ps_consume ps6 "(" with
                  | FStar_Pervasives_Native.Some ps7 ->
                      let rec parse_row acc1 ps8 =
                        let ps9 = skip_ws ps8 in
                        match ps_consume ps9 ")" with
                        | FStar_Pervasives_Native.Some ps10 ->
                            FStar_Pervasives_Native.Some
                              ((FStar_List_Tot_Base.rev acc1), ps10)
                        | FStar_Pervasives_Native.None ->
                            (match parse_one_term ps9 with
                             | FStar_Pervasives_Native.Some (t, ps10) ->
                                 parse_row (t :: acc1) ps10
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None) in
                      (match parse_row [] ps7 with
                       | FStar_Pervasives_Native.Some (row, ps8) ->
                           parse_rows (row :: acc) ps8
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None ->
                      if n_vars = Prims.int_one
                      then
                        (match parse_one_term ps6 with
                         | FStar_Pervasives_Native.Some (t, ps7) ->
                             parse_rows ([t] :: acc) ps7
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None) in
           (match parse_rows [] ps4 with
            | FStar_Pervasives_Native.Some (rows, ps5) ->
                FStar_Pervasives_Native.Some (vars, rows, ps5)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let parse_select_clause (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.select_clause * Prims.bool * Prims.bool * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "SELECT" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      let uu___ =
        match ps_consume ps3 "DISTINCT" with
        | FStar_Pervasives_Native.Some ps4 -> (true, false, ps4)
        | FStar_Pervasives_Native.None ->
            (match ps_consume ps3 "REDUCED" with
             | FStar_Pervasives_Native.Some ps4 -> (false, true, ps4)
             | FStar_Pervasives_Native.None -> (false, false, ps3)) in
      (match uu___ with
       | (is_distinct, is_reduced, ps4) ->
           let ps5 = skip_ws ps4 in
           (match ps_consume ps5 "*" with
            | FStar_Pervasives_Native.Some ps6 ->
                FStar_Pervasives_Native.Some
                  (SPARQL11_Algebra.Select_All, is_distinct, is_reduced, ps6)
            | FStar_Pervasives_Native.None ->
                let rec parse_items acc ps6 =
                  let ps7 = skip_ws ps6 in
                  match ps_peek ps7 with
                  | FStar_Pervasives_Native.Some c when
                      (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
                      let ps' = ps_advance ps7 Prims.int_one in
                      (match parse_expr ps' prefixes with
                       | FStar_Pervasives_Native.Some (e, ps'1) ->
                           let ps'2 = skip_ws ps'1 in
                           (match ps_consume ps'2 "AS" with
                            | FStar_Pervasives_Native.Some ps'3 ->
                                (match parse_variable ps'3 with
                                 | FStar_Pervasives_Native.Some (v, ps'4) ->
                                     (match ps_expect ps'4 ")" with
                                      | FStar_Pervasives_Native.Some ps'5 ->
                                          parse_items
                                            ((SPARQL11_Algebra.SI_Expr (e, v))
                                            :: acc) ps'5
                                      | FStar_Pervasives_Native.None ->
                                          if Prims.uu___is_Nil acc
                                          then FStar_Pervasives_Native.None
                                          else
                                            FStar_Pervasives_Native.Some
                                              ((FStar_List_Tot_Base.rev acc),
                                                ps7))
                                 | FStar_Pervasives_Native.None ->
                                     if Prims.uu___is_Nil acc
                                     then FStar_Pervasives_Native.None
                                     else
                                       FStar_Pervasives_Native.Some
                                         ((FStar_List_Tot_Base.rev acc), ps7))
                            | FStar_Pervasives_Native.None ->
                                if Prims.uu___is_Nil acc
                                then FStar_Pervasives_Native.None
                                else
                                  FStar_Pervasives_Native.Some
                                    ((FStar_List_Tot_Base.rev acc), ps7))
                       | FStar_Pervasives_Native.None ->
                           if Prims.uu___is_Nil acc
                           then FStar_Pervasives_Native.None
                           else
                             FStar_Pervasives_Native.Some
                               ((FStar_List_Tot_Base.rev acc), ps7))
                  | uu___1 ->
                      (match parse_variable ps7 with
                       | FStar_Pervasives_Native.Some (v, ps8) ->
                           parse_items ((SPARQL11_Algebra.SI_Var v) :: acc)
                             ps8
                       | FStar_Pervasives_Native.None ->
                           if Prims.uu___is_Nil acc
                           then FStar_Pervasives_Native.None
                           else
                             FStar_Pervasives_Native.Some
                               ((FStar_List_Tot_Base.rev acc), ps7)) in
                (match parse_items [] ps5 with
                 | FStar_Pervasives_Native.Some (items, ps6) ->
                     FStar_Pervasives_Native.Some
                       ((SPARQL11_Algebra.Select_Vars items), is_distinct,
                         is_reduced, ps6)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)))
let rec parse_order_by (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.order_condition Prims.list * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "ORDER" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      (match ps_consume ps3 "BY" with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ps4 ->
           let rec parse_conditions acc ps5 =
             let ps6 = skip_ws ps5 in
             match ps_consume ps6 "ASC" with
             | FStar_Pervasives_Native.Some ps' ->
                 let ps'1 = skip_ws ps' in
                 (match ps_expect ps'1 "(" with
                  | FStar_Pervasives_Native.Some ps'2 ->
                      (match parse_expr ps'2 prefixes with
                       | FStar_Pervasives_Native.Some (e, ps'3) ->
                           (match ps_expect ps'3 ")" with
                            | FStar_Pervasives_Native.Some ps'4 ->
                                parse_conditions ((SPARQL11_Algebra.OC_Asc e)
                                  :: acc) ps'4
                            | FStar_Pervasives_Native.None ->
                                if Prims.uu___is_Nil acc
                                then FStar_Pervasives_Native.None
                                else
                                  FStar_Pervasives_Native.Some
                                    ((FStar_List_Tot_Base.rev acc), ps6))
                       | FStar_Pervasives_Native.None ->
                           if Prims.uu___is_Nil acc
                           then FStar_Pervasives_Native.None
                           else
                             FStar_Pervasives_Native.Some
                               ((FStar_List_Tot_Base.rev acc), ps6))
                  | FStar_Pervasives_Native.None ->
                      if Prims.uu___is_Nil acc
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_List_Tot_Base.rev acc), ps6))
             | FStar_Pervasives_Native.None ->
                 (match ps_consume ps6 "DESC" with
                  | FStar_Pervasives_Native.Some ps' ->
                      let ps'1 = skip_ws ps' in
                      (match ps_expect ps'1 "(" with
                       | FStar_Pervasives_Native.Some ps'2 ->
                           (match parse_expr ps'2 prefixes with
                            | FStar_Pervasives_Native.Some (e, ps'3) ->
                                (match ps_expect ps'3 ")" with
                                 | FStar_Pervasives_Native.Some ps'4 ->
                                     parse_conditions
                                       ((SPARQL11_Algebra.OC_Desc e) :: acc)
                                       ps'4
                                 | FStar_Pervasives_Native.None ->
                                     if Prims.uu___is_Nil acc
                                     then FStar_Pervasives_Native.None
                                     else
                                       FStar_Pervasives_Native.Some
                                         ((FStar_List_Tot_Base.rev acc), ps6))
                            | FStar_Pervasives_Native.None ->
                                if Prims.uu___is_Nil acc
                                then FStar_Pervasives_Native.None
                                else
                                  FStar_Pervasives_Native.Some
                                    ((FStar_List_Tot_Base.rev acc), ps6))
                       | FStar_Pervasives_Native.None ->
                           if Prims.uu___is_Nil acc
                           then FStar_Pervasives_Native.None
                           else
                             FStar_Pervasives_Native.Some
                               ((FStar_List_Tot_Base.rev acc), ps6))
                  | FStar_Pervasives_Native.None ->
                      (match parse_expr ps6 prefixes with
                       | FStar_Pervasives_Native.Some (e, ps7) ->
                           parse_conditions ((SPARQL11_Algebra.OC_Asc e) ::
                             acc) ps7
                       | FStar_Pervasives_Native.None ->
                           if Prims.uu___is_Nil acc
                           then FStar_Pervasives_Native.None
                           else
                             FStar_Pervasives_Native.Some
                               ((FStar_List_Tot_Base.rev acc), ps6))) in
           parse_conditions [] ps4)
let parse_nat_digits (ps : pstate) :
  (Prims.nat * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  let start = ps1.pos in
  let rec skip_digits ps2 =
    match ps_peek ps2 with
    | FStar_Pervasives_Native.Some c when is_digit c ->
        skip_digits (ps_advance ps2 Prims.int_one)
    | uu___ -> ps2 in
  let ps2 = skip_digits ps1 in
  if ps2.pos = start
  then FStar_Pervasives_Native.None
  else
    (let s = FStar_String.sub ps1.inp start (ps2.pos - start) in
     let chars = FStar_String.list_of_string s in
     let rec to_int cs acc =
       match cs with
       | [] -> acc
       | c::rest ->
           to_int rest
             ((acc * (Prims.of_int (10))) +
                ((FStar_Char.int_of_char c) - (Prims.of_int (0x30)))) in
     let n = to_int chars Prims.int_zero in
     if n >= Prims.int_zero
     then FStar_Pervasives_Native.Some (n, ps2)
     else FStar_Pervasives_Native.None)
let parse_limit (ps : pstate) :
  (Prims.nat * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "LIMIT" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in parse_nat_digits ps3
let parse_offset (ps : pstate) :
  (Prims.nat * pstate) FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "OFFSET" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in parse_nat_digits ps3
let rec parse_group_by (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.group_condition Prims.list * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "GROUP" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let ps3 = skip_ws ps2 in
      (match ps_consume ps3 "BY" with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ps4 ->
           let rec parse_conditions acc ps5 =
             let ps6 = skip_ws ps5 in
             match parse_variable ps6 with
             | FStar_Pervasives_Native.Some (v, ps7) ->
                 parse_conditions ((SPARQL11_Algebra.GC_Var v) :: acc) ps7
             | FStar_Pervasives_Native.None ->
                 (match ps_peek ps6 with
                  | FStar_Pervasives_Native.Some c when
                      (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
                      let ps' = ps_advance ps6 Prims.int_one in
                      (match parse_expr ps' prefixes with
                       | FStar_Pervasives_Native.Some (e, ps'1) ->
                           let ps'2 = skip_ws ps'1 in
                           (match ps_consume ps'2 "AS" with
                            | FStar_Pervasives_Native.Some ps'3 ->
                                (match parse_variable ps'3 with
                                 | FStar_Pervasives_Native.Some (v, ps'4) ->
                                     (match ps_expect ps'4 ")" with
                                      | FStar_Pervasives_Native.Some ps'5 ->
                                          parse_conditions
                                            ((SPARQL11_Algebra.GC_Expr
                                                (e,
                                                  (FStar_Pervasives_Native.Some
                                                     v))) :: acc) ps'5
                                      | FStar_Pervasives_Native.None ->
                                          if Prims.uu___is_Nil acc
                                          then FStar_Pervasives_Native.None
                                          else
                                            FStar_Pervasives_Native.Some
                                              ((FStar_List_Tot_Base.rev acc),
                                                ps6))
                                 | FStar_Pervasives_Native.None ->
                                     if Prims.uu___is_Nil acc
                                     then FStar_Pervasives_Native.None
                                     else
                                       FStar_Pervasives_Native.Some
                                         ((FStar_List_Tot_Base.rev acc), ps6))
                            | FStar_Pervasives_Native.None ->
                                (match ps_expect ps'2 ")" with
                                 | FStar_Pervasives_Native.Some ps'3 ->
                                     parse_conditions
                                       ((SPARQL11_Algebra.GC_Expr
                                           (e, FStar_Pervasives_Native.None))
                                       :: acc) ps'3
                                 | FStar_Pervasives_Native.None ->
                                     if Prims.uu___is_Nil acc
                                     then FStar_Pervasives_Native.None
                                     else
                                       FStar_Pervasives_Native.Some
                                         ((FStar_List_Tot_Base.rev acc), ps6)))
                       | FStar_Pervasives_Native.None ->
                           if Prims.uu___is_Nil acc
                           then FStar_Pervasives_Native.None
                           else
                             FStar_Pervasives_Native.Some
                               ((FStar_List_Tot_Base.rev acc), ps6))
                  | uu___ ->
                      if Prims.uu___is_Nil acc
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_List_Tot_Base.rev acc), ps6)) in
           parse_conditions [] ps4)
let rec parse_having (ps : pstate)
  (prefixes : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  (SPARQL11_Algebra.having_condition Prims.list * pstate)
    FStar_Pervasives_Native.option=
  let ps1 = skip_ws ps in
  match ps_consume ps1 "HAVING" with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps2 ->
      let rec parse_conditions acc ps3 =
        let ps4 = skip_ws ps3 in
        match ps_peek ps4 with
        | FStar_Pervasives_Native.Some c when
            (FStar_Char.int_of_char c) = (Prims.of_int (0x28)) ->
            let ps' = ps_advance ps4 Prims.int_one in
            (match parse_expr ps' prefixes with
             | FStar_Pervasives_Native.Some (e, ps'1) ->
                 (match ps_expect ps'1 ")" with
                  | FStar_Pervasives_Native.Some ps'2 ->
                      parse_conditions (e :: acc) ps'2
                  | FStar_Pervasives_Native.None ->
                      if Prims.uu___is_Nil acc
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_List_Tot_Base.rev acc), ps4))
             | FStar_Pervasives_Native.None ->
                 if Prims.uu___is_Nil acc
                 then FStar_Pervasives_Native.None
                 else
                   FStar_Pervasives_Native.Some
                     ((FStar_List_Tot_Base.rev acc), ps4))
        | uu___ ->
            if Prims.uu___is_Nil acc
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                ((FStar_List_Tot_Base.rev acc), ps4) in
      parse_conditions [] ps2
let parse_query (input : Prims.string) :
  SPARQL11_Algebra.query FStar_Pervasives_Native.option=
  let ps = mk_pstate input in
  let uu___ = parse_prologue ps FStar_Pervasives_Native.None [] in
  match uu___ with
  | (base, prefixes, ps1) ->
      let prefixes1 =
        match base with
        | FStar_Pervasives_Native.Some b -> ("__base__", b) :: prefixes
        | FStar_Pervasives_Native.None -> prefixes in
      let ps2 = skip_ws ps1 in
      (match ps_consume ps2 "ASK" with
       | FStar_Pervasives_Native.Some ps3 ->
           (match parse_group_graph_pattern ps3 prefixes1 with
            | FStar_Pervasives_Native.Some (pattern, ps4) ->
                FStar_Pervasives_Native.Some
                  {
                    SPARQL11_Algebra.q_base = base;
                    SPARQL11_Algebra.q_prefixes = prefixes1;
                    SPARQL11_Algebra.q_form = SPARQL11_Algebra.QF_Ask;
                    SPARQL11_Algebra.q_dataset = [];
                    SPARQL11_Algebra.q_pattern = pattern;
                    SPARQL11_Algebra.q_group_by =
                      FStar_Pervasives_Native.None;
                    SPARQL11_Algebra.q_having = FStar_Pervasives_Native.None;
                    SPARQL11_Algebra.q_modifier =
                      {
                        SPARQL11_Algebra.sm_order_by =
                          FStar_Pervasives_Native.None;
                        SPARQL11_Algebra.sm_distinct = false;
                        SPARQL11_Algebra.sm_reduced = false;
                        SPARQL11_Algebra.sm_offset =
                          FStar_Pervasives_Native.None;
                        SPARQL11_Algebra.sm_limit =
                          FStar_Pervasives_Native.None
                      }
                  }
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None ->
           (match parse_select_clause ps2 prefixes1 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (sel, distinct, reduced, ps3) ->
                let ps4 = skip_ws ps3 in
                let rec skip_from ps5 =
                  let ps6 = skip_ws ps5 in
                  match ps_consume ps6 "FROM" with
                  | FStar_Pervasives_Native.Some ps7 ->
                      let ps8 = skip_ws ps7 in
                      let ps9 =
                        match ps_consume ps8 "NAMED" with
                        | FStar_Pervasives_Native.Some ps10 -> ps10
                        | FStar_Pervasives_Native.None -> ps8 in
                      let ps10 = skip_ws ps9 in
                      let ps11 =
                        match parse_iriref ps10 with
                        | FStar_Pervasives_Native.Some (uu___1, ps12) -> ps12
                        | FStar_Pervasives_Native.None -> ps10 in
                      skip_from ps11
                  | FStar_Pervasives_Native.None -> ps6 in
                let ps5 = skip_from ps4 in
                let ps6 = skip_ws ps5 in
                let ps7 =
                  match ps_consume ps6 "WHERE" with
                  | FStar_Pervasives_Native.Some ps8 -> ps8
                  | FStar_Pervasives_Native.None -> ps6 in
                (match parse_group_graph_pattern ps7 prefixes1 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (pattern, ps8) ->
                     let group_by = parse_group_by ps8 prefixes1 in
                     let uu___1 =
                       match group_by with
                       | FStar_Pervasives_Native.Some (gc, ps9) ->
                           ((FStar_Pervasives_Native.Some gc), ps9)
                       | FStar_Pervasives_Native.None ->
                           (FStar_Pervasives_Native.None, ps8) in
                     (match uu___1 with
                      | (gb, ps9) ->
                          let having = parse_having ps9 prefixes1 in
                          let uu___2 =
                            match having with
                            | FStar_Pervasives_Native.Some (hc, ps10) ->
                                ((FStar_Pervasives_Native.Some hc), ps10)
                            | FStar_Pervasives_Native.None ->
                                (FStar_Pervasives_Native.None, ps9) in
                          (match uu___2 with
                           | (hv, ps10) ->
                               let order = parse_order_by ps10 prefixes1 in
                               let uu___3 =
                                 match order with
                                 | FStar_Pervasives_Native.Some (oc, ps11) ->
                                     ((FStar_Pervasives_Native.Some oc),
                                       ps11)
                                 | FStar_Pervasives_Native.None ->
                                     (FStar_Pervasives_Native.None, ps10) in
                               (match uu___3 with
                                | (ob, ps11) ->
                                    let lim = parse_limit ps11 in
                                    let uu___4 =
                                      match lim with
                                      | FStar_Pervasives_Native.Some
                                          (n, ps12) ->
                                          ((FStar_Pervasives_Native.Some n),
                                            ps12)
                                      | FStar_Pervasives_Native.None ->
                                          (FStar_Pervasives_Native.None,
                                            ps11) in
                                    (match uu___4 with
                                     | (l, ps12) ->
                                         let off = parse_offset ps12 in
                                         let uu___5 =
                                           match off with
                                           | FStar_Pervasives_Native.Some
                                               (n, ps13) ->
                                               ((FStar_Pervasives_Native.Some
                                                   n), ps13)
                                           | FStar_Pervasives_Native.None ->
                                               (FStar_Pervasives_Native.None,
                                                 ps12) in
                                         (match uu___5 with
                                          | (o, ps13) ->
                                              let uu___6 =
                                                match l with
                                                | FStar_Pervasives_Native.Some
                                                    uu___7 -> (l, ps13)
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    (match parse_limit ps13
                                                     with
                                                     | FStar_Pervasives_Native.Some
                                                         (n, ps14) ->
                                                         ((FStar_Pervasives_Native.Some
                                                             n), ps14)
                                                     | FStar_Pervasives_Native.None
                                                         -> (l, ps13)) in
                                              (match uu___6 with
                                               | (l1, ps14) ->
                                                   let ps15 = skip_ws ps14 in
                                                   let uu___7 =
                                                     match ps_consume ps15
                                                             "VALUES"
                                                     with
                                                     | FStar_Pervasives_Native.Some
                                                         ps_v ->
                                                         (match parse_values_clause
                                                                  ps_v
                                                                  prefixes1
                                                          with
                                                          | FStar_Pervasives_Native.Some
                                                              (vars, rows,
                                                               ps')
                                                              ->
                                                              ((SPARQL11_Algebra.GP_Join
                                                                  (pattern,
                                                                    (
                                                                    SPARQL11_Algebra.GP_Values
                                                                    (vars,
                                                                    rows)))),
                                                                ps')
                                                          | FStar_Pervasives_Native.None
                                                              ->
                                                              (pattern, ps15))
                                                     | FStar_Pervasives_Native.None
                                                         -> (pattern, ps15) in
                                                   (match uu___7 with
                                                    | (pattern1, _ps) ->
                                                        FStar_Pervasives_Native.Some
                                                          {
                                                            SPARQL11_Algebra.q_base
                                                              = base;
                                                            SPARQL11_Algebra.q_prefixes
                                                              = prefixes1;
                                                            SPARQL11_Algebra.q_form
                                                              =
                                                              (SPARQL11_Algebra.QF_Select
                                                                 sel);
                                                            SPARQL11_Algebra.q_dataset
                                                              = [];
                                                            SPARQL11_Algebra.q_pattern
                                                              = pattern1;
                                                            SPARQL11_Algebra.q_group_by
                                                              = gb;
                                                            SPARQL11_Algebra.q_having
                                                              = hv;
                                                            SPARQL11_Algebra.q_modifier
                                                              =
                                                              {
                                                                SPARQL11_Algebra.sm_order_by
                                                                  = ob;
                                                                SPARQL11_Algebra.sm_distinct
                                                                  = distinct;
                                                                SPARQL11_Algebra.sm_reduced
                                                                  = reduced;
                                                                SPARQL11_Algebra.sm_offset
                                                                  = o;
                                                                SPARQL11_Algebra.sm_limit
                                                                  = l1
                                                              }
                                                          }))))))))))
