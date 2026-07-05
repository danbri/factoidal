open Prims
let lparen_code : Prims.int= (Prims.of_int (0x28))
let rparen_code : Prims.int= (Prims.of_int (0x29))
let langle_code : Prims.int= (Prims.of_int (0x3C))
let rangle_code : Prims.int= (Prims.of_int (0x3E))
let quote_code : Prims.int= (Prims.of_int (0x22))
let colon_code : Prims.int= (Prims.of_int (0x3A))
let eq_code : Prims.int= (Prims.of_int (0x3D))
let caret_code : Prims.int= (Prims.of_int (0x5E))
let char_at_code (input : Prims.string) (pos : Prims.nat) : Prims.int=
  if pos < (Parser_FastString.fs_byte_length input)
  then FStar_Char.int_of_char (Parser_FastString.fs_byte_index input pos)
  else (Prims.of_int (-1))
let is_fs_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let skip_ws (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  match Parser_Combinators.ptake_while_pos is_fs_ws input pos with
  | Parser_Combinators.ParseOk (uu___, pos') -> pos'
  | Parser_Combinators.ParseFail (uu___, fpos) -> fpos
let is_ident_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))) ||
       ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))))
      || ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
     || (code = (Prims.of_int (0x5F))))
    || (code = (Prims.of_int (0x2D)))
let try_match_word (input : Prims.string) (pos : Prims.nat)
  (kw : Prims.string) : Prims.nat FStar_Pervasives_Native.option=
  match Parser_Combinators.ptake_while1_pos is_ident_char input pos with
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
  | Parser_Combinators.ParseOk (w, pos') ->
      if w = kw
      then FStar_Pervasives_Native.Some pos'
      else FStar_Pervasives_Native.None
let rec scan_angle_iri_end (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then FStar_Pervasives_Native.None
     else
       (let code = char_at_code input pos in
        if code = rangle_code
        then FStar_Pervasives_Native.Some pos
        else
          scan_angle_iri_end input (pos + Prims.int_one)
            (fuel - Prims.int_one)))
let scan_angle_iri (input : Prims.string) (start : Prims.nat)
  (fuel : Prims.nat) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  match scan_angle_iri_end input start fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some gt_pos ->
      if gt_pos >= start
      then
        FStar_Pervasives_Native.Some
          ((Parser_FastString.fs_byte_sub input start (gt_pos - start)),
            (gt_pos + Prims.int_one))
      else FStar_Pervasives_Native.None
let rec lookup_prefix (prefixes : (Prims.string * Prims.string) Prims.list)
  (pfx : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  match prefixes with
  | [] -> FStar_Pervasives_Native.None
  | (p, ns)::rest ->
      if p = pfx
      then FStar_Pervasives_Native.Some ns
      else lookup_prefix rest pfx
let parse_curie (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Graph_Executable.wf_iri * Prims.nat) FStar_Pervasives_Native.option=
  match Parser_Combinators.ptake_while_pos is_ident_char input pos with
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
  | Parser_Combinators.ParseOk (pfx, pos1) ->
      if (char_at_code input pos1) <> colon_code
      then FStar_Pervasives_Native.None
      else
        (let pos2 = pos1 + Prims.int_one in
         match Parser_Combinators.ptake_while1_pos is_ident_char input pos2
         with
         | Parser_Combinators.ParseFail (uu___1, uu___2) ->
             FStar_Pervasives_Native.None
         | Parser_Combinators.ParseOk (local, pos3) ->
             (match lookup_prefix prefixes pfx with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some ns ->
                  let full = FStar_String.concat "" [ns; local] in
                  if RDF_Graph_Executable.is_iri full
                  then FStar_Pervasives_Native.Some (full, pos3)
                  else FStar_Pervasives_Native.None))
let parse_fs_iri (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Graph_Executable.wf_iri * Prims.nat) FStar_Pervasives_Native.option=
  if (char_at_code input pos) = langle_code
  then
    match scan_angle_iri input (pos + Prims.int_one)
            ((Parser_FastString.fs_byte_length input) - pos)
    with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (s, pos') ->
        (if RDF_Graph_Executable.is_iri s
         then FStar_Pervasives_Native.Some (s, pos')
         else FStar_Pervasives_Native.None)
  else parse_curie prefixes input pos
let rec scan_quote_end (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then FStar_Pervasives_Native.None
     else
       (let code = char_at_code input pos in
        if code = quote_code
        then FStar_Pervasives_Native.Some pos
        else
          scan_quote_end input (pos + Prims.int_one) (fuel - Prims.int_one)))
let parse_fs_literal (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Graph_Executable.wf_literal * Prims.nat)
    FStar_Pervasives_Native.option=
  if (char_at_code input pos) <> quote_code
  then FStar_Pervasives_Native.None
  else
    (match scan_quote_end input (pos + Prims.int_one)
             ((Parser_FastString.fs_byte_length input) - pos)
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some end_pos ->
         if end_pos < (pos + Prims.int_one)
         then FStar_Pervasives_Native.None
         else
           (let lexical =
              Parser_FastString.fs_byte_sub input (pos + Prims.int_one)
                (end_pos - (pos + Prims.int_one)) in
            let pos1 = skip_ws input (end_pos + Prims.int_one) in
            if
              ((char_at_code input pos1) = caret_code) &&
                ((char_at_code input (pos1 + Prims.int_one)) = caret_code)
            then
              match parse_fs_iri prefixes input (pos1 + (Prims.of_int (2)))
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (dt, pos2) ->
                  let lit =
                    {
                      RDF_Graph_Executable.lexical_form = lexical;
                      RDF_Graph_Executable.datatype = dt;
                      RDF_Graph_Executable.lang_tag =
                        FStar_Pervasives_Native.None
                    } in
                  (if RDF_Graph_Executable.literal_wf lit
                   then FStar_Pervasives_Native.Some (lit, pos2)
                   else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None))
let rec parse_prefixes_acc (input : Prims.string) (pos : Prims.nat)
  (acc : (Prims.string * Prims.string) Prims.list) (fuel : Prims.nat) :
  ((Prims.string * Prims.string) Prims.list * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some (acc, pos)
  else
    (let fuel1 = fuel - Prims.int_one in
     let pos0 = skip_ws input pos in
     match try_match_word input pos0 "Prefix" with
     | FStar_Pervasives_Native.None ->
         FStar_Pervasives_Native.Some (acc, pos0)
     | FStar_Pervasives_Native.Some pos1 ->
         let pos2 = skip_ws input pos1 in
         if (char_at_code input pos2) <> lparen_code
         then FStar_Pervasives_Native.None
         else
           (let pos3 = skip_ws input (pos2 + Prims.int_one) in
            match Parser_Combinators.ptake_while_pos is_ident_char input pos3
            with
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                FStar_Pervasives_Native.None
            | Parser_Combinators.ParseOk (pfx, pos4) ->
                if (char_at_code input pos4) <> colon_code
                then FStar_Pervasives_Native.None
                else
                  (let pos5 = skip_ws input (pos4 + Prims.int_one) in
                   if (char_at_code input pos5) <> eq_code
                   then FStar_Pervasives_Native.None
                   else
                     (let pos6 = skip_ws input (pos5 + Prims.int_one) in
                      if (char_at_code input pos6) <> langle_code
                      then FStar_Pervasives_Native.None
                      else
                        (match scan_angle_iri input (pos6 + Prims.int_one)
                                 ((Parser_FastString.fs_byte_length input) -
                                    pos6)
                         with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some (ns, pos7) ->
                             let pos8 = skip_ws input pos7 in
                             if (char_at_code input pos8) <> rparen_code
                             then FStar_Pervasives_Native.None
                             else
                               parse_prefixes_acc input
                                 (pos8 + Prims.int_one) ((pfx, ns) :: acc)
                                 fuel1)))))
let parse_declaration (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Graph_Executable.triple * Prims.nat) FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     let entity_kind =
       match try_match_word input pos2 "ObjectProperty" with
       | FStar_Pervasives_Native.Some p ->
           FStar_Pervasives_Native.Some
             (p, RDF_Graph_Executable.owl_ObjectProperty)
       | FStar_Pervasives_Native.None ->
           (match try_match_word input pos2 "DataProperty" with
            | FStar_Pervasives_Native.Some p ->
                FStar_Pervasives_Native.Some
                  (p, RDF_Graph_Executable.owl_DatatypeProperty)
            | FStar_Pervasives_Native.None ->
                (match try_match_word input pos2 "NamedIndividual" with
                 | FStar_Pervasives_Native.Some p ->
                     FStar_Pervasives_Native.Some
                       (p, RDF_Graph_Executable.owl_NamedIndividual)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)) in
     match entity_kind with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (pos3, type_iri) ->
         let pos4 = skip_ws input pos3 in
         if (char_at_code input pos4) <> lparen_code
         then FStar_Pervasives_Native.None
         else
           (let pos5 = skip_ws input (pos4 + Prims.int_one) in
            match parse_fs_iri prefixes input pos5 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (iri, pos6) ->
                let pos7 = skip_ws input pos6 in
                if (char_at_code input pos7) <> rparen_code
                then FStar_Pervasives_Native.None
                else
                  (let pos8 = skip_ws input (pos7 + Prims.int_one) in
                   if (char_at_code input pos8) <> rparen_code
                   then FStar_Pervasives_Native.None
                   else
                     FStar_Pervasives_Native.Some
                       ({
                          RDF_Graph_Executable.s =
                            (RDF_Graph_Executable.S_IRI iri);
                          RDF_Graph_Executable.p =
                            RDF_Graph_Executable.rdf_type;
                          RDF_Graph_Executable.o =
                            (RDF_Graph_Executable.T_IRI type_iri)
                        }, (pos8 + Prims.int_one)))))
let parse_unary_type_axiom
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat)
  (type_iri : RDF_Graph_Executable.wf_iri) :
  (RDF_Graph_Executable.triple * Prims.nat) FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_fs_iri prefixes input pos2 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (iri, pos3) ->
         let pos4 = skip_ws input pos3 in
         if (char_at_code input pos4) <> rparen_code
         then FStar_Pervasives_Native.None
         else
           FStar_Pervasives_Native.Some
             ({
                RDF_Graph_Executable.s = (RDF_Graph_Executable.S_IRI iri);
                RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type;
                RDF_Graph_Executable.o =
                  (RDF_Graph_Executable.T_IRI type_iri)
              }, (pos4 + Prims.int_one)))
let parse_data_property_range
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Graph_Executable.triple * Prims.nat) FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_fs_iri prefixes input pos2 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (prop, pos3) ->
         let pos4 = skip_ws input pos3 in
         (match parse_fs_iri prefixes input pos4 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (dt, pos5) ->
              let pos6 = skip_ws input pos5 in
              if (char_at_code input pos6) <> rparen_code
              then FStar_Pervasives_Native.None
              else
                FStar_Pervasives_Native.Some
                  ({
                     RDF_Graph_Executable.s =
                       (RDF_Graph_Executable.S_IRI prop);
                     RDF_Graph_Executable.p = RDF_Graph_Executable.rdfs_range;
                     RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI dt)
                   }, (pos6 + Prims.int_one))))
let parse_data_property_assertion
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Graph_Executable.triple * Prims.nat) FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_fs_iri prefixes input pos2 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (prop, pos3) ->
         let pos4 = skip_ws input pos3 in
         (match parse_fs_iri prefixes input pos4 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ind, pos5) ->
              let pos6 = skip_ws input pos5 in
              (match parse_fs_literal prefixes input pos6 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (lit, pos7) ->
                   let pos8 = skip_ws input pos7 in
                   if (char_at_code input pos8) <> rparen_code
                   then FStar_Pervasives_Native.None
                   else
                     FStar_Pervasives_Native.Some
                       ({
                          RDF_Graph_Executable.s =
                            (RDF_Graph_Executable.S_IRI ind);
                          RDF_Graph_Executable.p = prop;
                          RDF_Graph_Executable.o =
                            (RDF_Graph_Executable.T_Literal lit)
                        }, (pos8 + Prims.int_one)))))
let parse_class_assertion
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match try_match_word input pos2 "DataHasValue" with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some pos3 ->
         let pos4 = skip_ws input pos3 in
         if (char_at_code input pos4) <> lparen_code
         then FStar_Pervasives_Native.None
         else
           (let pos5 = skip_ws input (pos4 + Prims.int_one) in
            match parse_fs_iri prefixes input pos5 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (prop, pos6) ->
                let pos7 = skip_ws input pos6 in
                (match parse_fs_literal prefixes input pos7 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (lit, pos8) ->
                     let pos9 = skip_ws input pos8 in
                     if (char_at_code input pos9) <> rparen_code
                     then FStar_Pervasives_Native.None
                     else
                       (let pos10 = skip_ws input (pos9 + Prims.int_one) in
                        match parse_fs_iri prefixes input pos10 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (ind, pos11) ->
                            let pos12 = skip_ws input pos11 in
                            if (char_at_code input pos12) <> rparen_code
                            then FStar_Pervasives_Native.None
                            else
                              (let bnode_label =
                                 FStar_String.concat ""
                                   ["owlfs_restr"; Prims.string_of_int bc] in
                               let restr =
                                 RDF_Graph_Executable.S_BNode bnode_label in
                               let t1 =
                                 {
                                   RDF_Graph_Executable.s = restr;
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.rdf_type;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_IRI
                                        RDF_Graph_Executable.owl_Restriction_iri)
                                 } in
                               let t2 =
                                 {
                                   RDF_Graph_Executable.s = restr;
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.owl_onProperty_iri;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_IRI prop)
                                 } in
                               let t3 =
                                 {
                                   RDF_Graph_Executable.s = restr;
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.owl_hasValue_iri;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_Literal lit)
                                 } in
                               let t4 =
                                 {
                                   RDF_Graph_Executable.s =
                                     (RDF_Graph_Executable.S_IRI ind);
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.rdf_type;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_BNode
                                        bnode_label)
                                 } in
                               FStar_Pervasives_Native.Some
                                 ([t1; t2; t3; t4], (pos12 + Prims.int_one),
                                   (bc + Prims.int_one)))))))
let parse_sub_object_property_of
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match try_match_word input pos2 "ObjectPropertyChain" with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some pos3 ->
         let pos4 = skip_ws input pos3 in
         if (char_at_code input pos4) <> lparen_code
         then FStar_Pervasives_Native.None
         else
           (let pos5 = skip_ws input (pos4 + Prims.int_one) in
            match parse_fs_iri prefixes input pos5 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (p1, pos6) ->
                let pos7 = skip_ws input pos6 in
                (match parse_fs_iri prefixes input pos7 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (p2, pos8) ->
                     let pos9 = skip_ws input pos8 in
                     if (char_at_code input pos9) <> rparen_code
                     then FStar_Pervasives_Native.None
                     else
                       (let pos10 = skip_ws input (pos9 + Prims.int_one) in
                        match parse_fs_iri prefixes input pos10 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (q, pos11) ->
                            let pos12 = skip_ws input pos11 in
                            if (char_at_code input pos12) <> rparen_code
                            then FStar_Pervasives_Native.None
                            else
                              (let b1 =
                                 FStar_String.concat ""
                                   ["owlfs_chain"; Prims.string_of_int bc] in
                               let b2 =
                                 FStar_String.concat ""
                                   ["owlfs_chain";
                                   Prims.string_of_int (bc + Prims.int_one)] in
                               let t1 =
                                 {
                                   RDF_Graph_Executable.s =
                                     (RDF_Graph_Executable.S_BNode b1);
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.rdf_first;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_IRI p1)
                                 } in
                               let t2 =
                                 {
                                   RDF_Graph_Executable.s =
                                     (RDF_Graph_Executable.S_BNode b1);
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.rdf_rest;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_BNode b2)
                                 } in
                               let t3 =
                                 {
                                   RDF_Graph_Executable.s =
                                     (RDF_Graph_Executable.S_BNode b2);
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.rdf_first;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_IRI p2)
                                 } in
                               let t4 =
                                 {
                                   RDF_Graph_Executable.s =
                                     (RDF_Graph_Executable.S_BNode b2);
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.rdf_rest;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_IRI
                                        RDF_Graph_Executable.rdf_nil_iri)
                                 } in
                               let t5 =
                                 {
                                   RDF_Graph_Executable.s =
                                     (RDF_Graph_Executable.S_IRI q);
                                   RDF_Graph_Executable.p =
                                     RDF_Graph_Executable.owl_propertyChainAxiom;
                                   RDF_Graph_Executable.o =
                                     (RDF_Graph_Executable.T_BNode b1)
                                 } in
                               FStar_Pervasives_Native.Some
                                 ([t1; t2; t3; t4; t5],
                                   (pos12 + Prims.int_one),
                                   (bc + (Prims.of_int (2)))))))))
let rec parse_axioms_acc
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel1 = fuel - Prims.int_one in
     let pos0 = skip_ws input pos in
     if (char_at_code input pos0) = rparen_code
     then
       FStar_Pervasives_Native.Some ((FStar_List_Tot_Base.rev acc), pos0, bc)
     else
       (match try_match_word input pos0 "Declaration" with
        | FStar_Pervasives_Native.Some pos1 ->
            (match parse_declaration prefixes input pos1 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (t, pos2) ->
                 parse_axioms_acc prefixes input pos2 bc (t :: acc) fuel1)
        | FStar_Pervasives_Native.None ->
            (match try_match_word input pos0 "TransitiveObjectProperty" with
             | FStar_Pervasives_Native.Some pos1 ->
                 (match parse_unary_type_axiom prefixes input pos1
                          RDF_Graph_Executable.owl_TransitiveProperty
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (t, pos2) ->
                      parse_axioms_acc prefixes input pos2 bc (t :: acc)
                        fuel1)
             | FStar_Pervasives_Native.None ->
                 (match try_match_word input pos0 "FunctionalDataProperty"
                  with
                  | FStar_Pervasives_Native.Some pos1 ->
                      (match parse_unary_type_axiom prefixes input pos1
                               RDF_Graph_Executable.owl_FunctionalProperty
                       with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some (t, pos2) ->
                           parse_axioms_acc prefixes input pos2 bc (t :: acc)
                             fuel1)
                  | FStar_Pervasives_Native.None ->
                      (match try_match_word input pos0 "DataPropertyRange"
                       with
                       | FStar_Pervasives_Native.Some pos1 ->
                           (match parse_data_property_range prefixes input
                                    pos1
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (t, pos2) ->
                                parse_axioms_acc prefixes input pos2 bc (t ::
                                  acc) fuel1)
                       | FStar_Pervasives_Native.None ->
                           (match try_match_word input pos0
                                    "DataPropertyAssertion"
                            with
                            | FStar_Pervasives_Native.Some pos1 ->
                                (match parse_data_property_assertion prefixes
                                         input pos1
                                 with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some (t, pos2) ->
                                     parse_axioms_acc prefixes input pos2 bc
                                       (t :: acc) fuel1)
                            | FStar_Pervasives_Native.None ->
                                (match try_match_word input pos0
                                         "ClassAssertion"
                                 with
                                 | FStar_Pervasives_Native.Some pos1 ->
                                     (match parse_class_assertion prefixes
                                              input pos1 bc
                                      with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          (ts, pos2, bc') ->
                                          parse_axioms_acc prefixes input
                                            pos2 bc'
                                            (FStar_List_Tot_Base.rev_acc ts
                                               acc) fuel1)
                                 | FStar_Pervasives_Native.None ->
                                     (match try_match_word input pos0
                                              "SubObjectPropertyOf"
                                      with
                                      | FStar_Pervasives_Native.Some pos1 ->
                                          (match parse_sub_object_property_of
                                                   prefixes input pos1 bc
                                           with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some
                                               (ts, pos2, bc') ->
                                               parse_axioms_acc prefixes
                                                 input pos2 bc'
                                                 (FStar_List_Tot_Base.rev_acc
                                                    ts acc) fuel1)
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None))))))))
let parse_functional_syntax (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  match parse_prefixes_acc input Prims.int_zero [] (len + Prims.int_one) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (prefixes, pos_after_prefixes) ->
      let pos1 = skip_ws input pos_after_prefixes in
      (match try_match_word input pos1 "Ontology" with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some pos2 ->
           let pos3 = skip_ws input pos2 in
           if (char_at_code input pos3) <> lparen_code
           then FStar_Pervasives_Native.None
           else
             (let pos4 = skip_ws input (pos3 + Prims.int_one) in
              match parse_axioms_acc prefixes input pos4 Prims.int_zero []
                      (len + Prims.int_one)
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (triples, pos5, _bc) ->
                  if (char_at_code input pos5) = rparen_code
                  then FStar_Pervasives_Native.Some triples
                  else FStar_Pervasives_Native.None))
