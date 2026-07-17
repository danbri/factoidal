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
  (RDF_Term.wf_iri * Prims.nat) FStar_Pervasives_Native.option=
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
                  if RDF_Term.is_iri full
                  then FStar_Pervasives_Native.Some (full, pos3)
                  else FStar_Pervasives_Native.None))
let parse_fs_iri (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Term.wf_iri * Prims.nat) FStar_Pervasives_Native.option=
  if (char_at_code input pos) = langle_code
  then
    match scan_angle_iri input (pos + Prims.int_one)
            ((Parser_FastString.fs_byte_length input) - pos)
    with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (s, pos') ->
        (if RDF_Term.is_iri s
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
  (RDF_Term.wf_literal * Prims.nat) FStar_Pervasives_Native.option=
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
                      RDF_Term.lexical_form = lexical;
                      RDF_Term.datatype = dt;
                      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                      RDF_Term.direction = FStar_Pervasives_Native.None
                    } in
                  (if RDF_Term.literal_wf lit
                   then FStar_Pervasives_Native.Some (lit, pos2)
                   else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None))
let owl_onDatatype_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onDatatype"
let owl_withRestrictions_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#withRestrictions"
let owl_datatypeComplementOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#datatypeComplementOf"
let owl_NegativePropertyAssertion_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#NegativePropertyAssertion"
let term_to_subject (t : RDF_Term.rdf_term) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | RDF_Term.T_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | RDF_Term.T_Literal uu___ -> FStar_Pervasives_Native.None
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
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
  (RDF_Triple.triple * Prims.nat) FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     let entity_kind =
       match try_match_word input pos2 "ObjectProperty" with
       | FStar_Pervasives_Native.Some p ->
           FStar_Pervasives_Native.Some (p, RDFS_Closure.owl_ObjectProperty)
       | FStar_Pervasives_Native.None ->
           (match try_match_word input pos2 "DataProperty" with
            | FStar_Pervasives_Native.Some p ->
                FStar_Pervasives_Native.Some
                  (p, RDFS_Closure.owl_DatatypeProperty)
            | FStar_Pervasives_Native.None ->
                (match try_match_word input pos2 "NamedIndividual" with
                 | FStar_Pervasives_Native.Some p ->
                     FStar_Pervasives_Native.Some
                       (p, RDFS_Closure.owl_NamedIndividual)
                 | FStar_Pervasives_Native.None ->
                     (match try_match_word input pos2 "Class" with
                      | FStar_Pervasives_Native.Some p ->
                          FStar_Pervasives_Native.Some
                            (p, RDFS_Closure.owl_Class)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None))) in
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
                          RDF_Triple.s = (RDF_Term.S_IRI iri);
                          RDF_Triple.p = RDFS_Closure.rdf_type;
                          RDF_Triple.o = (RDF_Term.T_IRI type_iri)
                        }, (pos8 + Prims.int_one)))))
let parse_unary_type_axiom
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (type_iri : RDF_Term.wf_iri) :
  (RDF_Triple.triple * Prims.nat) FStar_Pervasives_Native.option=
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
                RDF_Triple.s = (RDF_Term.S_IRI iri);
                RDF_Triple.p = RDFS_Closure.rdf_type;
                RDF_Triple.o = (RDF_Term.T_IRI type_iri)
              }, (pos4 + Prims.int_one)))
let parse_data_property_range
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Triple.triple * Prims.nat) FStar_Pervasives_Native.option=
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
                     RDF_Triple.s = (RDF_Term.S_IRI prop);
                     RDF_Triple.p = RDFS_Closure.rdfs_range;
                     RDF_Triple.o = (RDF_Term.T_IRI dt)
                   }, (pos6 + Prims.int_one))))
let parse_data_property_assertion
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Triple.triple * Prims.nat) FStar_Pervasives_Native.option=
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
                          RDF_Triple.s = (RDF_Term.S_IRI ind);
                          RDF_Triple.p = prop;
                          RDF_Triple.o = (RDF_Term.T_Literal lit)
                        }, (pos8 + Prims.int_one)))))
let rec parse_literal_list_acc
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Term.wf_literal Prims.list) (fuel : Prims.nat) :
  (RDF_Term.wf_literal Prims.list * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel1 = fuel - Prims.int_one in
     let pos0 = skip_ws input pos in
     if (char_at_code input pos0) = rparen_code
     then
       (if (FStar_List_Tot_Base.length acc) = Prims.int_zero
        then FStar_Pervasives_Native.None
        else
          FStar_Pervasives_Native.Some ((FStar_List_Tot_Base.rev acc), pos0))
     else
       (match parse_fs_literal prefixes input pos0 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (lit, pos1) ->
            parse_literal_list_acc prefixes input pos1 (lit :: acc) fuel1))
let rec build_literal_list (lits : RDF_Term.wf_literal Prims.list)
  (bc : Prims.nat) :
  (RDF_Triple.triple Prims.list * RDF_Term.rdf_term * Prims.nat)=
  match lits with
  | [] -> ([], (RDF_Term.T_IRI OWL_Closure.rdf_nil_iri), bc)
  | l::rest ->
      let uu___ = build_literal_list rest bc in
      (match uu___ with
       | (rest_triples, rest_term, bc1) ->
           let node_label =
             FStar_String.concat "" ["owlfs_lst"; Prims.string_of_int bc1] in
           let t_first =
             {
               RDF_Triple.s = (RDF_Term.S_BNode node_label);
               RDF_Triple.p = OWL_Closure.rdf_first;
               RDF_Triple.o = (RDF_Term.T_Literal l)
             } in
           let t_rest =
             {
               RDF_Triple.s = (RDF_Term.S_BNode node_label);
               RDF_Triple.p = OWL_Closure.rdf_rest;
               RDF_Triple.o = rest_term
             } in
           ((t_first :: t_rest :: rest_triples),
             (RDF_Term.T_BNode node_label), (bc1 + Prims.int_one)))
let rec parse_facet_list_acc
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat)
  (acc : (RDF_Term.wf_iri * RDF_Term.wf_literal) Prims.list)
  (fuel : Prims.nat) :
  ((RDF_Term.wf_iri * RDF_Term.wf_literal) Prims.list * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel1 = fuel - Prims.int_one in
     let pos0 = skip_ws input pos in
     if (char_at_code input pos0) = rparen_code
     then
       (if (FStar_List_Tot_Base.length acc) = Prims.int_zero
        then FStar_Pervasives_Native.None
        else
          FStar_Pervasives_Native.Some ((FStar_List_Tot_Base.rev acc), pos0))
     else
       (match parse_fs_iri prefixes input pos0 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (facet, pos1) ->
            let pos2 = skip_ws input pos1 in
            (match parse_fs_literal prefixes input pos2 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (lit, pos3) ->
                 parse_facet_list_acc prefixes input pos3 ((facet, lit) ::
                   acc) fuel1)))
let rec build_facet_list
  (facets : (RDF_Term.wf_iri * RDF_Term.wf_literal) Prims.list)
  (bc : Prims.nat) :
  (RDF_Triple.triple Prims.list * RDF_Term.rdf_term * Prims.nat)=
  match facets with
  | [] -> ([], (RDF_Term.T_IRI OWL_Closure.rdf_nil_iri), bc)
  | (facet, lit)::rest ->
      let uu___ = build_facet_list rest bc in
      (match uu___ with
       | (rest_triples, rest_term, bc1) ->
           let fnode_label =
             FStar_String.concat "" ["owlfs_facet"; Prims.string_of_int bc1] in
           let vnode_label =
             FStar_String.concat ""
               ["owlfs_flst"; Prims.string_of_int (bc1 + Prims.int_one)] in
           let t_val =
             {
               RDF_Triple.s = (RDF_Term.S_BNode fnode_label);
               RDF_Triple.p = facet;
               RDF_Triple.o = (RDF_Term.T_Literal lit)
             } in
           let t_first =
             {
               RDF_Triple.s = (RDF_Term.S_BNode vnode_label);
               RDF_Triple.p = OWL_Closure.rdf_first;
               RDF_Triple.o = (RDF_Term.T_BNode fnode_label)
             } in
           let t_rest =
             {
               RDF_Triple.s = (RDF_Term.S_BNode vnode_label);
               RDF_Triple.p = OWL_Closure.rdf_rest;
               RDF_Triple.o = rest_term
             } in
           ((t_val :: t_first :: t_rest :: rest_triples),
             (RDF_Term.T_BNode vnode_label), (bc1 + (Prims.of_int (2)))))
let parse_data_has_value_expr
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_fs_iri prefixes input pos2 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (prop, pos3) ->
         let pos4 = skip_ws input pos3 in
         (match parse_fs_literal prefixes input pos4 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (lit, pos5) ->
              let pos6 = skip_ws input pos5 in
              if (char_at_code input pos6) <> rparen_code
              then FStar_Pervasives_Native.None
              else
                (let bnode_label =
                   FStar_String.concat ""
                     ["owlfs_restr"; Prims.string_of_int bc] in
                 let restr = RDF_Term.S_BNode bnode_label in
                 let t1 =
                   {
                     RDF_Triple.s = restr;
                     RDF_Triple.p = RDFS_Closure.rdf_type;
                     RDF_Triple.o =
                       (RDF_Term.T_IRI OWL_Closure.owl_Restriction_iri)
                   } in
                 let t2 =
                   {
                     RDF_Triple.s = restr;
                     RDF_Triple.p = OWL_Closure.owl_onProperty_iri;
                     RDF_Triple.o = (RDF_Term.T_IRI prop)
                   } in
                 let t3 =
                   {
                     RDF_Triple.s = restr;
                     RDF_Triple.p = OWL_Closure.owl_hasValue_iri;
                     RDF_Triple.o = (RDF_Term.T_Literal lit)
                   } in
                 FStar_Pervasives_Native.Some
                   ((RDF_Term.T_BNode bnode_label), [t1; t2; t3],
                     (pos6 + Prims.int_one), (bc + Prims.int_one)))))
let parse_data_one_of (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_literal_list_acc prefixes input pos2 []
             ((Parser_FastString.fs_byte_length input) + Prims.int_one)
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (lits, pos3) ->
         let pos4 = skip_ws input pos3 in
         if (char_at_code input pos4) <> rparen_code
         then FStar_Pervasives_Native.None
         else
           (let uu___2 = build_literal_list lits bc in
            match uu___2 with
            | (list_triples, list_head, bc1) ->
                let dt_label =
                  FStar_String.concat ""
                    ["owlfs_dtoneof"; Prims.string_of_int bc1] in
                let dt = RDF_Term.S_BNode dt_label in
                let t1 =
                  {
                    RDF_Triple.s = dt;
                    RDF_Triple.p = RDFS_Closure.rdf_type;
                    RDF_Triple.o =
                      (RDF_Term.T_IRI RDFS_Closure.rdfs_Datatype)
                  } in
                let t2 =
                  {
                    RDF_Triple.s = dt;
                    RDF_Triple.p = OWL_Closure.owl_oneOf_iri;
                    RDF_Triple.o = list_head
                  } in
                FStar_Pervasives_Native.Some
                  ((RDF_Term.T_BNode dt_label),
                    (FStar_List_Tot_Base.op_At list_triples [t1; t2]),
                    (pos4 + Prims.int_one), (bc1 + Prims.int_one))))
let parse_datatype_restriction
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_fs_iri prefixes input pos2 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (base_dt, pos3) ->
         (match parse_facet_list_acc prefixes input pos3 []
                  ((Parser_FastString.fs_byte_length input) + Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (facets, pos4) ->
              let pos5 = skip_ws input pos4 in
              if (char_at_code input pos5) <> rparen_code
              then FStar_Pervasives_Native.None
              else
                (let uu___2 = build_facet_list facets bc in
                 match uu___2 with
                 | (facet_triples, facet_head, bc1) ->
                     let dt_label =
                       FStar_String.concat ""
                         ["owlfs_dtrestr"; Prims.string_of_int bc1] in
                     let dt = RDF_Term.S_BNode dt_label in
                     let t1 =
                       {
                         RDF_Triple.s = dt;
                         RDF_Triple.p = RDFS_Closure.rdf_type;
                         RDF_Triple.o =
                           (RDF_Term.T_IRI RDFS_Closure.rdfs_Datatype)
                       } in
                     let t2 =
                       {
                         RDF_Triple.s = dt;
                         RDF_Triple.p = owl_onDatatype_iri;
                         RDF_Triple.o = (RDF_Term.T_IRI base_dt)
                       } in
                     let t3 =
                       {
                         RDF_Triple.s = dt;
                         RDF_Triple.p = owl_withRestrictions_iri;
                         RDF_Triple.o = facet_head
                       } in
                     FStar_Pervasives_Native.Some
                       ((RDF_Term.T_BNode dt_label),
                         (FStar_List_Tot_Base.op_At facet_triples
                            [t1; t2; t3]), (pos5 + Prims.int_one),
                         (bc1 + Prims.int_one)))))
let rec parse_class_expr
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel1 = fuel - Prims.int_one in
     let pos0 = skip_ws input pos in
     match parse_fs_iri prefixes input pos0 with
     | FStar_Pervasives_Native.Some (iri, pos1) ->
         FStar_Pervasives_Native.Some ((RDF_Term.T_IRI iri), [], pos1, bc)
     | FStar_Pervasives_Native.None ->
         (match try_match_word input pos0 "DataHasValue" with
          | FStar_Pervasives_Native.Some pos1 ->
              parse_data_has_value_expr prefixes input pos1 bc
          | FStar_Pervasives_Native.None ->
              (match try_match_word input pos0 "DataSomeValuesFrom" with
               | FStar_Pervasives_Native.Some pos1 ->
                   parse_data_values_from prefixes input pos1 bc fuel1
                     OWL_Closure.owl_someValuesFrom_iri
               | FStar_Pervasives_Native.None ->
                   (match try_match_word input pos0 "DataAllValuesFrom" with
                    | FStar_Pervasives_Native.Some pos1 ->
                        parse_data_values_from prefixes input pos1 bc fuel1
                          OWL_Closure.owl_allValuesFrom_iri
                    | FStar_Pervasives_Native.None ->
                        (match try_match_word input pos0 "ObjectComplementOf"
                         with
                         | FStar_Pervasives_Native.Some pos1 ->
                             parse_object_complement_of prefixes input pos1
                               bc fuel1
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None)))))
and parse_data_values_from
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat)
  (fuel : Prims.nat) (rel_iri : RDF_Term.wf_iri) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let pos1 = skip_ws input pos in
     if (char_at_code input pos1) <> lparen_code
     then FStar_Pervasives_Native.None
     else
       (let pos2 = skip_ws input (pos1 + Prims.int_one) in
        match parse_fs_iri prefixes input pos2 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (prop, pos3) ->
            let pos4 = skip_ws input pos3 in
            (match parse_data_range prefixes input pos4 bc
                     (fuel - Prims.int_one)
             with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (dr_term, dr_triples, pos5, bc1)
                 ->
                 let pos6 = skip_ws input pos5 in
                 if (char_at_code input pos6) <> rparen_code
                 then FStar_Pervasives_Native.None
                 else
                   (let bnode_label =
                      FStar_String.concat ""
                        ["owlfs_restr"; Prims.string_of_int bc1] in
                    let restr = RDF_Term.S_BNode bnode_label in
                    let t1 =
                      {
                        RDF_Triple.s = restr;
                        RDF_Triple.p = RDFS_Closure.rdf_type;
                        RDF_Triple.o =
                          (RDF_Term.T_IRI OWL_Closure.owl_Restriction_iri)
                      } in
                    let t2 =
                      {
                        RDF_Triple.s = restr;
                        RDF_Triple.p = OWL_Closure.owl_onProperty_iri;
                        RDF_Triple.o = (RDF_Term.T_IRI prop)
                      } in
                    let t3 =
                      {
                        RDF_Triple.s = restr;
                        RDF_Triple.p = rel_iri;
                        RDF_Triple.o = dr_term
                      } in
                    FStar_Pervasives_Native.Some
                      ((RDF_Term.T_BNode bnode_label),
                        (FStar_List_Tot_Base.op_At dr_triples [t1; t2; t3]),
                        (pos6 + Prims.int_one), (bc1 + Prims.int_one))))))
and parse_object_complement_of
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let pos1 = skip_ws input pos in
     if (char_at_code input pos1) <> lparen_code
     then FStar_Pervasives_Native.None
     else
       (let pos2 = skip_ws input (pos1 + Prims.int_one) in
        match parse_class_expr prefixes input pos2 bc (fuel - Prims.int_one)
        with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (ce_term, ce_triples, pos3, bc1) ->
            let pos4 = skip_ws input pos3 in
            if (char_at_code input pos4) <> rparen_code
            then FStar_Pervasives_Native.None
            else
              (let bnode_label =
                 FStar_String.concat ""
                   ["owlfs_comp"; Prims.string_of_int bc1] in
               let comp = RDF_Term.S_BNode bnode_label in
               let t1 =
                 {
                   RDF_Triple.s = comp;
                   RDF_Triple.p = RDFS_Closure.rdf_type;
                   RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
                 } in
               let t2 =
                 {
                   RDF_Triple.s = comp;
                   RDF_Triple.p = OWL_Closure.owl_complementOf_iri;
                   RDF_Triple.o = ce_term
                 } in
               FStar_Pervasives_Native.Some
                 ((RDF_Term.T_BNode bnode_label),
                   (FStar_List_Tot_Base.op_At ce_triples [t1; t2]),
                   (pos4 + Prims.int_one), (bc1 + Prims.int_one)))))
and parse_data_range (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel1 = fuel - Prims.int_one in
     let pos0 = skip_ws input pos in
     match parse_fs_iri prefixes input pos0 with
     | FStar_Pervasives_Native.Some (iri, pos1) ->
         FStar_Pervasives_Native.Some ((RDF_Term.T_IRI iri), [], pos1, bc)
     | FStar_Pervasives_Native.None ->
         (match try_match_word input pos0 "DataOneOf" with
          | FStar_Pervasives_Native.Some pos1 ->
              parse_data_one_of prefixes input pos1 bc
          | FStar_Pervasives_Native.None ->
              (match try_match_word input pos0 "DataComplementOf" with
               | FStar_Pervasives_Native.Some pos1 ->
                   parse_data_complement_of prefixes input pos1 bc fuel1
               | FStar_Pervasives_Native.None ->
                   (match try_match_word input pos0 "DatatypeRestriction"
                    with
                    | FStar_Pervasives_Native.Some pos1 ->
                        parse_datatype_restriction prefixes input pos1 bc
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None))))
and parse_data_complement_of
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let pos1 = skip_ws input pos in
     if (char_at_code input pos1) <> lparen_code
     then FStar_Pervasives_Native.None
     else
       (let pos2 = skip_ws input (pos1 + Prims.int_one) in
        match parse_data_range prefixes input pos2 bc (fuel - Prims.int_one)
        with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (dr_term, dr_triples, pos3, bc1) ->
            let pos4 = skip_ws input pos3 in
            if (char_at_code input pos4) <> rparen_code
            then FStar_Pervasives_Native.None
            else
              (let dt_label =
                 FStar_String.concat ""
                   ["owlfs_dtcomp"; Prims.string_of_int bc1] in
               let dt = RDF_Term.S_BNode dt_label in
               let t1 =
                 {
                   RDF_Triple.s = dt;
                   RDF_Triple.p = RDFS_Closure.rdf_type;
                   RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.rdfs_Datatype)
                 } in
               let t2 =
                 {
                   RDF_Triple.s = dt;
                   RDF_Triple.p = owl_datatypeComplementOf_iri;
                   RDF_Triple.o = dr_term
                 } in
               FStar_Pervasives_Native.Some
                 ((RDF_Term.T_BNode dt_label),
                   (FStar_List_Tot_Base.op_At dr_triples [t1; t2]),
                   (pos4 + Prims.int_one), (bc1 + Prims.int_one)))))
let parse_subclass_of (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     let fuel = (Parser_FastString.fs_byte_length input) + Prims.int_one in
     match parse_class_expr prefixes input pos2 bc fuel with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (ce1_term, ce1_triples, pos3, bc1) ->
         let pos4 = skip_ws input pos3 in
         (match parse_class_expr prefixes input pos4 bc1 fuel with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ce2_term, ce2_triples, pos5, bc2)
              ->
              let pos6 = skip_ws input pos5 in
              if (char_at_code input pos6) <> rparen_code
              then FStar_Pervasives_Native.None
              else
                (match term_to_subject ce1_term with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some ce1_subj ->
                     let t_sco =
                       {
                         RDF_Triple.s = ce1_subj;
                         RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                         RDF_Triple.o = ce2_term
                       } in
                     FStar_Pervasives_Native.Some
                       ((FStar_List_Tot_Base.op_At ce1_triples
                           (FStar_List_Tot_Base.op_At ce2_triples [t_sco])),
                         (pos6 + Prims.int_one), bc2))))
let parse_class_assertion
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_class_expr prefixes input pos2 bc
             ((Parser_FastString.fs_byte_length input) + Prims.int_one)
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (ce_term, ce_triples, pos3, bc1) ->
         let pos4 = skip_ws input pos3 in
         (match parse_fs_iri prefixes input pos4 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ind, pos5) ->
              let pos6 = skip_ws input pos5 in
              if (char_at_code input pos6) <> rparen_code
              then FStar_Pervasives_Native.None
              else
                (let t_assert =
                   {
                     RDF_Triple.s = (RDF_Term.S_IRI ind);
                     RDF_Triple.p = RDFS_Closure.rdf_type;
                     RDF_Triple.o = ce_term
                   } in
                 FStar_Pervasives_Native.Some
                   ((FStar_List_Tot_Base.op_At ce_triples [t_assert]),
                     (pos6 + Prims.int_one), bc1))))
let parse_disjoint_data_properties
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Triple.triple * Prims.nat) FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  if (char_at_code input pos1) <> lparen_code
  then FStar_Pervasives_Native.None
  else
    (let pos2 = skip_ws input (pos1 + Prims.int_one) in
     match parse_fs_iri prefixes input pos2 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (p1, pos3) ->
         let pos4 = skip_ws input pos3 in
         (match parse_fs_iri prefixes input pos4 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (p2, pos5) ->
              let pos6 = skip_ws input pos5 in
              if (char_at_code input pos6) <> rparen_code
              then FStar_Pervasives_Native.None
              else
                FStar_Pervasives_Native.Some
                  ({
                     RDF_Triple.s = (RDF_Term.S_IRI p1);
                     RDF_Triple.p = OWL_Closure.owl_propertyDisjointWith;
                     RDF_Triple.o = (RDF_Term.T_IRI p2)
                   }, (pos6 + Prims.int_one))))
let parse_negative_data_property_assertion
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
    FStar_Pervasives_Native.option=
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
                     (let bnode_label =
                        FStar_String.concat ""
                          ["owlfs_npa"; Prims.string_of_int bc] in
                      let npa = RDF_Term.S_BNode bnode_label in
                      let t1 =
                        {
                          RDF_Triple.s = npa;
                          RDF_Triple.p = RDFS_Closure.rdf_type;
                          RDF_Triple.o =
                            (RDF_Term.T_IRI owl_NegativePropertyAssertion_iri)
                        } in
                      let t2 =
                        {
                          RDF_Triple.s = npa;
                          RDF_Triple.p = OWL_Closure.owl_sourceIndividual;
                          RDF_Triple.o = (RDF_Term.T_IRI ind)
                        } in
                      let t3 =
                        {
                          RDF_Triple.s = npa;
                          RDF_Triple.p = OWL_Closure.owl_assertionProperty;
                          RDF_Triple.o = (RDF_Term.T_IRI prop)
                        } in
                      let t4 =
                        {
                          RDF_Triple.s = npa;
                          RDF_Triple.p = OWL_Closure.owl_targetValue;
                          RDF_Triple.o = (RDF_Term.T_Literal lit)
                        } in
                      FStar_Pervasives_Native.Some
                        ([t1; t2; t3; t4], (pos8 + Prims.int_one),
                          (bc + Prims.int_one))))))
let parse_sub_object_property_of
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat) :
  (RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
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
                                   RDF_Triple.s = (RDF_Term.S_BNode b1);
                                   RDF_Triple.p = OWL_Closure.rdf_first;
                                   RDF_Triple.o = (RDF_Term.T_IRI p1)
                                 } in
                               let t2 =
                                 {
                                   RDF_Triple.s = (RDF_Term.S_BNode b1);
                                   RDF_Triple.p = OWL_Closure.rdf_rest;
                                   RDF_Triple.o = (RDF_Term.T_BNode b2)
                                 } in
                               let t3 =
                                 {
                                   RDF_Triple.s = (RDF_Term.S_BNode b2);
                                   RDF_Triple.p = OWL_Closure.rdf_first;
                                   RDF_Triple.o = (RDF_Term.T_IRI p2)
                                 } in
                               let t4 =
                                 {
                                   RDF_Triple.s = (RDF_Term.S_BNode b2);
                                   RDF_Triple.p = OWL_Closure.rdf_rest;
                                   RDF_Triple.o =
                                     (RDF_Term.T_IRI OWL_Closure.rdf_nil_iri)
                                 } in
                               let t5 =
                                 {
                                   RDF_Triple.s = (RDF_Term.S_IRI q);
                                   RDF_Triple.p =
                                     OWL_Closure.owl_propertyChainAxiom;
                                   RDF_Triple.o = (RDF_Term.T_BNode b1)
                                 } in
                               FStar_Pervasives_Native.Some
                                 ([t1; t2; t3; t4; t5],
                                   (pos12 + Prims.int_one),
                                   (bc + (Prims.of_int (2)))))))))
let rec parse_axioms_acc
  (prefixes : (Prims.string * Prims.string) Prims.list)
  (input : Prims.string) (pos : Prims.nat) (bc : Prims.nat)
  (acc : RDF_Triple.triple Prims.list) (fuel : Prims.nat) :
  (RDF_Triple.triple Prims.list * Prims.nat * Prims.nat)
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
                          OWL_Closure.owl_TransitiveProperty
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
                               OWL_Closure.owl_FunctionalProperty
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
                                          (match try_match_word input pos0
                                                   "SubClassOf"
                                           with
                                           | FStar_Pervasives_Native.Some
                                               pos1 ->
                                               (match parse_subclass_of
                                                        prefixes input pos1
                                                        bc
                                                with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    (ts, pos2, bc') ->
                                                    parse_axioms_acc prefixes
                                                      input pos2 bc'
                                                      (FStar_List_Tot_Base.rev_acc
                                                         ts acc) fuel1)
                                           | FStar_Pervasives_Native.None ->
                                               (match try_match_word input
                                                        pos0
                                                        "DisjointDataProperties"
                                                with
                                                | FStar_Pervasives_Native.Some
                                                    pos1 ->
                                                    (match parse_disjoint_data_properties
                                                             prefixes input
                                                             pos1
                                                     with
                                                     | FStar_Pervasives_Native.None
                                                         ->
                                                         FStar_Pervasives_Native.None
                                                     | FStar_Pervasives_Native.Some
                                                         (t, pos2) ->
                                                         parse_axioms_acc
                                                           prefixes input
                                                           pos2 bc (t :: acc)
                                                           fuel1)
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    (match try_match_word
                                                             input pos0
                                                             "NegativeDataPropertyAssertion"
                                                     with
                                                     | FStar_Pervasives_Native.Some
                                                         pos1 ->
                                                         (match parse_negative_data_property_assertion
                                                                  prefixes
                                                                  input pos1
                                                                  bc
                                                          with
                                                          | FStar_Pervasives_Native.None
                                                              ->
                                                              FStar_Pervasives_Native.None
                                                          | FStar_Pervasives_Native.Some
                                                              (ts, pos2, bc')
                                                              ->
                                                              parse_axioms_acc
                                                                prefixes
                                                                input pos2
                                                                bc'
                                                                (FStar_List_Tot_Base.rev_acc
                                                                   ts acc)
                                                                fuel1)
                                                     | FStar_Pervasives_Native.None
                                                         ->
                                                         FStar_Pervasives_Native.None)))))))))))
let parse_functional_syntax (input : Prims.string) :
  RDF_Triple.triple Prims.list FStar_Pervasives_Native.option=
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
