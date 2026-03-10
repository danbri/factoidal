open Prims
let rec trig_find_named_graph (name : RDF_Graph_Executable.iri)
  (ngs : RDF_Graph_Executable.named_graph Prims.list) :
  (RDF_Graph_Executable.named_graph Prims.list *
    RDF_Graph_Executable.rdf_graph * RDF_Graph_Executable.named_graph
    Prims.list) FStar_Pervasives_Native.option=
  match ngs with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.RDF_Graph_Executable.ng_name = name
      then
        FStar_Pervasives_Native.Some
          ([], (ng.RDF_Graph_Executable.ng_graph), rest)
      else
        (match trig_find_named_graph name rest with
         | FStar_Pervasives_Native.Some (before, g, after) ->
             FStar_Pervasives_Native.Some ((ng :: before), g, after)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let trig_dataset_add (ds : RDF_Graph_Executable.rdf_dataset)
  (t : RDF_Graph_Executable.triple)
  (graph_name : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_dataset=
  match graph_name with
  | FStar_Pervasives_Native.None ->
      {
        RDF_Graph_Executable.ds_default =
          (RDF_Graph_Executable.graph_add t
             ds.RDF_Graph_Executable.ds_default);
        RDF_Graph_Executable.ds_named = (ds.RDF_Graph_Executable.ds_named)
      }
  | FStar_Pervasives_Native.Some name ->
      (match trig_find_named_graph name ds.RDF_Graph_Executable.ds_named with
       | FStar_Pervasives_Native.Some (before, existing_g, after) ->
           let updated_g = RDF_Graph_Executable.graph_add t existing_g in
           let updated_ng =
             {
               RDF_Graph_Executable.ng_name = name;
               RDF_Graph_Executable.ng_graph = updated_g
             } in
           {
             RDF_Graph_Executable.ds_default =
               (ds.RDF_Graph_Executable.ds_default);
             RDF_Graph_Executable.ds_named =
               (FStar_List_Tot_Base.append before
                  (FStar_List_Tot_Base.append [updated_ng] after))
           }
       | FStar_Pervasives_Native.None ->
           let new_ng =
             {
               RDF_Graph_Executable.ng_name = name;
               RDF_Graph_Executable.ng_graph = [t]
             } in
           {
             RDF_Graph_Executable.ds_default =
               (ds.RDF_Graph_Executable.ds_default);
             RDF_Graph_Executable.ds_named =
               (FStar_List_Tot_Base.append ds.RDF_Graph_Executable.ds_named
                  [new_ng])
           })
let rec trig_dataset_add_triples (ds : RDF_Graph_Executable.rdf_dataset)
  (triples : RDF_Graph_Executable.triple Prims.list)
  (graph_name : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_dataset=
  match triples with
  | [] -> ds
  | t::rest ->
      trig_dataset_add_triples (trig_dataset_add ds t graph_name) rest
        graph_name
let parse_trig_graph_name (st : Parser_Turtle.turtle_state)
  (input : Prims.string) (pos : Prims.nat) :
  (RDF_Graph_Executable.iri * Parser_Turtle.turtle_state)
    Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected graph name", pos)
  else
    (let c = FStar_String.index input pos in
     let code = FStar_Char.int_of_char c in
     if code = (Prims.of_int (0x5F))
     then
       match Parser_NTriples.parse_bnode input pos with
       | Parser_Combinators.ParseOk (b, pos') ->
           let bnode_iri = FStar_String.concat "" ["_:"; b] in
           Parser_Combinators.ParseOk ((bnode_iri, st), pos')
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
     else
       (match Parser_Turtle.parse_turtle_iri st input pos with
        | Parser_Combinators.ParseOk (i, pos') ->
            Parser_Combinators.ParseOk ((i, st), pos')
        | Parser_Combinators.ParseFail (msg, fpos) ->
            Parser_Combinators.ParseFail (msg, fpos)))
let char_to_lower (c : FStar_Char.char) : FStar_Char.char=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (code + (Prims.of_int (32)))
  else c
let is_graph_keyword (input : Prims.string) (pos : Prims.nat) : Prims.bool=
  let len = FStar_String.strlen input in
  if (pos + (Prims.of_int (5))) > len
  then false
  else
    (let c0 = char_to_lower (FStar_String.index input pos) in
     let c1 = char_to_lower (FStar_String.index input (pos + Prims.int_one)) in
     let c2 =
       char_to_lower (FStar_String.index input (pos + (Prims.of_int (2)))) in
     let c3 =
       char_to_lower (FStar_String.index input (pos + (Prims.of_int (3)))) in
     let c4 =
       char_to_lower (FStar_String.index input (pos + (Prims.of_int (4)))) in
     if
       (((((FStar_Char.int_of_char c0) = (Prims.of_int (0x67))) &&
            ((FStar_Char.int_of_char c1) = (Prims.of_int (0x72))))
           && ((FStar_Char.int_of_char c2) = (Prims.of_int (0x61))))
          && ((FStar_Char.int_of_char c3) = (Prims.of_int (0x70))))
         && ((FStar_Char.int_of_char c4) = (Prims.of_int (0x68)))
     then
       (if (pos + (Prims.of_int (5))) >= len
        then true
        else
          (let next = FStar_String.index input (pos + (Prims.of_int (5))) in
           Prims.op_Negation (Parser_Turtle.is_pn_chars next)))
     else false)
let rec graph_body_skip_line (input : Prims.string) (p : Prims.nat)
  (f : Prims.nat) : Prims.nat=
  if f = Prims.int_zero
  then p
  else
    if p >= (FStar_String.strlen input)
    then p
    else
      (let ch = FStar_String.index input p in
       let cd = FStar_Char.int_of_char ch in
       if (cd = (Prims.of_int (0x0A))) || (cd = (Prims.of_int (0x0D)))
       then p + Prims.int_one
       else
         if cd = (Prims.of_int (0x7D))
         then p
         else
           graph_body_skip_line input (p + Prims.int_one) (f - Prims.int_one))
let rec parse_graph_body (st : Parser_Turtle.turtle_state)
  (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * Parser_Turtle.turtle_state)
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (((FStar_List_Tot_Base.rev acc), st), pos)
  else
    (let fuel' = fuel - Prims.int_one in
     let len = FStar_String.strlen input in
     match Parser_Turtle.turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then
           Parser_Combinators.ParseFail
             ("unterminated graph block, expected '}'", pos1)
         else
           (let c = FStar_String.index input pos1 in
            let code = FStar_Char.int_of_char c in
            if code = (Prims.of_int (0x7D))
            then
              Parser_Combinators.ParseOk
                (((FStar_List_Tot_Base.rev acc), st), (pos1 + Prims.int_one))
            else
              (match Parser_Turtle.parse_turtle_statement st input pos1 fuel
               with
               | Parser_Combinators.ParseOk ((triples, st'), pos2) ->
                   if pos2 = pos1
                   then
                     Parser_Combinators.ParseOk
                       (((FStar_List_Tot_Base.rev
                            (FStar_List_Tot_Base.append
                               (FStar_List_Tot_Base.rev triples) acc)), st'),
                         pos2)
                   else
                     parse_graph_body st' input pos2
                       (FStar_List_Tot_Base.append
                          (FStar_List_Tot_Base.rev triples) acc) fuel'
               | Parser_Combinators.ParseFail (uu___3, uu___4) ->
                   let pos2 = graph_body_skip_line input pos1 (len - pos1) in
                   if pos2 = pos1
                   then
                     Parser_Combinators.ParseOk
                       (((FStar_List_Tot_Base.rev acc), st), pos1)
                   else parse_graph_body st input pos2 acc fuel')))
let parse_trig_statement (st : Parser_Turtle.turtle_state)
  (input : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) :
  ((RDF_Graph_Executable.iri FStar_Pervasives_Native.option *
    RDF_Graph_Executable.triple Prims.list) Prims.list *
    Parser_Turtle.turtle_state) Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit", pos)
  else
    (let fuel' = fuel - Prims.int_one in
     let len = FStar_String.strlen input in
     match Parser_Turtle.turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then Parser_Combinators.ParseOk (([], st), pos1)
         else
           (let c = FStar_String.index input pos1 in
            let code = FStar_Char.int_of_char c in
            match Parser_Turtle.parse_prefix_directive input pos1 with
            | Parser_Combinators.ParseOk ((prefix, iri_val), pos2) ->
                let new_prefixes = (prefix, iri_val) ::
                  (st.Parser_Turtle.prefixes) in
                Parser_Combinators.ParseOk
                  (([],
                     {
                       Parser_Turtle.prefixes = new_prefixes;
                       Parser_Turtle.base_iri = (st.Parser_Turtle.base_iri);
                       Parser_Turtle.bnode_counter =
                         (st.Parser_Turtle.bnode_counter)
                     }), pos2)
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                (match Parser_Turtle.parse_base_directive input pos1 with
                 | Parser_Combinators.ParseOk (base_val, pos2) ->
                     Parser_Combinators.ParseOk
                       (([],
                          {
                            Parser_Turtle.prefixes =
                              (st.Parser_Turtle.prefixes);
                            Parser_Turtle.base_iri = base_val;
                            Parser_Turtle.bnode_counter =
                              (st.Parser_Turtle.bnode_counter)
                          }), pos2)
                 | Parser_Combinators.ParseFail (uu___4, uu___5) ->
                     if code = (Prims.of_int (0x7B))
                     then
                       (match parse_graph_body st input
                                (pos1 + Prims.int_one) [] fuel
                        with
                        | Parser_Combinators.ParseOk ((triples, st'), pos2)
                            ->
                            Parser_Combinators.ParseOk
                              (([(FStar_Pervasives_Native.None, triples)],
                                 st'), pos2)
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos))
                     else
                       if is_graph_keyword input pos1
                       then
                         (match Parser_Turtle.turtle_ws input
                                  (pos1 + (Prims.of_int (5)))
                          with
                          | Parser_Combinators.ParseOk ((), pos2) ->
                              if pos2 >= len
                              then
                                Parser_Combinators.ParseFail
                                  ("expected graph name or '{' after GRAPH",
                                    pos2)
                              else
                                (let c2 = FStar_String.index input pos2 in
                                 let code2 = FStar_Char.int_of_char c2 in
                                 if code2 = (Prims.of_int (0x7B))
                                 then
                                   match parse_graph_body st input
                                           (pos2 + Prims.int_one) [] fuel
                                   with
                                   | Parser_Combinators.ParseOk
                                       ((triples, st'), pos3) ->
                                       Parser_Combinators.ParseOk
                                         (([(FStar_Pervasives_Native.None,
                                              triples)], st'), pos3)
                                   | Parser_Combinators.ParseFail (msg, fpos)
                                       ->
                                       Parser_Combinators.ParseFail
                                         (msg, fpos)
                                 else
                                   (match parse_trig_graph_name st input pos2
                                    with
                                    | Parser_Combinators.ParseOk
                                        ((gname, st2), pos3) ->
                                        (match Parser_Turtle.turtle_ws input
                                                 pos3
                                         with
                                         | Parser_Combinators.ParseOk
                                             ((), pos4) ->
                                             if pos4 >= len
                                             then
                                               Parser_Combinators.ParseFail
                                                 ("expected '{'", pos4)
                                             else
                                               if
                                                 (FStar_Char.int_of_char
                                                    (FStar_String.index input
                                                       pos4))
                                                   = (Prims.of_int (0x7B))
                                               then
                                                 (match parse_graph_body st2
                                                          input
                                                          (pos4 +
                                                             Prims.int_one)
                                                          [] fuel
                                                  with
                                                  | Parser_Combinators.ParseOk
                                                      ((triples, st3), pos5)
                                                      ->
                                                      Parser_Combinators.ParseOk
                                                        (([((FStar_Pervasives_Native.Some
                                                               gname),
                                                             triples)], st3),
                                                          pos5)
                                                  | Parser_Combinators.ParseFail
                                                      (msg, fpos) ->
                                                      Parser_Combinators.ParseFail
                                                        (msg, fpos))
                                               else
                                                 Parser_Combinators.ParseFail
                                                   ("expected '{' after graph name",
                                                     pos4))
                                    | Parser_Combinators.ParseFail
                                        (msg, fpos) ->
                                        Parser_Combinators.ParseFail
                                          (msg, fpos))))
                       else
                         (match parse_trig_graph_name st input pos1 with
                          | Parser_Combinators.ParseOk
                              ((candidate_name, st2), pos2) ->
                              (match Parser_Turtle.turtle_ws input pos2 with
                               | Parser_Combinators.ParseOk ((), pos3) ->
                                   if
                                     (pos3 < len) &&
                                       ((FStar_Char.int_of_char
                                           (FStar_String.index input pos3))
                                          = (Prims.of_int (0x7B)))
                                   then
                                     (match parse_graph_body st2 input
                                              (pos3 + Prims.int_one) [] fuel
                                      with
                                      | Parser_Combinators.ParseOk
                                          ((triples, st3), pos4) ->
                                          Parser_Combinators.ParseOk
                                            (([((FStar_Pervasives_Native.Some
                                                   candidate_name), triples)],
                                               st3), pos4)
                                      | Parser_Combinators.ParseFail
                                          (msg, fpos) ->
                                          Parser_Combinators.ParseFail
                                            (msg, fpos))
                                   else
                                     (let is_bnode =
                                        ((FStar_String.strlen candidate_name)
                                           >= (Prims.of_int (2)))
                                          &&
                                          (let c0 =
                                             FStar_String.index
                                               candidate_name Prims.int_zero in
                                           let c1 =
                                             FStar_String.index
                                               candidate_name Prims.int_one in
                                           ((FStar_Char.int_of_char c0) =
                                              (Prims.of_int (0x5F)))
                                             &&
                                             ((FStar_Char.int_of_char c1) =
                                                (Prims.of_int (0x3A)))) in
                                      if is_bnode
                                      then
                                        let bname =
                                          if
                                            (FStar_String.strlen
                                               candidate_name)
                                              > (Prims.of_int (2))
                                          then
                                            FStar_String.sub candidate_name
                                              (Prims.of_int (2))
                                              ((FStar_String.strlen
                                                  candidate_name)
                                                 - (Prims.of_int (2)))
                                          else "" in
                                        let subj =
                                          RDF_Graph_Executable.S_BNode bname in
                                        match Parser_Turtle.parse_predicate_object_list
                                                st2 subj input pos3 fuel'
                                        with
                                        | Parser_Combinators.ParseOk
                                            ((po_triples, st3), pos4) ->
                                            (match Parser_Turtle.turtle_ws
                                                     input pos4
                                             with
                                             | Parser_Combinators.ParseOk
                                                 ((), pos5) ->
                                                 let pos6 =
                                                   if
                                                     (pos5 < len) &&
                                                       ((FStar_Char.int_of_char
                                                           (FStar_String.index
                                                              input pos5))
                                                          =
                                                          (Prims.of_int (0x2E)))
                                                   then pos5 + Prims.int_one
                                                   else pos5 in
                                                 Parser_Combinators.ParseOk
                                                   (([(FStar_Pervasives_Native.None,
                                                        po_triples)], st3),
                                                     pos6))
                                        | Parser_Combinators.ParseFail
                                            (msg, fpos) ->
                                            Parser_Combinators.ParseFail
                                              (msg, fpos)
                                      else
                                        if
                                          RDF_Graph_Executable.is_iri
                                            candidate_name
                                        then
                                          (let subj =
                                             RDF_Graph_Executable.S_IRI
                                               candidate_name in
                                           match Parser_Turtle.parse_predicate_object_list
                                                   st2 subj input pos3 fuel'
                                           with
                                           | Parser_Combinators.ParseOk
                                               ((po_triples, st3), pos4) ->
                                               (match Parser_Turtle.turtle_ws
                                                        input pos4
                                                with
                                                | Parser_Combinators.ParseOk
                                                    ((), pos5) ->
                                                    let pos6 =
                                                      if
                                                        (pos5 < len) &&
                                                          ((FStar_Char.int_of_char
                                                              (FStar_String.index
                                                                 input pos5))
                                                             =
                                                             (Prims.of_int (0x2E)))
                                                      then
                                                        pos5 + Prims.int_one
                                                      else pos5 in
                                                    Parser_Combinators.ParseOk
                                                      (([(FStar_Pervasives_Native.None,
                                                           po_triples)], st3),
                                                        pos6))
                                           | Parser_Combinators.ParseFail
                                               (msg, fpos) ->
                                               Parser_Combinators.ParseFail
                                                 (msg, fpos))
                                        else
                                          Parser_Combinators.ParseFail
                                            ("invalid IRI for subject", pos3)))
                          | Parser_Combinators.ParseFail (uu___8, uu___9) ->
                              (match Parser_Turtle.parse_turtle_statement st
                                       input pos1 fuel
                               with
                               | Parser_Combinators.ParseOk
                                   ((triples, st'), pos2) ->
                                   Parser_Combinators.ParseOk
                                     (([(FStar_Pervasives_Native.None,
                                          triples)], st'), pos2)
                               | Parser_Combinators.ParseFail (msg, fpos) ->
                                   Parser_Combinators.ParseFail (msg, fpos))))))
let rec parse_trig_doc (st : Parser_Turtle.turtle_state)
  (input : Prims.string) (pos : Prims.nat)
  (ds : RDF_Graph_Executable.rdf_dataset) (fuel : Prims.nat) :
  (RDF_Graph_Executable.rdf_dataset * Parser_Turtle.turtle_state)=
  if fuel = Prims.int_zero
  then (ds, st)
  else
    (let fuel' = fuel - Prims.int_one in
     let len = FStar_String.strlen input in
     match Parser_Turtle.turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then (ds, st)
         else
           (match parse_trig_statement st input pos1 fuel with
            | Parser_Combinators.ParseOk ((deltas, st'), pos2) ->
                if pos2 = pos1
                then
                  let ds' =
                    FStar_List_Tot_Base.fold_left
                      (fun acc delta ->
                         let uu___2 = delta in
                         match uu___2 with
                         | (gname, triples) ->
                             trig_dataset_add_triples acc triples gname) ds
                      deltas in
                  (ds', st')
                else
                  (let ds' =
                     FStar_List_Tot_Base.fold_left
                       (fun acc delta ->
                          let uu___3 = delta in
                          match uu___3 with
                          | (gname, triples) ->
                              trig_dataset_add_triples acc triples gname) ds
                       deltas in
                   parse_trig_doc st' input pos2 ds' fuel')
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                let pos2 = graph_body_skip_line input pos1 (len - pos1) in
                if pos2 = pos1
                then (ds, st)
                else parse_trig_doc st input pos2 ds fuel'))
let parse_trig (input : Prims.string) : RDF_Graph_Executable.rdf_dataset=
  let len = FStar_String.strlen input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (3)) in
  let uu___ =
    parse_trig_doc Parser_Turtle.empty_turtle_state input Prims.int_zero
      RDF_Graph_Executable.empty_dataset fuel in
  match uu___ with | (ds, uu___1) -> ds
let parse_trig_with_base (input : Prims.string) (base : Prims.string) :
  RDF_Graph_Executable.rdf_dataset=
  let len = FStar_String.strlen input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (3)) in
  let st =
    {
      Parser_Turtle.prefixes =
        (Parser_Turtle.empty_turtle_state.Parser_Turtle.prefixes);
      Parser_Turtle.base_iri = base;
      Parser_Turtle.bnode_counter =
        (Parser_Turtle.empty_turtle_state.Parser_Turtle.bnode_counter)
    } in
  let uu___ =
    parse_trig_doc st input Prims.int_zero RDF_Graph_Executable.empty_dataset
      fuel in
  match uu___ with | (ds, uu___1) -> ds
