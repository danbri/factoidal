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
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected graph name", pos)
  else
    (let c = Parser_FastString.fs_byte_index input pos in
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
       if code = (Prims.of_int (0x5B))
       then
         (match Parser_Turtle.turtle_ws input (pos + Prims.int_one) with
          | Parser_Combinators.ParseOk ((), pos2) ->
              if
                (pos2 < len) &&
                  ((FStar_Char.int_of_char
                      (Parser_FastString.fs_byte_index input pos2))
                     = (Prims.of_int (0x5D)))
              then
                let uu___2 = Parser_Turtle.fresh_bnode st in
                (match uu___2 with
                 | (bname, st') ->
                     let bnode_iri = FStar_String.concat "" ["_:"; bname] in
                     Parser_Combinators.ParseOk
                       ((bnode_iri, st'), (pos2 + Prims.int_one)))
              else
                Parser_Combinators.ParseFail
                  ("expected ']' for anonymous blank node graph name", pos2))
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
let is_at_directive (input : Prims.string) (pos : Prims.nat) : Prims.bool=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then false
  else
    if
      (FStar_Char.int_of_char (Parser_FastString.fs_byte_index input pos)) <>
        (Prims.of_int (0x40))
    then false
    else
      if (pos + (Prims.of_int (7))) <= len
      then
        (let s = Parser_FastString.fs_byte_sub input pos (Prims.of_int (7)) in
         if s = "@prefix"
         then true
         else
           if (pos + (Prims.of_int (5))) <= len
           then
             (let s2 =
                Parser_FastString.fs_byte_sub input pos (Prims.of_int (5)) in
              s2 = "@base")
           else false)
      else
        if (pos + (Prims.of_int (5))) <= len
        then
          (let s2 =
             Parser_FastString.fs_byte_sub input pos (Prims.of_int (5)) in
           s2 = "@base")
        else false
let is_sparql_directive (input : Prims.string) (pos : Prims.nat) :
  Prims.bool=
  let len = Parser_FastString.fs_byte_length input in
  if (pos + (Prims.of_int (6))) <= len
  then
    let c0 = char_to_lower (Parser_FastString.fs_byte_index input pos) in
    let c1 =
      char_to_lower
        (Parser_FastString.fs_byte_index input (pos + Prims.int_one)) in
    let c2 =
      char_to_lower
        (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2)))) in
    let c3 =
      char_to_lower
        (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (3)))) in
    let c4 =
      char_to_lower
        (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (4)))) in
    let c5 =
      char_to_lower
        (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (5)))) in
    (if
       ((((((FStar_Char.int_of_char c0) = (Prims.of_int (0x70))) &&
             ((FStar_Char.int_of_char c1) = (Prims.of_int (0x72))))
            && ((FStar_Char.int_of_char c2) = (Prims.of_int (0x65))))
           && ((FStar_Char.int_of_char c3) = (Prims.of_int (0x66))))
          && ((FStar_Char.int_of_char c4) = (Prims.of_int (0x69))))
         && ((FStar_Char.int_of_char c5) = (Prims.of_int (0x78)))
     then
       (if (pos + (Prims.of_int (6))) >= len
        then true
        else
          Prims.op_Negation
            (Parser_Turtle.is_pn_chars
               (Parser_FastString.fs_byte_index input
                  (pos + (Prims.of_int (6))))))
     else
       if (pos + (Prims.of_int (4))) <= len
       then
         (if
            ((((FStar_Char.int_of_char c0) = (Prims.of_int (0x62))) &&
                ((FStar_Char.int_of_char c1) = (Prims.of_int (0x61))))
               && ((FStar_Char.int_of_char c2) = (Prims.of_int (0x73))))
              && ((FStar_Char.int_of_char c3) = (Prims.of_int (0x65)))
          then
            (if (pos + (Prims.of_int (4))) >= len
             then true
             else
               Prims.op_Negation
                 (Parser_Turtle.is_pn_chars
                    (Parser_FastString.fs_byte_index input
                       (pos + (Prims.of_int (4))))))
          else false)
       else false)
  else
    if (pos + (Prims.of_int (4))) <= len
    then
      (let c0 = char_to_lower (Parser_FastString.fs_byte_index input pos) in
       let c1 =
         char_to_lower
           (Parser_FastString.fs_byte_index input (pos + Prims.int_one)) in
       let c2 =
         char_to_lower
           (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2)))) in
       let c3 =
         char_to_lower
           (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (3)))) in
       if
         ((((FStar_Char.int_of_char c0) = (Prims.of_int (0x62))) &&
             ((FStar_Char.int_of_char c1) = (Prims.of_int (0x61))))
            && ((FStar_Char.int_of_char c2) = (Prims.of_int (0x73))))
           && ((FStar_Char.int_of_char c3) = (Prims.of_int (0x65)))
       then
         (if (pos + (Prims.of_int (4))) >= len
          then true
          else
            Prims.op_Negation
              (Parser_Turtle.is_pn_chars
                 (Parser_FastString.fs_byte_index input
                    (pos + (Prims.of_int (4))))))
       else false)
    else false
let is_directive_at (input : Prims.string) (pos : Prims.nat) : Prims.bool=
  (is_at_directive input pos) || (is_sparql_directive input pos)
let is_graph_keyword (input : Prims.string) (pos : Prims.nat) : Prims.bool=
  let len = Parser_FastString.fs_byte_length input in
  if (pos + (Prims.of_int (5))) > len
  then false
  else
    (let c0 = char_to_lower (Parser_FastString.fs_byte_index input pos) in
     let c1 =
       char_to_lower
         (Parser_FastString.fs_byte_index input (pos + Prims.int_one)) in
     let c2 =
       char_to_lower
         (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2)))) in
     let c3 =
       char_to_lower
         (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (3)))) in
     let c4 =
       char_to_lower
         (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (4)))) in
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
          (let next =
             Parser_FastString.fs_byte_index input (pos + (Prims.of_int (5))) in
           Prims.op_Negation (Parser_Turtle.is_pn_chars next)))
     else false)
let rec graph_body_skip_line (input : Prims.string) (p : Prims.nat)
  (f : Prims.nat) : Prims.nat=
  if f = Prims.int_zero
  then p
  else
    if p >= (Parser_FastString.fs_byte_length input)
    then p
    else
      (let ch = Parser_FastString.fs_byte_index input p in
       let cd = FStar_Char.int_of_char ch in
       if (cd = (Prims.of_int (0x0A))) || (cd = (Prims.of_int (0x0D)))
       then p + Prims.int_one
       else
         if cd = (Prims.of_int (0x7D))
         then p
         else
           graph_body_skip_line input (p + Prims.int_one) (f - Prims.int_one))
type trig_parse_state =
  {
  ts: Parser_Turtle.turtle_state ;
  has_error: Prims.bool }
let __proj__Mktrig_parse_state__item__ts (projectee : trig_parse_state) :
  Parser_Turtle.turtle_state= match projectee with | { ts; has_error;_} -> ts
let __proj__Mktrig_parse_state__item__has_error
  (projectee : trig_parse_state) : Prims.bool=
  match projectee with | { ts; has_error;_} -> has_error
let rec parse_graph_body (tps : trig_parse_state) (input : Prims.string)
  (pos : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * trig_parse_state)
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (((FStar_List_Tot_Base.rev acc), tps), pos)
  else
    (let fuel' = fuel - Prims.int_one in
     let len = Parser_FastString.fs_byte_length input in
     match Parser_Turtle.turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then
           Parser_Combinators.ParseFail
             ("unterminated graph block, expected '}'", pos1)
         else
           (let c = Parser_FastString.fs_byte_index input pos1 in
            let code = FStar_Char.int_of_char c in
            if code = (Prims.of_int (0x7D))
            then
              Parser_Combinators.ParseOk
                (((FStar_List_Tot_Base.rev acc), tps),
                  (pos1 + Prims.int_one))
            else
              if is_directive_at input pos1
              then
                Parser_Combinators.ParseFail
                  ("directives not allowed inside graph block", pos1)
              else
                if is_graph_keyword input pos1
                then
                  Parser_Combinators.ParseFail
                    ("nested GRAPH not allowed inside graph block", pos1)
                else
                  (match Parser_Turtle.parse_turtle_statement tps.ts input
                           pos1 fuel
                   with
                   | Parser_Combinators.ParseOk ((triples, st'), pos2) ->
                       let tps' = { ts = st'; has_error = (tps.has_error) } in
                       if pos2 = pos1
                       then
                         Parser_Combinators.ParseOk
                           (((FStar_List_Tot_Base.rev
                                (FStar_List_Tot_Base.append
                                   (FStar_List_Tot_Base.rev triples) acc)),
                              tps'), pos2)
                       else
                         parse_graph_body tps' input pos2
                           (FStar_List_Tot_Base.append
                              (FStar_List_Tot_Base.rev triples) acc) fuel'
                   | Parser_Combinators.ParseFail (uu___5, uu___6) ->
                       let tps' = { ts = (tps.ts); has_error = true } in
                       let pos2 =
                         graph_body_skip_line input pos1 (len - pos1) in
                       if pos2 = pos1
                       then
                         Parser_Combinators.ParseOk
                           (((FStar_List_Tot_Base.rev acc), tps'), pos1)
                       else parse_graph_body tps' input pos2 acc fuel')))
let parse_trig_statement (tps : trig_parse_state) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  ((RDF_Graph_Executable.iri FStar_Pervasives_Native.option *
    RDF_Graph_Executable.triple Prims.list) Prims.list * trig_parse_state)
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit", pos)
  else
    (let fuel' = fuel - Prims.int_one in
     let len = Parser_FastString.fs_byte_length input in
     let st = tps.ts in
     match Parser_Turtle.turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then Parser_Combinators.ParseOk (([], tps), pos1)
         else
           (let c = Parser_FastString.fs_byte_index input pos1 in
            let code = FStar_Char.int_of_char c in
            match Parser_Turtle.parse_prefix_directive st input pos1 with
            | Parser_Combinators.ParseOk ((prefix, iri_val), pos2) ->
                let new_prefixes = (prefix, iri_val) ::
                  (st.Parser_Turtle.prefixes) in
                Parser_Combinators.ParseOk
                  (([],
                     {
                       ts =
                         {
                           Parser_Turtle.prefixes = new_prefixes;
                           Parser_Turtle.base_iri =
                             (st.Parser_Turtle.base_iri);
                           Parser_Turtle.bnode_counter =
                             (st.Parser_Turtle.bnode_counter)
                         };
                       has_error = (tps.has_error)
                     }), pos2)
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                (match Parser_Turtle.parse_base_directive st input pos1 with
                 | Parser_Combinators.ParseOk (base_val, pos2) ->
                     Parser_Combinators.ParseOk
                       (([],
                          {
                            ts =
                              {
                                Parser_Turtle.prefixes =
                                  (st.Parser_Turtle.prefixes);
                                Parser_Turtle.base_iri = base_val;
                                Parser_Turtle.bnode_counter =
                                  (st.Parser_Turtle.bnode_counter)
                              };
                            has_error = (tps.has_error)
                          }), pos2)
                 | Parser_Combinators.ParseFail (uu___4, uu___5) ->
                     if code = (Prims.of_int (0x7B))
                     then
                       (match parse_graph_body tps input
                                (pos1 + Prims.int_one) [] fuel
                        with
                        | Parser_Combinators.ParseOk ((triples, tps'), pos2)
                            ->
                            Parser_Combinators.ParseOk
                              (([(FStar_Pervasives_Native.None, triples)],
                                 tps'), pos2)
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
                                  ("expected graph name after GRAPH", pos2)
                              else
                                (match parse_trig_graph_name st input pos2
                                 with
                                 | Parser_Combinators.ParseOk
                                     ((gname, st2), pos3) ->
                                     (match Parser_Turtle.turtle_ws input
                                              pos3
                                      with
                                      | Parser_Combinators.ParseOk ((), pos4)
                                          ->
                                          if pos4 >= len
                                          then
                                            Parser_Combinators.ParseFail
                                              ("expected '{'", pos4)
                                          else
                                            if
                                              (FStar_Char.int_of_char
                                                 (Parser_FastString.fs_byte_index
                                                    input pos4))
                                                = (Prims.of_int (0x7B))
                                            then
                                              (let tps2 =
                                                 {
                                                   ts = st2;
                                                   has_error =
                                                     (tps.has_error)
                                                 } in
                                               match parse_graph_body tps2
                                                       input
                                                       (pos4 + Prims.int_one)
                                                       [] fuel
                                               with
                                               | Parser_Combinators.ParseOk
                                                   ((triples, tps3), pos5) ->
                                                   Parser_Combinators.ParseOk
                                                     (([((FStar_Pervasives_Native.Some
                                                            gname), triples)],
                                                        tps3), pos5)
                                               | Parser_Combinators.ParseFail
                                                   (msg, fpos) ->
                                                   Parser_Combinators.ParseFail
                                                     (msg, fpos))
                                            else
                                              Parser_Combinators.ParseFail
                                                ("expected '{' after graph name",
                                                  pos4))
                                 | Parser_Combinators.ParseFail (msg, fpos)
                                     ->
                                     Parser_Combinators.ParseFail (msg, fpos)))
                       else
                         if code = (Prims.of_int (0x28))
                         then
                           Parser_Combinators.ParseFail
                             ("collection cannot be used as graph name or subject in TriG",
                               pos1)
                         else
                           (match parse_trig_graph_name st input pos1 with
                            | Parser_Combinators.ParseOk
                                ((candidate_name, st2), pos2) ->
                                (match Parser_Turtle.turtle_ws input pos2
                                 with
                                 | Parser_Combinators.ParseOk ((), pos3) ->
                                     if
                                       (pos3 < len) &&
                                         ((FStar_Char.int_of_char
                                             (Parser_FastString.fs_byte_index
                                                input pos3))
                                            = (Prims.of_int (0x7B)))
                                     then
                                       let tps2 =
                                         {
                                           ts = st2;
                                           has_error = (tps.has_error)
                                         } in
                                       (match parse_graph_body tps2 input
                                                (pos3 + Prims.int_one) []
                                                fuel
                                        with
                                        | Parser_Combinators.ParseOk
                                            ((triples, tps3), pos4) ->
                                            Parser_Combinators.ParseOk
                                              (([((FStar_Pervasives_Native.Some
                                                     candidate_name),
                                                   triples)], tps3), pos4)
                                        | Parser_Combinators.ParseFail
                                            (msg, fpos) ->
                                            Parser_Combinators.ParseFail
                                              (msg, fpos))
                                     else
                                       (let is_bnode =
                                          ((Parser_FastString.fs_byte_length
                                              candidate_name)
                                             >= (Prims.of_int (2)))
                                            &&
                                            (let c0 =
                                               Parser_FastString.fs_byte_index
                                                 candidate_name
                                                 Prims.int_zero in
                                             let c1 =
                                               Parser_FastString.fs_byte_index
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
                                              (Parser_FastString.fs_byte_length
                                                 candidate_name)
                                                > (Prims.of_int (2))
                                            then
                                              Parser_FastString.fs_byte_sub
                                                candidate_name
                                                (Prims.of_int (2))
                                                ((Parser_FastString.fs_byte_length
                                                    candidate_name)
                                                   - (Prims.of_int (2)))
                                            else "" in
                                          let subj =
                                            RDF_Graph_Executable.S_BNode
                                              bname in
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
                                                   if
                                                     (pos5 < len) &&
                                                       ((FStar_Char.int_of_char
                                                           (Parser_FastString.fs_byte_index
                                                              input pos5))
                                                          =
                                                          (Prims.of_int (0x2E)))
                                                   then
                                                     Parser_Combinators.ParseOk
                                                       (([(FStar_Pervasives_Native.None,
                                                            po_triples)],
                                                          {
                                                            ts = st3;
                                                            has_error =
                                                              (tps.has_error)
                                                          }),
                                                         (pos5 +
                                                            Prims.int_one))
                                                   else
                                                     if
                                                       (pos5 >= len) ||
                                                         ((FStar_Char.int_of_char
                                                             (Parser_FastString.fs_byte_index
                                                                input pos5))
                                                            =
                                                            (Prims.of_int (0x7D)))
                                                     then
                                                       Parser_Combinators.ParseOk
                                                         (([(FStar_Pervasives_Native.None,
                                                              po_triples)],
                                                            {
                                                              ts = st3;
                                                              has_error =
                                                                (tps.has_error)
                                                            }), pos5)
                                                     else
                                                       Parser_Combinators.ParseFail
                                                         ("expected '.' after triple",
                                                           pos5))
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
                                                     st2 subj input pos3
                                                     fuel'
                                             with
                                             | Parser_Combinators.ParseOk
                                                 ((po_triples, st3), pos4) ->
                                                 (match Parser_Turtle.turtle_ws
                                                          input pos4
                                                  with
                                                  | Parser_Combinators.ParseOk
                                                      ((), pos5) ->
                                                      if
                                                        (pos5 < len) &&
                                                          ((FStar_Char.int_of_char
                                                              (Parser_FastString.fs_byte_index
                                                                 input pos5))
                                                             =
                                                             (Prims.of_int (0x2E)))
                                                      then
                                                        Parser_Combinators.ParseOk
                                                          (([(FStar_Pervasives_Native.None,
                                                               po_triples)],
                                                             {
                                                               ts = st3;
                                                               has_error =
                                                                 (tps.has_error)
                                                             }),
                                                            (pos5 +
                                                               Prims.int_one))
                                                      else
                                                        if
                                                          (pos5 >= len) ||
                                                            ((FStar_Char.int_of_char
                                                                (Parser_FastString.fs_byte_index
                                                                   input pos5))
                                                               =
                                                               (Prims.of_int (0x7D)))
                                                        then
                                                          Parser_Combinators.ParseOk
                                                            (([(FStar_Pervasives_Native.None,
                                                                 po_triples)],
                                                               {
                                                                 ts = st3;
                                                                 has_error =
                                                                   (tps.has_error)
                                                               }), pos5)
                                                        else
                                                          Parser_Combinators.ParseFail
                                                            ("expected '.' after triple",
                                                              pos5))
                                             | Parser_Combinators.ParseFail
                                                 (msg, fpos) ->
                                                 Parser_Combinators.ParseFail
                                                   (msg, fpos))
                                          else
                                            Parser_Combinators.ParseFail
                                              ("invalid IRI for subject",
                                                pos3)))
                            | Parser_Combinators.ParseFail (uu___9, uu___10)
                                ->
                                (match Parser_Turtle.parse_turtle_statement
                                         st input pos1 fuel
                                 with
                                 | Parser_Combinators.ParseOk
                                     ((triples, st'), pos2) ->
                                     Parser_Combinators.ParseOk
                                       (([(FStar_Pervasives_Native.None,
                                            triples)],
                                          {
                                            ts = st';
                                            has_error = (tps.has_error)
                                          }), pos2)
                                 | Parser_Combinators.ParseFail (msg, fpos)
                                     ->
                                     Parser_Combinators.ParseFail (msg, fpos))))))
let rec parse_trig_doc (tps : trig_parse_state) (input : Prims.string)
  (pos : Prims.nat) (ds : RDF_Graph_Executable.rdf_dataset)
  (fuel : Prims.nat) : (RDF_Graph_Executable.rdf_dataset * trig_parse_state)=
  if fuel = Prims.int_zero
  then (ds, tps)
  else
    (let fuel' = fuel - Prims.int_one in
     let len = Parser_FastString.fs_byte_length input in
     match Parser_Turtle.turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then (ds, tps)
         else
           (match parse_trig_statement tps input pos1 fuel with
            | Parser_Combinators.ParseOk ((deltas, tps'), pos2) ->
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
                  (ds', tps')
                else
                  (let ds' =
                     FStar_List_Tot_Base.fold_left
                       (fun acc delta ->
                          let uu___3 = delta in
                          match uu___3 with
                          | (gname, triples) ->
                              trig_dataset_add_triples acc triples gname) ds
                       deltas in
                   parse_trig_doc tps' input pos2 ds' fuel')
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                let tps' = { ts = (tps.ts); has_error = true } in
                let pos2 = graph_body_skip_line input pos1 (len - pos1) in
                if pos2 = pos1
                then (ds, tps')
                else parse_trig_doc tps' input pos2 ds fuel'))
let make_trig_parse_state (st : Parser_Turtle.turtle_state) :
  trig_parse_state= { ts = st; has_error = false }
let parse_trig (input : Prims.string) :
  RDF_Graph_Executable.rdf_dataset FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (3)) in
  let tps = make_trig_parse_state Parser_Turtle.empty_turtle_state in
  let uu___ =
    parse_trig_doc tps input Prims.int_zero
      RDF_Graph_Executable.empty_dataset fuel in
  match uu___ with
  | (ds, tps') ->
      if tps'.has_error
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some ds
let parse_trig_with_base (input : Prims.string) (base : Prims.string) :
  RDF_Graph_Executable.rdf_dataset FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (3)) in
  let st =
    {
      Parser_Turtle.prefixes =
        (Parser_Turtle.empty_turtle_state.Parser_Turtle.prefixes);
      Parser_Turtle.base_iri = base;
      Parser_Turtle.bnode_counter =
        (Parser_Turtle.empty_turtle_state.Parser_Turtle.bnode_counter)
    } in
  let tps = make_trig_parse_state st in
  let uu___ =
    parse_trig_doc tps input Prims.int_zero
      RDF_Graph_Executable.empty_dataset fuel in
  match uu___ with
  | (ds, tps') ->
      if tps'.has_error
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some ds
let parse_trig_lenient (input : Prims.string) :
  RDF_Graph_Executable.rdf_dataset=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (3)) in
  let tps = make_trig_parse_state Parser_Turtle.empty_turtle_state in
  let uu___ =
    parse_trig_doc tps input Prims.int_zero
      RDF_Graph_Executable.empty_dataset fuel in
  match uu___ with | (ds, uu___1) -> ds
let parse_trig_with_base_lenient (input : Prims.string) (base : Prims.string)
  : RDF_Graph_Executable.rdf_dataset=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (3)) in
  let st =
    {
      Parser_Turtle.prefixes =
        (Parser_Turtle.empty_turtle_state.Parser_Turtle.prefixes);
      Parser_Turtle.base_iri = base;
      Parser_Turtle.bnode_counter =
        (Parser_Turtle.empty_turtle_state.Parser_Turtle.bnode_counter)
    } in
  let tps = make_trig_parse_state st in
  let uu___ =
    parse_trig_doc tps input Prims.int_zero
      RDF_Graph_Executable.empty_dataset fuel in
  match uu___ with | (ds, uu___1) -> ds
