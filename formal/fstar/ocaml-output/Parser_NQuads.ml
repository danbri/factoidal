open Prims
let parse_graph_label : RDF_Graph_Executable.iri Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected graph label", pos)
    else
      (let ch = FStar_String.index input pos in
       let code = FStar_Char.int_of_char ch in
       if code = (Prims.of_int (0x3C))
       then Parser_NTriples.parse_iri_raw input pos
       else
         if code = (Prims.of_int (0x5F))
         then
           (match Parser_NTriples.parse_bnode input pos with
            | Parser_Combinators.ParseOk (bnode_label, pos') ->
                Parser_Combinators.ParseOk
                  ((FStar_String.concat "" ["_:"; bnode_label]), pos')
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos))
         else
           Parser_Combinators.ParseFail
             ("expected '<' or '_:' for graph label", pos))
let parse_opt_graph_label :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option
    Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    match Parser_NTriples.pws input pos with
    | Parser_Combinators.ParseOk ((), pos1) ->
        if pos1 >= len
        then Parser_Combinators.ParseOk (FStar_Pervasives_Native.None, pos1)
        else
          (let ch = FStar_String.index input pos1 in
           let code = FStar_Char.int_of_char ch in
           if code = (Prims.of_int (0x2E))
           then
             Parser_Combinators.ParseOk (FStar_Pervasives_Native.None, pos1)
           else
             if
               (code = (Prims.of_int (0x3C))) ||
                 (code = (Prims.of_int (0x5F)))
             then
               (match parse_graph_label input pos1 with
                | Parser_Combinators.ParseOk (g, pos2) ->
                    Parser_Combinators.ParseOk
                      ((FStar_Pervasives_Native.Some g), pos2)
                | Parser_Combinators.ParseFail (msg, fpos) ->
                    Parser_Combinators.ParseFail (msg, fpos))
             else
               Parser_Combinators.ParseOk
                 (FStar_Pervasives_Native.None, pos1))
    | Parser_Combinators.ParseFail (msg, fpos) ->
        Parser_Combinators.ParseFail (msg, fpos)
let parse_nquad :
  (RDF_Graph_Executable.triple * RDF_Graph_Executable.iri
    FStar_Pervasives_Native.option) Parser_Combinators.parser=
  fun input pos ->
    match Parser_NTriples.pws input pos with
    | Parser_Combinators.ParseOk ((), pos1) ->
        (match Parser_NTriples.parse_subject input pos1 with
         | Parser_Combinators.ParseOk (subj, pos2) ->
             (match Parser_NTriples.pws input pos2 with
              | Parser_Combinators.ParseOk ((), pos3) ->
                  (match Parser_NTriples.parse_iri input pos3 with
                   | Parser_Combinators.ParseOk (pred, pos4) ->
                       (match Parser_NTriples.pws input pos4 with
                        | Parser_Combinators.ParseOk ((), pos5) ->
                            (match Parser_NTriples.parse_object input pos5
                             with
                             | Parser_Combinators.ParseOk (obj, pos6) ->
                                 (match parse_opt_graph_label input pos6 with
                                  | Parser_Combinators.ParseOk
                                      (graph_opt, pos7) ->
                                      (match Parser_NTriples.pws input pos7
                                       with
                                       | Parser_Combinators.ParseOk
                                           ((), pos8) ->
                                           let len =
                                             FStar_String.strlen input in
                                           if pos8 >= len
                                           then
                                             Parser_Combinators.ParseFail
                                               ("expected '.'", pos8)
                                           else
                                             (let dot =
                                                FStar_String.index input pos8 in
                                              if
                                                (FStar_Char.int_of_char dot)
                                                  = (Prims.of_int (0x2E))
                                              then
                                                (if
                                                   RDF_Graph_Executable.is_iri
                                                     pred
                                                 then
                                                   let t =
                                                     {
                                                       RDF_Graph_Executable.s
                                                         = subj;
                                                       RDF_Graph_Executable.p
                                                         = pred;
                                                       RDF_Graph_Executable.o
                                                         = obj
                                                     } in
                                                   Parser_Combinators.ParseOk
                                                     ((t, graph_opt),
                                                       (pos8 + Prims.int_one))
                                                 else
                                                   Parser_Combinators.ParseFail
                                                     ("invalid predicate IRI",
                                                       pos4))
                                              else
                                                Parser_Combinators.ParseFail
                                                  ("expected '.'", pos8))
                                       | Parser_Combinators.ParseFail
                                           (msg, fpos) ->
                                           Parser_Combinators.ParseFail
                                             (msg, fpos))
                                  | Parser_Combinators.ParseFail (msg, fpos)
                                      ->
                                      Parser_Combinators.ParseFail
                                        (msg, fpos))
                             | Parser_Combinators.ParseFail (msg, fpos) ->
                                 Parser_Combinators.ParseFail (msg, fpos))
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos))
                   | Parser_Combinators.ParseFail (msg, fpos) ->
                       Parser_Combinators.ParseFail (msg, fpos))
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos))
         | Parser_Combinators.ParseFail (msg, fpos) ->
             Parser_Combinators.ParseFail (msg, fpos))
    | Parser_Combinators.ParseFail (msg, fpos) ->
        Parser_Combinators.ParseFail (msg, fpos)
let rec find_named_graph (name : RDF_Graph_Executable.iri)
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
        (match find_named_graph name rest with
         | FStar_Pervasives_Native.Some (before, g, after) ->
             FStar_Pervasives_Native.Some ((ng :: before), g, after)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let dataset_add_quad (ds : RDF_Graph_Executable.rdf_dataset)
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
      (match find_named_graph name ds.RDF_Graph_Executable.ds_named with
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
               (FStar_List_Tot_Base.op_At before
                  (FStar_List_Tot_Base.op_At [updated_ng] after))
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
               (FStar_List_Tot_Base.op_At ds.RDF_Graph_Executable.ds_named
                  [new_ng])
           })
let rec parse_nquads_acc (input : Prims.string) (pos : Prims.nat)
  (ds : RDF_Graph_Executable.rdf_dataset) (fuel : Prims.nat) :
  RDF_Graph_Executable.rdf_dataset=
  if fuel = Prims.int_zero
  then ds
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then ds
     else
       (let pos1 =
          match Parser_NTriples.pws input pos with
          | Parser_Combinators.ParseOk ((), p) -> p
          | uu___2 -> pos in
        if pos1 >= len
        then ds
        else
          (let ch = FStar_String.index input pos1 in
           let code = FStar_Char.int_of_char ch in
           if code = (Prims.of_int (0x23))
           then
             let pos2 = Parser_NTriples.skip_comment input pos1 in
             let pos3 = Parser_NTriples.skip_eol input pos2 in
             (if pos3 = pos1
              then ds
              else parse_nquads_acc input pos3 ds (fuel - Prims.int_one))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then
               (let pos2 = Parser_NTriples.skip_eol input pos1 in
                if pos2 = pos1
                then ds
                else parse_nquads_acc input pos2 ds (fuel - Prims.int_one))
             else
               (match parse_nquad input pos1 with
                | Parser_Combinators.ParseOk ((t, graph_opt), pos2) ->
                    let ds' = dataset_add_quad ds t graph_opt in
                    let pos3 =
                      match Parser_NTriples.pws input pos2 with
                      | Parser_Combinators.ParseOk ((), p) -> p
                      | uu___5 -> pos2 in
                    let pos4 = Parser_NTriples.skip_comment input pos3 in
                    let pos5 = Parser_NTriples.skip_eol input pos4 in
                    let pos_next =
                      if pos5 > pos1
                      then pos5
                      else if pos4 > pos1 then pos4 else pos2 in
                    parse_nquads_acc input pos_next ds'
                      (fuel - Prims.int_one)
                | Parser_Combinators.ParseFail (uu___5, uu___6) ->
                    let rec skip_line p f =
                      if f = Prims.int_zero
                      then p
                      else
                        if p >= len
                        then p
                        else
                          (let c = FStar_String.index input p in
                           let cc = FStar_Char.int_of_char c in
                           if
                             (cc = (Prims.of_int (0x0A))) ||
                               (cc = (Prims.of_int (0x0D)))
                           then Parser_NTriples.skip_eol input p
                           else
                             skip_line (p + Prims.int_one)
                               (f - Prims.int_one)) in
                    let pos2 = skip_line pos1 (len - pos1) in
                    if pos2 = pos1
                    then ds
                    else
                      parse_nquads_acc input pos2 ds (fuel - Prims.int_one)))))
let parse_nquads (input : Prims.string) : RDF_Graph_Executable.rdf_dataset=
  let len = FStar_String.strlen input in
  parse_nquads_acc input Prims.int_zero RDF_Graph_Executable.empty_dataset
    (len + Prims.int_one)
type nquad =
  {
  nq_triple: RDF_Graph_Executable.triple ;
  nq_graph: RDF_Graph_Executable.iri FStar_Pervasives_Native.option }
let __proj__Mknquad__item__nq_triple (projectee : nquad) :
  RDF_Graph_Executable.triple=
  match projectee with | { nq_triple; nq_graph;_} -> nq_triple
let __proj__Mknquad__item__nq_graph (projectee : nquad) :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option=
  match projectee with | { nq_triple; nq_graph;_} -> nq_graph
let rec parse_nquads_flat_acc (input : Prims.string) (pos : Prims.nat)
  (acc : nquad Prims.list) (fuel : Prims.nat) : nquad Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then FStar_List_Tot_Base.rev acc
     else
       (let pos1 =
          match Parser_NTriples.pws input pos with
          | Parser_Combinators.ParseOk ((), p) -> p
          | uu___2 -> pos in
        if pos1 >= len
        then FStar_List_Tot_Base.rev acc
        else
          (let ch = FStar_String.index input pos1 in
           let code = FStar_Char.int_of_char ch in
           if code = (Prims.of_int (0x23))
           then
             let pos2 = Parser_NTriples.skip_comment input pos1 in
             let pos3 = Parser_NTriples.skip_eol input pos2 in
             (if pos3 = pos1
              then FStar_List_Tot_Base.rev acc
              else
                parse_nquads_flat_acc input pos3 acc (fuel - Prims.int_one))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then
               (let pos2 = Parser_NTriples.skip_eol input pos1 in
                if pos2 = pos1
                then FStar_List_Tot_Base.rev acc
                else
                  parse_nquads_flat_acc input pos2 acc (fuel - Prims.int_one))
             else
               (match parse_nquad input pos1 with
                | Parser_Combinators.ParseOk ((t, graph_opt), pos2) ->
                    let q = { nq_triple = t; nq_graph = graph_opt } in
                    let pos3 =
                      match Parser_NTriples.pws input pos2 with
                      | Parser_Combinators.ParseOk ((), p) -> p
                      | uu___5 -> pos2 in
                    let pos4 = Parser_NTriples.skip_comment input pos3 in
                    let pos5 = Parser_NTriples.skip_eol input pos4 in
                    let pos_next =
                      if pos5 > pos1
                      then pos5
                      else if pos4 > pos1 then pos4 else pos2 in
                    parse_nquads_flat_acc input pos_next (q :: acc)
                      (fuel - Prims.int_one)
                | Parser_Combinators.ParseFail (uu___5, uu___6) ->
                    let rec skip_line p f =
                      if f = Prims.int_zero
                      then p
                      else
                        if p >= len
                        then p
                        else
                          (let c = FStar_String.index input p in
                           let cc = FStar_Char.int_of_char c in
                           if
                             (cc = (Prims.of_int (0x0A))) ||
                               (cc = (Prims.of_int (0x0D)))
                           then Parser_NTriples.skip_eol input p
                           else
                             skip_line (p + Prims.int_one)
                               (f - Prims.int_one)) in
                    let pos2 = skip_line pos1 (len - pos1) in
                    if pos2 = pos1
                    then FStar_List_Tot_Base.rev acc
                    else
                      parse_nquads_flat_acc input pos2 acc
                        (fuel - Prims.int_one)))))
let parse_nquads_flat (input : Prims.string) : nquad Prims.list=
  let len = FStar_String.strlen input in
  parse_nquads_flat_acc input Prims.int_zero [] (len + Prims.int_one)
