open Prims
let parse_graph_label : RDF_Term.iri Parser_Combinators.parser=
  fun input pos ->
    let len = Parser_FastString.fs_byte_length input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected graph label", pos)
    else
      (let ch = Parser_FastString.fs_byte_index input pos in
       let code = FStar_Char.int_of_char ch in
       if code = (Prims.of_int (0x3C))
       then
         match Parser_NTriples.parse_iri_raw input pos with
         | Parser_Combinators.ParseOk (iri, pos') ->
             (if RDF_Term.is_iri iri
              then Parser_Combinators.ParseOk (iri, pos')
              else
                Parser_Combinators.ParseFail
                  ("graph label IRI must be absolute", pos))
         | Parser_Combinators.ParseFail (msg, fpos) ->
             Parser_Combinators.ParseFail (msg, fpos)
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
  RDF_Term.iri FStar_Pervasives_Native.option Parser_Combinators.parser=
  fun input pos ->
    let len = Parser_FastString.fs_byte_length input in
    match Parser_NTriples.pws input pos with
    | Parser_Combinators.ParseOk ((), pos1) ->
        if pos1 >= len
        then Parser_Combinators.ParseOk (FStar_Pervasives_Native.None, pos1)
        else
          (let ch = Parser_FastString.fs_byte_index input pos1 in
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
               if code = (Prims.of_int (0x22))
               then
                 Parser_Combinators.ParseFail
                   ("literals are not allowed as graph names in N-Quads",
                     pos1)
               else
                 Parser_Combinators.ParseOk
                   (FStar_Pervasives_Native.None, pos1))
    | Parser_Combinators.ParseFail (msg, fpos) ->
        Parser_Combinators.ParseFail (msg, fpos)
let parse_nquad :
  (RDF_Triple.triple * RDF_Term.iri FStar_Pervasives_Native.option)
    Parser_Combinators.parser=
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
                                             Parser_FastString.fs_byte_length
                                               input in
                                           if pos8 >= len
                                           then
                                             Parser_Combinators.ParseFail
                                               ("expected '.'", pos8)
                                           else
                                             (let dot =
                                                Parser_FastString.fs_byte_index
                                                  input pos8 in
                                              if
                                                (FStar_Char.int_of_char dot)
                                                  = (Prims.of_int (0x2E))
                                              then
                                                (if RDF_Term.is_iri pred
                                                 then
                                                   let t =
                                                     {
                                                       RDF_Triple.s = subj;
                                                       RDF_Triple.p = pred;
                                                       RDF_Triple.o = obj
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
let rec find_named_graph (name : RDF_Term.iri)
  (ngs : RDF_Graph.named_graph Prims.list) :
  (RDF_Graph.named_graph Prims.list * RDF_Graph.rdf_graph *
    RDF_Graph.named_graph Prims.list) FStar_Pervasives_Native.option=
  match ngs with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.RDF_Graph.ng_name = name
      then FStar_Pervasives_Native.Some ([], (ng.RDF_Graph.ng_graph), rest)
      else
        (match find_named_graph name rest with
         | FStar_Pervasives_Native.Some (before, g, after) ->
             FStar_Pervasives_Native.Some ((ng :: before), g, after)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let dataset_add_quad (ds : RDF_Graph.rdf_dataset) (t : RDF_Triple.triple)
  (graph_name : RDF_Term.iri FStar_Pervasives_Native.option) :
  RDF_Graph.rdf_dataset=
  match graph_name with
  | FStar_Pervasives_Native.None ->
      {
        RDF_Graph.ds_default =
          (RDF_Graph_Executable.graph_add_unchecked t ds.RDF_Graph.ds_default);
        RDF_Graph.ds_named = (ds.RDF_Graph.ds_named)
      }
  | FStar_Pervasives_Native.Some name ->
      (match find_named_graph name ds.RDF_Graph.ds_named with
       | FStar_Pervasives_Native.Some (before, existing_g, after) ->
           let updated_g =
             RDF_Graph_Executable.graph_add_unchecked t existing_g in
           let updated_ng =
             { RDF_Graph.ng_name = name; RDF_Graph.ng_graph = updated_g } in
           {
             RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
             RDF_Graph.ds_named =
               (FStar_List_Tot_Base.op_At before
                  (FStar_List_Tot_Base.op_At [updated_ng] after))
           }
       | FStar_Pervasives_Native.None ->
           let new_ng =
             { RDF_Graph.ng_name = name; RDF_Graph.ng_graph = [t] } in
           {
             RDF_Graph.ds_default = (ds.RDF_Graph.ds_default);
             RDF_Graph.ds_named =
               (FStar_List_Tot_Base.op_At ds.RDF_Graph.ds_named [new_ng])
           })
let rec parse_nquads_acc (input : Prims.string) (pos : Prims.nat)
  (ds : RDF_Graph.rdf_dataset) (fuel : Prims.nat) : RDF_Graph.rdf_dataset=
  if fuel = Prims.int_zero
  then ds
  else
    (let len = Parser_FastString.fs_byte_length input in
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
          (let ch = Parser_FastString.fs_byte_index input pos1 in
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
                          (let c = Parser_FastString.fs_byte_index input p in
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
let parse_nquads (input : Prims.string) : RDF_Graph.rdf_dataset=
  let len = Parser_FastString.fs_byte_length input in
  RDF_Graph_Executable.dataset_finalise
    (parse_nquads_acc input Prims.int_zero RDF_Graph.empty_dataset
       (len + Prims.int_one))
let rec fold_nquads_acc :
  'a .
    (RDF_Triple.triple ->
       RDF_Term.iri FStar_Pervasives_Native.option -> 'a -> 'a)
      ->
      ('a -> Prims.bool) ->
        Prims.string -> Prims.nat -> 'a -> Prims.nat -> 'a
  =
  fun step stop input pos acc fuel ->
    if fuel = Prims.int_zero
    then acc
    else
      if stop acc
      then acc
      else
        (let len = Parser_FastString.fs_byte_length input in
         if pos >= len
         then acc
         else
           (let pos1 =
              match Parser_NTriples.pws input pos with
              | Parser_Combinators.ParseOk ((), p) -> p
              | uu___3 -> pos in
            if pos1 >= len
            then acc
            else
              (let ch = Parser_FastString.fs_byte_index input pos1 in
               let code = FStar_Char.int_of_char ch in
               if code = (Prims.of_int (0x23))
               then
                 let pos2 = Parser_NTriples.skip_comment input pos1 in
                 let pos3 = Parser_NTriples.skip_eol input pos2 in
                 (if pos3 = pos1
                  then acc
                  else
                    fold_nquads_acc step stop input pos3 acc
                      (fuel - Prims.int_one))
               else
                 if
                   (code = (Prims.of_int (0x0A))) ||
                     (code = (Prims.of_int (0x0D)))
                 then
                   (let pos2 = Parser_NTriples.skip_eol input pos1 in
                    if pos2 = pos1
                    then acc
                    else
                      fold_nquads_acc step stop input pos2 acc
                        (fuel - Prims.int_one))
                 else
                   (match parse_nquad input pos1 with
                    | Parser_Combinators.ParseOk ((t, graph_opt), pos2) ->
                        let acc1 = step t graph_opt acc in
                        let pos3 =
                          match Parser_NTriples.pws input pos2 with
                          | Parser_Combinators.ParseOk ((), p) -> p
                          | uu___6 -> pos2 in
                        let pos4 = Parser_NTriples.skip_comment input pos3 in
                        let pos5 = Parser_NTriples.skip_eol input pos4 in
                        let pos_next =
                          if pos5 > pos1
                          then pos5
                          else if pos4 > pos1 then pos4 else pos2 in
                        if stop acc1
                        then acc1
                        else
                          fold_nquads_acc step stop input pos_next acc1
                            (fuel - Prims.int_one)
                    | Parser_Combinators.ParseFail (uu___6, uu___7) ->
                        let rec skip_line p f =
                          if f = Prims.int_zero
                          then p
                          else
                            if p >= len
                            then p
                            else
                              (let c =
                                 Parser_FastString.fs_byte_index input p in
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
                        then acc
                        else
                          fold_nquads_acc step stop input pos2 acc
                            (fuel - Prims.int_one)))))
let fold_nquads
  (step :
    RDF_Triple.triple ->
      RDF_Term.iri FStar_Pervasives_Native.option -> 'a -> 'a)
  (stop : 'a -> Prims.bool) (init : 'a) (input : Prims.string) : 'a=
  let len = Parser_FastString.fs_byte_length input in
  fold_nquads_acc step stop input Prims.int_zero init (len + Prims.int_one)
let validate_graph_label (input : Prims.string) (pos : Prims.nat) :
  Prims.nat Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected graph label", pos)
  else
    (let ch = Parser_FastString.fs_byte_index input pos in
     let code = FStar_Char.int_of_char ch in
     if code = (Prims.of_int (0x3C))
     then Parser_NTriples.validate_iri input pos
     else
       if code = (Prims.of_int (0x5F))
       then Parser_NTriples.validate_bnode input pos
       else
         Parser_Combinators.ParseFail
           ("expected '<' or '_:' for graph label", pos))
let validate_opt_graph_label (input : Prims.string) (pos : Prims.nat) :
  Prims.nat Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  match Parser_NTriples.pws input pos with
  | Parser_Combinators.ParseOk ((), pos1) ->
      if pos1 >= len
      then Parser_Combinators.ParseOk (pos1, pos1)
      else
        (let ch = Parser_FastString.fs_byte_index input pos1 in
         let code = FStar_Char.int_of_char ch in
         if code = (Prims.of_int (0x2E))
         then Parser_Combinators.ParseOk (pos1, pos1)
         else
           if
             (code = (Prims.of_int (0x3C))) || (code = (Prims.of_int (0x5F)))
           then validate_graph_label input pos1
           else
             if code = (Prims.of_int (0x22))
             then
               Parser_Combinators.ParseFail
                 ("literals are not allowed as graph names in N-Quads", pos1)
             else Parser_Combinators.ParseOk (pos1, pos1))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let validate_nquad (input : Prims.string) (pos : Prims.nat) :
  Prims.nat Parser_Combinators.parse_result=
  match Parser_NTriples.pws input pos with
  | Parser_Combinators.ParseOk ((), pos1) ->
      (match Parser_NTriples.validate_subject input pos1 with
       | Parser_Combinators.ParseOk (pos2, uu___) ->
           (match Parser_NTriples.pws input pos2 with
            | Parser_Combinators.ParseOk ((), pos3) ->
                (match Parser_NTriples.validate_iri input pos3 with
                 | Parser_Combinators.ParseOk (pos4, uu___1) ->
                     (match Parser_NTriples.pws input pos4 with
                      | Parser_Combinators.ParseOk ((), pos5) ->
                          (match Parser_NTriples.validate_object input pos5
                           with
                           | Parser_Combinators.ParseOk (pos6, uu___2) ->
                               (match validate_opt_graph_label input pos6
                                with
                                | Parser_Combinators.ParseOk (pos7, uu___3)
                                    ->
                                    (match Parser_NTriples.pws input pos7
                                     with
                                     | Parser_Combinators.ParseOk ((), pos8)
                                         ->
                                         let len =
                                           Parser_FastString.fs_byte_length
                                             input in
                                         if pos8 >= len
                                         then
                                           Parser_Combinators.ParseFail
                                             ("expected '.'", pos8)
                                         else
                                           (let dot =
                                              Parser_FastString.fs_byte_index
                                                input pos8 in
                                            if
                                              (FStar_Char.int_of_char dot) =
                                                (Prims.of_int (0x2E))
                                            then
                                              Parser_Combinators.ParseOk
                                                ((pos8 + Prims.int_one),
                                                  (pos8 + Prims.int_one))
                                            else
                                              Parser_Combinators.ParseFail
                                                ("expected '.'", pos8))
                                     | Parser_Combinators.ParseFail
                                         (msg, fpos) ->
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
           Parser_Combinators.ParseFail (msg, fpos))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let rec count_nquads_acc (input : Prims.string) (pos : Prims.nat)
  (acc : Prims.nat) (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then acc
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then acc
     else
       (let pos1 =
          match Parser_NTriples.pws input pos with
          | Parser_Combinators.ParseOk ((), p) -> p
          | uu___2 -> pos in
        if pos1 >= len
        then acc
        else
          (let ch = Parser_FastString.fs_byte_index input pos1 in
           let code = FStar_Char.int_of_char ch in
           if code = (Prims.of_int (0x23))
           then
             let pos2 = Parser_NTriples.skip_comment input pos1 in
             let pos3 = Parser_NTriples.skip_eol input pos2 in
             (if pos3 = pos1
              then acc
              else count_nquads_acc input pos3 acc (fuel - Prims.int_one))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then
               (let pos2 = Parser_NTriples.skip_eol input pos1 in
                if pos2 = pos1
                then acc
                else count_nquads_acc input pos2 acc (fuel - Prims.int_one))
             else
               (match validate_nquad input pos1 with
                | Parser_Combinators.ParseOk (pos2, uu___5) ->
                    let pos3 =
                      match Parser_NTriples.pws input pos2 with
                      | Parser_Combinators.ParseOk ((), p) -> p
                      | uu___6 -> pos2 in
                    let pos4 = Parser_NTriples.skip_comment input pos3 in
                    let pos5 = Parser_NTriples.skip_eol input pos4 in
                    let pos_next =
                      if pos5 > pos1
                      then pos5
                      else if pos4 > pos1 then pos4 else pos2 in
                    count_nquads_acc input pos_next (acc + Prims.int_one)
                      (fuel - Prims.int_one)
                | Parser_Combinators.ParseFail (uu___5, uu___6) ->
                    let rec skip_line p f =
                      if f = Prims.int_zero
                      then p
                      else
                        if p >= len
                        then p
                        else
                          (let c = Parser_FastString.fs_byte_index input p in
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
                    then acc
                    else
                      count_nquads_acc input pos2 acc (fuel - Prims.int_one)))))
let count_nquads_quads (input : Prims.string) : Prims.nat=
  let len = Parser_FastString.fs_byte_length input in
  count_nquads_acc input Prims.int_zero Prims.int_zero (len + Prims.int_one)
let rec parse_nquads_strict_acc (input : Prims.string) (pos : Prims.nat)
  (ds : RDF_Graph.rdf_dataset) (fuel : Prims.nat) :
  RDF_Graph.rdf_dataset FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then FStar_Pervasives_Native.Some ds
     else
       (let pos1 =
          match Parser_NTriples.pws input pos with
          | Parser_Combinators.ParseOk ((), p) -> p
          | uu___2 -> pos in
        if pos1 >= len
        then FStar_Pervasives_Native.Some ds
        else
          (let ch = Parser_FastString.fs_byte_index input pos1 in
           let code = FStar_Char.int_of_char ch in
           if code = (Prims.of_int (0x23))
           then
             let pos2 = Parser_NTriples.skip_comment input pos1 in
             let pos3 = Parser_NTriples.skip_eol input pos2 in
             (if pos3 = pos1
              then FStar_Pervasives_Native.None
              else
                parse_nquads_strict_acc input pos3 ds (fuel - Prims.int_one))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then
               (let pos2 = Parser_NTriples.skip_eol input pos1 in
                if pos2 = pos1
                then FStar_Pervasives_Native.None
                else
                  parse_nquads_strict_acc input pos2 ds
                    (fuel - Prims.int_one))
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
                    if pos5 > pos1
                    then
                      parse_nquads_strict_acc input pos5 ds'
                        (fuel - Prims.int_one)
                    else
                      if pos2 >= len
                      then
                        parse_nquads_strict_acc input pos2 ds'
                          (fuel - Prims.int_one)
                      else FStar_Pervasives_Native.None
                | Parser_Combinators.ParseFail (uu___5, uu___6) ->
                    FStar_Pervasives_Native.None))))
let parse_nquads_strict (input : Prims.string) :
  RDF_Graph.rdf_dataset FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  match parse_nquads_strict_acc input Prims.int_zero RDF_Graph.empty_dataset
          (len + Prims.int_one)
  with
  | FStar_Pervasives_Native.Some ds ->
      FStar_Pervasives_Native.Some (RDF_Graph_Executable.dataset_finalise ds)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
type nquad =
  {
  nq_triple: RDF_Triple.triple ;
  nq_graph: RDF_Term.iri FStar_Pervasives_Native.option }
let __proj__Mknquad__item__nq_triple (projectee : nquad) : RDF_Triple.triple=
  match projectee with | { nq_triple; nq_graph;_} -> nq_triple
let __proj__Mknquad__item__nq_graph (projectee : nquad) :
  RDF_Term.iri FStar_Pervasives_Native.option=
  match projectee with | { nq_triple; nq_graph;_} -> nq_graph
let rec parse_nquads_flat_acc (input : Prims.string) (pos : Prims.nat)
  (acc : nquad Prims.list) (fuel : Prims.nat) : nquad Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    (let len = Parser_FastString.fs_byte_length input in
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
          (let ch = Parser_FastString.fs_byte_index input pos1 in
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
                          (let c = Parser_FastString.fs_byte_index input p in
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
  let len = Parser_FastString.fs_byte_length input in
  parse_nquads_flat_acc input Prims.int_zero [] (len + Prims.int_one)
