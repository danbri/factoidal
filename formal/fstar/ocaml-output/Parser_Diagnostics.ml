open Prims
type source_position =
  {
  sp_offset: Prims.nat ;
  sp_line: Prims.nat ;
  sp_column: Prims.nat }
let __proj__Mksource_position__item__sp_offset (projectee : source_position)
  : Prims.nat=
  match projectee with | { sp_offset; sp_line; sp_column;_} -> sp_offset
let __proj__Mksource_position__item__sp_line (projectee : source_position) :
  Prims.nat=
  match projectee with | { sp_offset; sp_line; sp_column;_} -> sp_line
let __proj__Mksource_position__item__sp_column (projectee : source_position)
  : Prims.nat=
  match projectee with | { sp_offset; sp_line; sp_column;_} -> sp_column
let rec position_of_offset_acc (input : Prims.string) (stop : Prims.nat)
  (i : Prims.nat) (line : Prims.nat) (col : Prims.nat) :
  (Prims.nat * Prims.nat)=
  if i >= stop
  then (line, col)
  else
    (let b = Parser_FastString.fs_byte_at input i in
     if b = (Prims.of_int (0x0A))
     then
       position_of_offset_acc input stop (i + Prims.int_one)
         (line + Prims.int_one) Prims.int_one
     else
       if (b >= (Prims.of_int (0x80))) && (b <= (Prims.of_int (0xBF)))
       then position_of_offset_acc input stop (i + Prims.int_one) line col
       else
         position_of_offset_acc input stop (i + Prims.int_one) line
           (col + Prims.int_one))
let position_of_offset (input : Prims.string) (offset : Prims.nat) :
  source_position=
  let len = Parser_FastString.fs_byte_length input in
  let stop = if offset > len then len else offset in
  let uu___ =
    position_of_offset_acc input stop Prims.int_zero Prims.int_one
      Prims.int_one in
  match uu___ with
  | (line, col) -> { sp_offset = offset; sp_line = line; sp_column = col }
type 'a document_outcome =
  {
  do_value: 'a ;
  do_prefixes: (Prims.string * Prims.string) Prims.list ;
  do_base: Prims.string ;
  do_error: (Prims.string * Prims.nat) FStar_Pervasives_Native.option }
let __proj__Mkdocument_outcome__item__do_value
  (projectee : 'a document_outcome) : 'a=
  match projectee with
  | { do_value; do_prefixes; do_base; do_error;_} -> do_value
let __proj__Mkdocument_outcome__item__do_prefixes
  (projectee : 'a document_outcome) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { do_value; do_prefixes; do_base; do_error;_} -> do_prefixes
let __proj__Mkdocument_outcome__item__do_base
  (projectee : 'a document_outcome) : Prims.string=
  match projectee with
  | { do_value; do_prefixes; do_base; do_error;_} -> do_base
let __proj__Mkdocument_outcome__item__do_error
  (projectee : 'a document_outcome) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  match projectee with
  | { do_value; do_prefixes; do_base; do_error;_} -> do_error
let turtle_document (mode : Parser_NTriples.rdf_syntax_mode)
  (input : Prims.string) (base : Prims.string) :
  RDF_Triple.triple Prims.list document_outcome=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (2)) in
  let seed =
    match mode with
    | Parser_NTriples.Mode_11 -> Parser_Turtle.empty_turtle_state
    | Parser_NTriples.Mode_12 -> Parser_Turtle.empty_turtle_state_12 in
  let st =
    {
      Parser_Turtle.prefixes = (seed.Parser_Turtle.prefixes);
      Parser_Turtle.base_iri = base;
      Parser_Turtle.bnode_counter = (seed.Parser_Turtle.bnode_counter);
      Parser_Turtle.ts_mode = (seed.Parser_Turtle.ts_mode)
    } in
  let r =
    Parser_Turtle.parse_turtle_doc st input Prims.int_zero []
      FStar_Pervasives_Native.None fuel in
  let triples =
    match mode with
    | Parser_NTriples.Mode_11 -> r.Parser_Turtle.tdr_triples
    | Parser_NTriples.Mode_12 ->
        RDF_Graph.graph_dedup_sort r.Parser_Turtle.tdr_triples in
  {
    do_value = triples;
    do_prefixes = ((r.Parser_Turtle.tdr_state).Parser_Turtle.prefixes);
    do_base = ((r.Parser_Turtle.tdr_state).Parser_Turtle.base_iri);
    do_error = (r.Parser_Turtle.tdr_error)
  }
let trig_document (mode : Parser_NTriples.rdf_syntax_mode)
  (input : Prims.string) (base : Prims.string) :
  RDF_Graph.rdf_dataset document_outcome=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (3)) in
  let seed =
    match mode with
    | Parser_NTriples.Mode_11 -> Parser_Turtle.empty_turtle_state
    | Parser_NTriples.Mode_12 -> Parser_Turtle.empty_turtle_state_12 in
  let st =
    {
      Parser_Turtle.prefixes = (seed.Parser_Turtle.prefixes);
      Parser_Turtle.base_iri = base;
      Parser_Turtle.bnode_counter = (seed.Parser_Turtle.bnode_counter);
      Parser_Turtle.ts_mode = (seed.Parser_Turtle.ts_mode)
    } in
  let tps = Parser_TriG.make_trig_parse_state st in
  let uu___ =
    Parser_TriG.parse_trig_doc tps input Prims.int_zero
      RDF_Graph.empty_dataset fuel in
  match uu___ with
  | (ds, tps') ->
      {
        do_value = (RDF_Graph_Executable.dataset_finalise ds);
        do_prefixes = ((tps'.Parser_TriG.ts).Parser_Turtle.prefixes);
        do_base = ((tps'.Parser_TriG.ts).Parser_Turtle.base_iri);
        do_error = (tps'.Parser_TriG.terr)
      }
let rec ntriples_diagnostic_acc (mode : Parser_NTriples.rdf_syntax_mode)
  (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Triple.triple Prims.list) (fuel : Prims.nat) :
  RDF_Triple.triple Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("fuel exhausted", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), len)
     else
       (let pos1 =
          match Parser_NTriples.pws input pos with
          | Parser_Combinators.ParseOk ((), p) -> p
          | uu___2 -> pos in
        if pos1 >= len
        then Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), len)
        else
          (let code =
             FStar_Char.int_of_char
               (Parser_FastString.fs_byte_index input pos1) in
           if code = (Prims.of_int (0x23))
           then
             let pos2 = Parser_NTriples.skip_comment input pos1 in
             let pos3 = Parser_NTriples.skip_eol input pos2 in
             (if pos3 = pos1
              then
                Parser_Combinators.ParseFail ("malformed comment line", pos1)
              else
                ntriples_diagnostic_acc mode input pos3 acc
                  (fuel - Prims.int_one))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then
               (let pos2 = Parser_NTriples.skip_eol input pos1 in
                if pos2 = pos1
                then
                  Parser_Combinators.ParseFail
                    ("malformed end of line", pos1)
                else
                  ntriples_diagnostic_acc mode input pos2 acc
                    (fuel - Prims.int_one))
             else
               (let triple_result =
                  match mode with
                  | Parser_NTriples.Mode_11 ->
                      Parser_NTriples.parse_triple input pos1
                  | Parser_NTriples.Mode_12 ->
                      Parser_NTriples.parse_triple_12 input pos1 in
                match triple_result with
                | Parser_Combinators.ParseOk (t, pos2) ->
                    let pos3 =
                      match Parser_NTriples.pws input pos2 with
                      | Parser_Combinators.ParseOk ((), p) -> p
                      | uu___5 -> pos2 in
                    let pos4 = Parser_NTriples.skip_comment input pos3 in
                    let pos5 = Parser_NTriples.skip_eol input pos4 in
                    if pos5 > pos4
                    then
                      ntriples_diagnostic_acc mode input pos5 (t :: acc)
                        (fuel - Prims.int_one)
                    else
                      if pos4 >= len
                      then
                        ntriples_diagnostic_acc mode input pos4 (t :: acc)
                          (fuel - Prims.int_one)
                      else
                        Parser_Combinators.ParseFail
                          ("expected end of line after statement", pos4)
                | Parser_Combinators.ParseFail (msg, fpos) ->
                    Parser_Combinators.ParseFail (msg, fpos)))))
let ntriples_diagnostic (mode : Parser_NTriples.rdf_syntax_mode)
  (input : Prims.string) :
  RDF_Triple.triple Prims.list Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  ntriples_diagnostic_acc mode input Prims.int_zero [] (len + Prims.int_one)
let rec nquads_diagnostic_acc (mode : Parser_NTriples.rdf_syntax_mode)
  (input : Prims.string) (pos : Prims.nat) (ds : RDF_Graph.rdf_dataset)
  (fuel : Prims.nat) : RDF_Graph.rdf_dataset Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("fuel exhausted", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseOk (ds, len)
     else
       (let pos1 =
          match Parser_NTriples.pws input pos with
          | Parser_Combinators.ParseOk ((), p) -> p
          | uu___2 -> pos in
        if pos1 >= len
        then Parser_Combinators.ParseOk (ds, len)
        else
          (let code =
             FStar_Char.int_of_char
               (Parser_FastString.fs_byte_index input pos1) in
           if code = (Prims.of_int (0x23))
           then
             let pos2 = Parser_NTriples.skip_comment input pos1 in
             let pos3 = Parser_NTriples.skip_eol input pos2 in
             (if pos3 = pos1
              then
                Parser_Combinators.ParseFail ("malformed comment line", pos1)
              else
                nquads_diagnostic_acc mode input pos3 ds
                  (fuel - Prims.int_one))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then
               (let pos2 = Parser_NTriples.skip_eol input pos1 in
                if pos2 = pos1
                then
                  Parser_Combinators.ParseFail
                    ("malformed end of line", pos1)
                else
                  nquads_diagnostic_acc mode input pos2 ds
                    (fuel - Prims.int_one))
             else
               (let quad_result =
                  match mode with
                  | Parser_NTriples.Mode_11 ->
                      Parser_NQuads.parse_nquad input pos1
                  | Parser_NTriples.Mode_12 ->
                      Parser_NQuads.parse_nquad_12 input pos1 in
                match quad_result with
                | Parser_Combinators.ParseOk ((t, graph_opt), pos2) ->
                    let ds' = Parser_NQuads.dataset_add_quad ds t graph_opt in
                    let pos3 =
                      match Parser_NTriples.pws input pos2 with
                      | Parser_Combinators.ParseOk ((), p) -> p
                      | uu___5 -> pos2 in
                    let pos4 = Parser_NTriples.skip_comment input pos3 in
                    let pos5 = Parser_NTriples.skip_eol input pos4 in
                    if pos5 > pos4
                    then
                      nquads_diagnostic_acc mode input pos5 ds'
                        (fuel - Prims.int_one)
                    else
                      if pos4 >= len
                      then
                        nquads_diagnostic_acc mode input pos4 ds'
                          (fuel - Prims.int_one)
                      else
                        Parser_Combinators.ParseFail
                          ("expected end of line after statement", pos4)
                | Parser_Combinators.ParseFail (msg, fpos) ->
                    Parser_Combinators.ParseFail (msg, fpos)))))
let nquads_diagnostic (mode : Parser_NTriples.rdf_syntax_mode)
  (input : Prims.string) :
  RDF_Graph.rdf_dataset Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  match nquads_diagnostic_acc mode input Prims.int_zero
          RDF_Graph.empty_dataset (len + Prims.int_one)
  with
  | Parser_Combinators.ParseOk (ds, pos) ->
      Parser_Combinators.ParseOk
        ((RDF_Graph_Executable.dataset_finalise ds), pos)
  | Parser_Combinators.ParseFail (msg, pos) ->
      Parser_Combinators.ParseFail (msg, pos)
