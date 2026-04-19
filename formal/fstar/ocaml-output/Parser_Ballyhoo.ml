open Prims
type ballyhoo_mode =
  | BM_NQuads 
let uu___is_BM_NQuads (projectee : ballyhoo_mode) : Prims.bool= true
type ballyhoo_error = {
  be_line: Prims.nat ;
  be_message: Prims.string }
let __proj__Mkballyhoo_error__item__be_line (projectee : ballyhoo_error) :
  Prims.nat= match projectee with | { be_line; be_message;_} -> be_line
let __proj__Mkballyhoo_error__item__be_message (projectee : ballyhoo_error) :
  Prims.string= match projectee with | { be_line; be_message;_} -> be_message
type ballyhoo_event =
  | BE_DefaultTriple of RDF_Graph_Executable.triple 
  | BE_NamedTriple of RDF_Graph_Executable.iri * RDF_Graph_Executable.triple 
let uu___is_BE_DefaultTriple (projectee : ballyhoo_event) : Prims.bool=
  match projectee with | BE_DefaultTriple _0 -> true | uu___ -> false
let __proj__BE_DefaultTriple__item___0 (projectee : ballyhoo_event) :
  RDF_Graph_Executable.triple=
  match projectee with | BE_DefaultTriple _0 -> _0
let uu___is_BE_NamedTriple (projectee : ballyhoo_event) : Prims.bool=
  match projectee with | BE_NamedTriple (_0, _1) -> true | uu___ -> false
let __proj__BE_NamedTriple__item___0 (projectee : ballyhoo_event) :
  RDF_Graph_Executable.iri=
  match projectee with | BE_NamedTriple (_0, _1) -> _0
let __proj__BE_NamedTriple__item___1 (projectee : ballyhoo_event) :
  RDF_Graph_Executable.triple=
  match projectee with | BE_NamedTriple (_0, _1) -> _1
type ballyhoo_state =
  {
  bs_mode: ballyhoo_mode ;
  bs_carry: Prims.string ;
  bs_line_no: Prims.nat ;
  bs_events_rev: ballyhoo_event Prims.list ;
  bs_errors_rev: ballyhoo_error Prims.list ;
  bs_lines_ok: Prims.nat ;
  bs_lines_failed: Prims.nat }
let __proj__Mkballyhoo_state__item__bs_mode (projectee : ballyhoo_state) :
  ballyhoo_mode=
  match projectee with
  | { bs_mode; bs_carry; bs_line_no; bs_events_rev; bs_errors_rev;
      bs_lines_ok; bs_lines_failed;_} -> bs_mode
let __proj__Mkballyhoo_state__item__bs_carry (projectee : ballyhoo_state) :
  Prims.string=
  match projectee with
  | { bs_mode; bs_carry; bs_line_no; bs_events_rev; bs_errors_rev;
      bs_lines_ok; bs_lines_failed;_} -> bs_carry
let __proj__Mkballyhoo_state__item__bs_line_no (projectee : ballyhoo_state) :
  Prims.nat=
  match projectee with
  | { bs_mode; bs_carry; bs_line_no; bs_events_rev; bs_errors_rev;
      bs_lines_ok; bs_lines_failed;_} -> bs_line_no
let __proj__Mkballyhoo_state__item__bs_events_rev
  (projectee : ballyhoo_state) : ballyhoo_event Prims.list=
  match projectee with
  | { bs_mode; bs_carry; bs_line_no; bs_events_rev; bs_errors_rev;
      bs_lines_ok; bs_lines_failed;_} -> bs_events_rev
let __proj__Mkballyhoo_state__item__bs_errors_rev
  (projectee : ballyhoo_state) : ballyhoo_error Prims.list=
  match projectee with
  | { bs_mode; bs_carry; bs_line_no; bs_events_rev; bs_errors_rev;
      bs_lines_ok; bs_lines_failed;_} -> bs_errors_rev
let __proj__Mkballyhoo_state__item__bs_lines_ok (projectee : ballyhoo_state)
  : Prims.nat=
  match projectee with
  | { bs_mode; bs_carry; bs_line_no; bs_events_rev; bs_errors_rev;
      bs_lines_ok; bs_lines_failed;_} -> bs_lines_ok
let __proj__Mkballyhoo_state__item__bs_lines_failed
  (projectee : ballyhoo_state) : Prims.nat=
  match projectee with
  | { bs_mode; bs_carry; bs_line_no; bs_events_rev; bs_errors_rev;
      bs_lines_ok; bs_lines_failed;_} -> bs_lines_failed
let empty_ballyhoo_state : ballyhoo_state=
  {
    bs_mode = BM_NQuads;
    bs_carry = "";
    bs_line_no = Prims.int_one;
    bs_events_rev = [];
    bs_errors_rev = [];
    bs_lines_ok = Prims.int_zero;
    bs_lines_failed = Prims.int_zero
  }
let append_carry (st : ballyhoo_state) (chunk : Prims.string) : Prims.string=
  if (FStar_String.strlen st.bs_carry) = Prims.int_zero
  then chunk
  else FStar_String.concat "" [st.bs_carry; chunk]
let is_inline_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))
let rec skip_inline_ws (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then pos
     else
       if is_inline_ws (FStar_String.index input pos)
       then skip_inline_ws input (pos + Prims.int_one) (fuel - Prims.int_one)
       else pos)
let skip_inline_ws0 (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let len = FStar_String.strlen input in
  if pos <= len
  then skip_inline_ws input pos ((len - pos) + Prims.int_one)
  else pos
let rec find_line_end (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then pos
     else
       (let code = FStar_Char.int_of_char (FStar_String.index input pos) in
        if (code = (Prims.of_int (0x0A))) || (code = (Prims.of_int (0x0D)))
        then pos
        else find_line_end input (pos + Prims.int_one) (fuel - Prims.int_one)))
let consume_eol (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let len = FStar_String.strlen input in
  if pos >= len
  then pos
  else
    (let c0 = FStar_Char.int_of_char (FStar_String.index input pos) in
     if c0 = (Prims.of_int (0x0D))
     then
       (if
          ((pos + Prims.int_one) < len) &&
            ((FStar_Char.int_of_char
                (FStar_String.index input (pos + Prims.int_one)))
               = (Prims.of_int (0x0A)))
        then pos + (Prims.of_int (2))
        else pos + Prims.int_one)
     else if c0 = (Prims.of_int (0x0A)) then pos + Prims.int_one else pos)
let line_sub (input : Prims.string) (start_pos : Prims.nat)
  (end_pos : Prims.nat) : Prims.string=
  if (end_pos >= start_pos) && (end_pos <= (FStar_String.strlen input))
  then FStar_String.sub input start_pos (end_pos - start_pos)
  else ""
let add_event (st : ballyhoo_state) (t : RDF_Graph_Executable.triple)
  (graph_opt : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  ballyhoo_state=
  let ev =
    match graph_opt with
    | FStar_Pervasives_Native.None -> BE_DefaultTriple t
    | FStar_Pervasives_Native.Some g -> BE_NamedTriple (g, t) in
  {
    bs_mode = (st.bs_mode);
    bs_carry = (st.bs_carry);
    bs_line_no = (st.bs_line_no + Prims.int_one);
    bs_events_rev = (ev :: (st.bs_events_rev));
    bs_errors_rev = (st.bs_errors_rev);
    bs_lines_ok = (st.bs_lines_ok + Prims.int_one);
    bs_lines_failed = (st.bs_lines_failed)
  }
let add_error (st : ballyhoo_state) (msg : Prims.string) : ballyhoo_state=
  let err = { be_line = (st.bs_line_no); be_message = msg } in
  {
    bs_mode = (st.bs_mode);
    bs_carry = (st.bs_carry);
    bs_line_no = (st.bs_line_no + Prims.int_one);
    bs_events_rev = (st.bs_events_rev);
    bs_errors_rev = (err :: (st.bs_errors_rev));
    bs_lines_ok = (st.bs_lines_ok);
    bs_lines_failed = (st.bs_lines_failed + Prims.int_one)
  }
let finish_line_parse (line : Prims.string) (pos : Prims.nat) : Prims.bool=
  let pos1 = skip_inline_ws0 line pos in
  let len = FStar_String.strlen line in
  if pos1 >= len
  then true
  else
    (FStar_Char.int_of_char (FStar_String.index line pos1)) =
      (Prims.of_int (0x23))
let parse_nquads_line (st : ballyhoo_state) (line : Prims.string) :
  ballyhoo_state=
  let pos0 = skip_inline_ws0 line Prims.int_zero in
  let len = FStar_String.strlen line in
  if pos0 >= len
  then
    {
      bs_mode = (st.bs_mode);
      bs_carry = (st.bs_carry);
      bs_line_no = (st.bs_line_no + Prims.int_one);
      bs_events_rev = (st.bs_events_rev);
      bs_errors_rev = (st.bs_errors_rev);
      bs_lines_ok = (st.bs_lines_ok);
      bs_lines_failed = (st.bs_lines_failed)
    }
  else
    (let code = FStar_Char.int_of_char (FStar_String.index line pos0) in
     if code = (Prims.of_int (0x23))
     then
       {
         bs_mode = (st.bs_mode);
         bs_carry = (st.bs_carry);
         bs_line_no = (st.bs_line_no + Prims.int_one);
         bs_events_rev = (st.bs_events_rev);
         bs_errors_rev = (st.bs_errors_rev);
         bs_lines_ok = (st.bs_lines_ok);
         bs_lines_failed = (st.bs_lines_failed)
       }
     else
       (match Parser_NQuads.parse_nquad line pos0 with
        | Parser_Combinators.ParseOk ((t, graph_opt), pos1) ->
            if finish_line_parse line pos1
            then add_event st t graph_opt
            else add_error st "trailing data after parsed quad"
        | Parser_Combinators.ParseFail (msg, uu___2) -> add_error st msg))
let rec feed_complete_lines (input : Prims.string) (pos : Prims.nat)
  (st : ballyhoo_state) (fuel : Prims.nat) : ballyhoo_state=
  if fuel = Prims.int_zero
  then
    {
      bs_mode = (st.bs_mode);
      bs_carry = (line_sub input pos (FStar_String.strlen input));
      bs_line_no = (st.bs_line_no);
      bs_events_rev = (st.bs_events_rev);
      bs_errors_rev = (st.bs_errors_rev);
      bs_lines_ok = (st.bs_lines_ok);
      bs_lines_failed = (st.bs_lines_failed)
    }
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then
       {
         bs_mode = (st.bs_mode);
         bs_carry = "";
         bs_line_no = (st.bs_line_no);
         bs_events_rev = (st.bs_events_rev);
         bs_errors_rev = (st.bs_errors_rev);
         bs_lines_ok = (st.bs_lines_ok);
         bs_lines_failed = (st.bs_lines_failed)
       }
     else
       (let line_end = find_line_end input pos ((len - pos) + Prims.int_one) in
        if line_end >= len
        then
          {
            bs_mode = (st.bs_mode);
            bs_carry = (line_sub input pos len);
            bs_line_no = (st.bs_line_no);
            bs_events_rev = (st.bs_events_rev);
            bs_errors_rev = (st.bs_errors_rev);
            bs_lines_ok = (st.bs_lines_ok);
            bs_lines_failed = (st.bs_lines_failed)
          }
        else
          (let line = line_sub input pos line_end in
           let st' = parse_nquads_line st line in
           let next_pos = consume_eol input line_end in
           if next_pos > pos
           then feed_complete_lines input next_pos st' (fuel - Prims.int_one)
           else
             {
               bs_mode = (st'.bs_mode);
               bs_carry = (line_sub input pos len);
               bs_line_no = (st'.bs_line_no);
               bs_events_rev = (st'.bs_events_rev);
               bs_errors_rev = (st'.bs_errors_rev);
               bs_lines_ok = (st'.bs_lines_ok);
               bs_lines_failed = (st'.bs_lines_failed)
             })))
let feed_ballyhoo_nquads_chunk (st : ballyhoo_state) (chunk : Prims.string) :
  ballyhoo_state=
  let input = append_carry st chunk in
  let len = FStar_String.strlen input in
  let st0 =
    {
      bs_mode = (st.bs_mode);
      bs_carry = "";
      bs_line_no = (st.bs_line_no);
      bs_events_rev = (st.bs_events_rev);
      bs_errors_rev = (st.bs_errors_rev);
      bs_lines_ok = (st.bs_lines_ok);
      bs_lines_failed = (st.bs_lines_failed)
    } in
  feed_complete_lines input Prims.int_zero st0 (len + Prims.int_one)
let finish_ballyhoo_nquads (st : ballyhoo_state) : ballyhoo_state=
  if (FStar_String.strlen st.bs_carry) = Prims.int_zero
  then st
  else
    (let carry = st.bs_carry in
     let st0 =
       {
         bs_mode = (st.bs_mode);
         bs_carry = "";
         bs_line_no = (st.bs_line_no);
         bs_events_rev = (st.bs_events_rev);
         bs_errors_rev = (st.bs_errors_rev);
         bs_lines_ok = (st.bs_lines_ok);
         bs_lines_failed = (st.bs_lines_failed)
       } in
     parse_nquads_line st0 carry)
let ballyhoo_events (st : ballyhoo_state) : ballyhoo_event Prims.list=
  FStar_List_Tot_Base.rev st.bs_events_rev
let ballyhoo_errors (st : ballyhoo_state) : ballyhoo_error Prims.list=
  FStar_List_Tot_Base.rev st.bs_errors_rev
let dataset_add_ballyhoo_event (ds : RDF_Graph_Executable.rdf_dataset)
  (ev : ballyhoo_event) : RDF_Graph_Executable.rdf_dataset=
  match ev with
  | BE_DefaultTriple t ->
      {
        RDF_Graph_Executable.ds_default =
          (RDF_Graph_Executable.graph_add t
             ds.RDF_Graph_Executable.ds_default);
        RDF_Graph_Executable.ds_named = (ds.RDF_Graph_Executable.ds_named)
      }
  | BE_NamedTriple (g, t) ->
      let rec update_named ngs =
        match ngs with
        | [] ->
            [{
               RDF_Graph_Executable.ng_name = g;
               RDF_Graph_Executable.ng_graph = [t]
             }]
        | ng::rest ->
            if ng.RDF_Graph_Executable.ng_name = g
            then
              {
                RDF_Graph_Executable.ng_name = g;
                RDF_Graph_Executable.ng_graph =
                  (RDF_Graph_Executable.graph_add t
                     ng.RDF_Graph_Executable.ng_graph)
              } :: rest
            else ng :: (update_named rest) in
      {
        RDF_Graph_Executable.ds_default =
          (ds.RDF_Graph_Executable.ds_default);
        RDF_Graph_Executable.ds_named =
          (update_named ds.RDF_Graph_Executable.ds_named)
      }
let rec dataset_of_events_acc (evs : ballyhoo_event Prims.list)
  (ds : RDF_Graph_Executable.rdf_dataset) : RDF_Graph_Executable.rdf_dataset=
  match evs with
  | [] -> ds
  | ev::rest -> dataset_of_events_acc rest (dataset_add_ballyhoo_event ds ev)
let dataset_of_ballyhoo_events (evs : ballyhoo_event Prims.list) :
  RDF_Graph_Executable.rdf_dataset=
  dataset_of_events_acc evs RDF_Graph_Executable.empty_dataset
let parse_ballyhoo_nquads (input : Prims.string) : ballyhoo_state=
  finish_ballyhoo_nquads
    (feed_ballyhoo_nquads_chunk empty_ballyhoo_state input)
