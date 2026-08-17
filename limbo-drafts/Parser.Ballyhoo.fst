module Parser.Ballyhoo

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open Parser.Combinators
open Parser.NQuads

// Ballyhoo is an experimental parser path.
// It does not replace the current more compliant parsers.
// The purpose is to explore a streaming, chunk-oriented ingestion architecture
// that plugs into the RDF core independently.

noeq type ballyhoo_mode =
  | BM_NQuads

noeq type ballyhoo_error = {
  be_line: nat;
  be_message: string;
}

noeq type ballyhoo_event =
  | BE_DefaultTriple : triple -> ballyhoo_event
  | BE_NamedTriple : iri -> triple -> ballyhoo_event

noeq type ballyhoo_state = {
  bs_mode: ballyhoo_mode;
  bs_carry: string;
  bs_line_no: nat;
  bs_events_rev: list ballyhoo_event;
  bs_errors_rev: list ballyhoo_error;
  bs_lines_ok: nat;
  bs_lines_failed: nat;
}

let empty_ballyhoo_state : ballyhoo_state = {
  bs_mode = BM_NQuads;
  bs_carry = "";
  bs_line_no = 1;
  bs_events_rev = [];
  bs_errors_rev = [];
  bs_lines_ok = 0;
  bs_lines_failed = 0;
}

let append_carry (st: ballyhoo_state) (chunk: string) : string =
  if String.length st.bs_carry = 0 then chunk
  else String.concat "" [st.bs_carry; chunk]

let is_inline_ws (c: FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x20 || code = 0x09

let rec skip_inline_ws (input: string) (pos: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else if is_inline_ws (String.index input pos) then
      skip_inline_ws input (pos + 1) (fuel - 1)
    else
      pos

let skip_inline_ws0 (input: string) (pos: nat) : nat =
  let len = String.length input in
  if pos <= len then skip_inline_ws input pos (len - pos + 1) else pos

let rec find_line_end (input: string) (pos: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let code = FStar.Char.int_of_char (String.index input pos) in
      if code = 0x0A || code = 0x0D then pos
      else find_line_end input (pos + 1) (fuel - 1)

let consume_eol (input: string) (pos: nat) : nat =
  let len = String.length input in
  if pos >= len then pos
  else
    let c0 = FStar.Char.int_of_char (String.index input pos) in
    if c0 = 0x0D then
      if pos + 1 < len && FStar.Char.int_of_char (String.index input (pos + 1)) = 0x0A
      then pos + 2
      else pos + 1
    else if c0 = 0x0A then pos + 1
    else pos

let line_sub (input: string) (start_pos: nat) (end_pos: nat) : string =
  if end_pos >= start_pos && end_pos <= String.length input then
    String.sub input start_pos (end_pos - start_pos)
  else
    ""

let add_event (st: ballyhoo_state) (t: triple) (graph_opt: option iri) : ballyhoo_state =
  let ev =
    match graph_opt with
    | None -> BE_DefaultTriple t
    | Some g -> BE_NamedTriple g t
  in
  { st with
      bs_events_rev = ev :: st.bs_events_rev;
      bs_lines_ok = st.bs_lines_ok + 1;
      bs_line_no = st.bs_line_no + 1; }

let add_error (st: ballyhoo_state) (msg: string) : ballyhoo_state =
  let err = { be_line = st.bs_line_no; be_message = msg } in
  { st with
      bs_errors_rev = err :: st.bs_errors_rev;
      bs_lines_failed = st.bs_lines_failed + 1;
      bs_line_no = st.bs_line_no + 1; }

let finish_line_parse (line: string) (pos: nat) : bool =
  let pos1 = skip_inline_ws0 line pos in
  let len = String.length line in
  if pos1 >= len then true
  else FStar.Char.int_of_char (String.index line pos1) = 0x23

let parse_nquads_line (st: ballyhoo_state) (line: string) : ballyhoo_state =
  let pos0 = skip_inline_ws0 line 0 in
  let len = String.length line in
  if pos0 >= len then
    { st with bs_line_no = st.bs_line_no + 1 }
  else
    let code = FStar.Char.int_of_char (String.index line pos0) in
    if code = 0x23 then
      { st with bs_line_no = st.bs_line_no + 1 }
    else
      match parse_nquad line pos0 with
      | ParseOk (t, graph_opt) pos1 ->
        if finish_line_parse line pos1 then add_event st t graph_opt
        else add_error st "trailing data after parsed quad"
      | ParseFail msg _ -> add_error st msg

let rec feed_complete_lines (input: string) (pos: nat) (st: ballyhoo_state) (fuel: nat)
  : Tot ballyhoo_state (decreases fuel) =
  if fuel = 0 then { st with bs_carry = line_sub input pos (String.length input) }
  else
    let len = String.length input in
    if pos >= len then { st with bs_carry = "" }
    else
      let line_end = find_line_end input pos (len - pos + 1) in
      if line_end >= len then
        { st with bs_carry = line_sub input pos len }
      else
        let line = line_sub input pos line_end in
        let st' = parse_nquads_line st line in
        let next_pos = consume_eol input line_end in
        if next_pos > pos then feed_complete_lines input next_pos st' (fuel - 1)
        else { st' with bs_carry = line_sub input pos len }

let feed_ballyhoo_nquads_chunk (st: ballyhoo_state) (chunk: string) : ballyhoo_state =
  let input = append_carry st chunk in
  let len = String.length input in
  let st0 = { st with bs_carry = "" } in
  feed_complete_lines input 0 st0 (len + 1)

let finish_ballyhoo_nquads (st: ballyhoo_state) : ballyhoo_state =
  if String.length st.bs_carry = 0 then st
  else
    let carry = st.bs_carry in
    let st0 = { st with bs_carry = "" } in
    parse_nquads_line st0 carry

let ballyhoo_events (st: ballyhoo_state) : list ballyhoo_event =
  List.Tot.rev st.bs_events_rev

let ballyhoo_errors (st: ballyhoo_state) : list ballyhoo_error =
  List.Tot.rev st.bs_errors_rev

let dataset_add_ballyhoo_event (ds: rdf_dataset) (ev: ballyhoo_event) : rdf_dataset =
  match ev with
  | BE_DefaultTriple t ->
    { ds with ds_default = graph_add t ds.ds_default }
  | BE_NamedTriple g t ->
    let rec update_named (ngs: list named_graph) : list named_graph =
      match ngs with
      | [] -> [{ ng_name = g; ng_graph = [t] }]
      | ng :: rest ->
        if ng.ng_name = g then
          { ng_name = g; ng_graph = graph_add t ng.ng_graph } :: rest
        else
          ng :: update_named rest
    in
    { ds with ds_named = update_named ds.ds_named }

let rec dataset_of_events_acc (evs: list ballyhoo_event) (ds: rdf_dataset)
  : Tot rdf_dataset (decreases evs) =
  match evs with
  | [] -> ds
  | ev :: rest -> dataset_of_events_acc rest (dataset_add_ballyhoo_event ds ev)

let dataset_of_ballyhoo_events (evs: list ballyhoo_event) : rdf_dataset =
  dataset_of_events_acc evs empty_dataset

let parse_ballyhoo_nquads (input: string) : ballyhoo_state =
  finish_ballyhoo_nquads (feed_ballyhoo_nquads_chunk empty_ballyhoo_state input)

