module Parser.TriG

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.Combinators
open Parser.NTriples
open Parser.Turtle
open RDF.Graph.Executable

(* ================================================================ *)
(* TriG Parser                                                       *)
(*                                                                   *)
(* TriG extends Turtle with named graphs. A TriG document contains:  *)
(*   - Prefix/base directives (same as Turtle)                       *)
(*   - Triples in the default graph (same as Turtle)                 *)
(*   - Named graph blocks:  IRI { triples }                          *)
(*   - Named graph blocks:  GRAPH IRI { triples }                    *)
(*   - Default graph block: { triples }                              *)
(*   - Default graph block: GRAPH { triples }  (invalid per spec)    *)
(*   - Blank node graph names: _:bnode { triples }                   *)
(*                                                                   *)
(* W3C spec: https://www.w3.org/TR/trig/                             *)
(* ================================================================ *)

(* ================================================================ *)
(* Dataset construction helpers                                      *)
(* (Same pattern as Parser.NQuads)                                   *)
(* ================================================================ *)

(** Find a named graph in the list, returning split context *)
let rec trig_find_named_graph (name : iri) (ngs : list named_graph)
  : option (list named_graph & rdf_graph & list named_graph) =
  match ngs with
  | [] -> None
  | ng :: rest ->
    if ng.ng_name = name then
      Some ([], ng.ng_graph, rest)
    else
      match trig_find_named_graph name rest with
      | Some (before, g, after) -> Some (ng :: before, g, after)
      | None -> None

(** Add a triple to the appropriate graph in the dataset *)
let trig_dataset_add (ds : rdf_dataset) (t : triple) (graph_name : option iri) : rdf_dataset =
  match graph_name with
  | None ->
    { ds with ds_default = graph_add t ds.ds_default }
  | Some name ->
    match trig_find_named_graph name ds.ds_named with
    | Some (before, existing_g, after) ->
      let updated_g = graph_add t existing_g in
      let updated_ng : named_graph = { ng_name = name; ng_graph = updated_g } in
      { ds with ds_named = List.Tot.append before (List.Tot.append [updated_ng] after) }
    | None ->
      let new_ng : named_graph = { ng_name = name; ng_graph = [t] } in
      { ds with ds_named = List.Tot.append ds.ds_named [new_ng] }

(** Add a list of triples to the appropriate graph *)
let rec trig_dataset_add_triples (ds : rdf_dataset) (triples : list triple) (graph_name : option iri)
  : rdf_dataset =
  match triples with
  | [] -> ds
  | t :: rest -> trig_dataset_add_triples (trig_dataset_add ds t graph_name) rest graph_name

(* ================================================================ *)
(* TriG graph name parser                                            *)
(* ================================================================ *)

(** Parse a graph name: IRI, prefixed name, or blank node.
    Returns (graph_iri, updated_state). *)
let parse_trig_graph_name (st: turtle_state) (input: string) (pos: nat)
  : parse_result (iri & turtle_state) =
  let len = String.length input in
  if pos >= len then ParseFail "expected graph name" pos
  else
    let c = String.index input pos in
    let code = int_of_char c in
    if code = 0x5F then (* '_' — blank node graph name *)
      begin match parse_bnode input pos with
      | ParseOk b pos' ->
        let bnode_iri = String.concat "" ["_:"; b] in
        ParseOk (bnode_iri, st) pos'
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    else
      (* Try IRI (full or prefixed) *)
      begin match parse_turtle_iri st input pos with
      | ParseOk i pos' -> ParseOk (i, st) pos'
      | ParseFail msg fpos -> ParseFail msg fpos
      end

(* ================================================================ *)
(* Case-insensitive keyword matching for GRAPH                       *)
(* ================================================================ *)

let char_to_lower (c: char) : char =
  let code = int_of_char c in
  if code >= 0x41 && code <= 0x5A then char_of_int (code + 32)
  else c

(** Check if input starting at pos matches "graph" case-insensitively,
    followed by a non-PN_CHARS character (whitespace, '{', etc.) *)
let is_graph_keyword (input: string) (pos: nat) : bool =
  let len = String.length input in
  if pos + 5 > len then false
  else
    let c0 = char_to_lower (String.index input pos) in
    let c1 = char_to_lower (String.index input (pos + 1)) in
    let c2 = char_to_lower (String.index input (pos + 2)) in
    let c3 = char_to_lower (String.index input (pos + 3)) in
    let c4 = char_to_lower (String.index input (pos + 4)) in
    if int_of_char c0 = 0x67 &&    (* g *)
       int_of_char c1 = 0x72 &&    (* r *)
       int_of_char c2 = 0x61 &&    (* a *)
       int_of_char c3 = 0x70 &&    (* p *)
       int_of_char c4 = 0x68       (* h *)
    then
      (* Must be followed by non-pn_chars character or end of input *)
      if pos + 5 >= len then true
      else
        let next = String.index input (pos + 5) in
        not (is_pn_chars next)
    else false

(* ================================================================ *)
(* Turtle content inside graph blocks                                *)
(*                                                                   *)
(* Inside { ... }, the content is standard Turtle (triples,          *)
(* directives, etc.) terminated by '}'.                              *)
(* ================================================================ *)

(** Parse the body of a graph block: Turtle statements until '}'.
    Returns (triples, updated_state). *)
let rec parse_graph_body (st: turtle_state) (input: string) (pos: nat)
    (acc: list triple) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc, st) pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseFail "unterminated graph block, expected '}'" pos1
      else
        let c = String.index input pos1 in
        let code = int_of_char c in
        if code = 0x7D then (* '}' — end of graph block *)
          ParseOk (List.Tot.rev acc, st) (pos1 + 1)
        else
          (* Try to parse a Turtle statement *)
          begin match parse_turtle_statement st input pos1 fuel with
          | ParseOk (triples, st') pos2 ->
            if pos2 = pos1 then
              (* No progress — stop *)
              ParseOk (List.Tot.rev (List.Tot.append (List.Tot.rev triples) acc), st') pos2
            else
              parse_graph_body st' input pos2
                (List.Tot.append (List.Tot.rev triples) acc) (fuel - 1)
          | ParseFail _ _ ->
            (* On failure, skip to next line and try again *)
            let rec skip_line (p: nat) (f: nat) : Tot nat (decreases f) =
              if f = 0 then p
              else if p >= len then p
              else
                let ch = String.index input p in
                let cd = int_of_char ch in
                if cd = 0x0A || cd = 0x0D then p + 1
                else if cd = 0x7D then p  (* Don't skip past '}' *)
                else skip_line (p + 1) (f - 1)
            in
            let pos2 = skip_line pos1 (len - pos1) in
            if pos2 = pos1 then
              ParseOk (List.Tot.rev acc, st) pos1
            else
              parse_graph_body st input pos2 acc (fuel - 1)
          end

(* ================================================================ *)
(* Top-level TriG statement parser                                   *)
(* ================================================================ *)

(** Parse a single top-level TriG statement.
    A TriG statement is one of:
    1. A prefix/base directive (same as Turtle)
    2. A triples statement in the default graph (same as Turtle)
    3. A named graph block: graphName { ... }
    4. A GRAPH keyword block: GRAPH graphName { ... }
    5. A bare graph block: { ... }  (default graph)

    Returns (dataset_delta, updated_state) where dataset_delta is a list of
    (graph_name_option, triples) pairs. *)
let parse_trig_statement (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list (option iri & list triple) & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseOk ([], st) pos1
      else
        let c = String.index input pos1 in
        let code = int_of_char c in
        (* Case 1: Prefix directive *)
        begin match parse_prefix_directive input pos1 with
        | ParseOk (prefix, iri_val) pos2 ->
          let new_prefixes = (prefix, iri_val) :: st.prefixes in
          ParseOk ([], { st with prefixes = new_prefixes }) pos2
        | ParseFail _ _ ->
          (* Case 2: Base directive *)
          begin match parse_base_directive input pos1 with
          | ParseOk base_val pos2 ->
            ParseOk ([], { st with base_iri = base_val }) pos2
          | ParseFail _ _ ->
            (* Case 3: Bare graph block { ... } — triples go to default graph *)
            if code = 0x7B then
              begin match parse_graph_body st input (pos1 + 1) [] fuel with
              | ParseOk (triples, st') pos2 ->
                ParseOk ([(None, triples)], st') pos2
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            (* Case 4: GRAPH keyword *)
            else if is_graph_keyword input pos1 then
              begin match turtle_ws input (pos1 + 5) with
              | ParseOk () pos2 ->
                if pos2 >= len then ParseFail "expected graph name or '{' after GRAPH" pos2
                else
                  let c2 = String.index input pos2 in
                  let code2 = int_of_char c2 in
                  if code2 = 0x7B then
                    (* GRAPH { ... } — default graph *)
                    begin match parse_graph_body st input (pos2 + 1) [] fuel with
                    | ParseOk (triples, st') pos3 ->
                      ParseOk ([(None, triples)], st') pos3
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
                  else
                    (* GRAPH graphName { ... } *)
                    begin match parse_trig_graph_name st input pos2 with
                    | ParseOk (gname, st2) pos3 ->
                      begin match turtle_ws input pos3 with
                      | ParseOk () pos4 ->
                        if pos4 >= len then ParseFail "expected '{'" pos4
                        else if int_of_char (String.index input pos4) = 0x7B then
                          begin match parse_graph_body st2 input (pos4 + 1) [] fuel with
                          | ParseOk (triples, st3) pos5 ->
                            ParseOk ([(Some gname, triples)], st3) pos5
                          | ParseFail msg fpos -> ParseFail msg fpos
                          end
                        else
                          ParseFail "expected '{' after graph name" pos4
                      end
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
              end
            else
              (* Case 5: Could be graphName { ... } or regular Turtle triples.
                 We try to parse an IRI/bnode and then check if '{' follows. *)
              begin match parse_trig_graph_name st input pos1 with
              | ParseOk (candidate_name, st2) pos2 ->
                begin match turtle_ws input pos2 with
                | ParseOk () pos3 ->
                  if pos3 < len && int_of_char (String.index input pos3) = 0x7B then
                    (* It's a named graph block: name { ... } *)
                    begin match parse_graph_body st2 input (pos3 + 1) [] fuel with
                    | ParseOk (triples, st3) pos4 ->
                      ParseOk ([(Some candidate_name, triples)], st3) pos4
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
                  else
                    (* Not followed by '{' — this is a regular Turtle triples statement.
                       We already consumed the subject (the IRI/bnode), so we need to parse
                       the predicate-object list. The candidate_name is actually the subject IRI. *)
                    let subj : subject =
                      (* Check if candidate_name starts with "_:" for blank node *)
                      if String.length candidate_name >= 2 then
                        let c0 = String.index candidate_name 0 in
                        let c1 = String.index candidate_name 1 in
                        if int_of_char c0 = 0x5F && int_of_char c1 = 0x3A then
                          (* It's a blank node — strip the "_:" prefix *)
                          let bname = if String.length candidate_name > 2
                                      then String.sub candidate_name 2 (String.length candidate_name - 2)
                                      else "" in
                          S_BNode bname
                        else
                          S_IRI candidate_name
                      else
                        S_IRI candidate_name
                    in
                    begin match parse_predicate_object_list st2 subj input pos3 (fuel - 1) with
                    | ParseOk (po_triples, st3) pos4 ->
                      (* Expect optional '.' *)
                      begin match turtle_ws input pos4 with
                      | ParseOk () pos5 ->
                        let pos6 =
                          if pos5 < len && int_of_char (String.index input pos5) = 0x2E
                          then pos5 + 1
                          else pos5
                        in
                        ParseOk ([(None, po_triples)], st3) pos6
                      end
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
                end
              | ParseFail _ _ ->
                (* Case 6: Other Turtle constructs (blank node subjects like [], (), etc.) *)
                begin match parse_turtle_statement st input pos1 fuel with
                | ParseOk (triples, st') pos2 ->
                  ParseOk ([(None, triples)], st') pos2
                | ParseFail msg fpos -> ParseFail msg fpos
                end
              end
          end
        end

(* ================================================================ *)
(* Full TriG document parser                                         *)
(* ================================================================ *)

(** Parse the full TriG document, accumulating into an rdf_dataset *)
let rec parse_trig_doc (st: turtle_state) (input: string) (pos: nat)
    (ds: rdf_dataset) (fuel: nat)
  : Tot (rdf_dataset & turtle_state) (decreases fuel) =
  if fuel = 0 then (ds, st)
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then (ds, st)
      else
        begin match parse_trig_statement st input pos1 fuel with
        | ParseOk (deltas, st') pos2 ->
          if pos2 = pos1 then
            (* No progress — stop *)
            let ds' = List.Tot.fold_left
              (fun (acc : rdf_dataset) (delta : option iri & list triple) ->
                let (gname, triples) = delta in
                trig_dataset_add_triples acc triples gname)
              ds deltas
            in
            (ds', st')
          else
            let ds' = List.Tot.fold_left
              (fun (acc : rdf_dataset) (delta : option iri & list triple) ->
                let (gname, triples) = delta in
                trig_dataset_add_triples acc triples gname)
              ds deltas
            in
            parse_trig_doc st' input pos2 ds' (fuel - 1)
        | ParseFail _ _ ->
          (* Skip to next line on failure *)
          let rec skip_line (p: nat) (f: nat) : Tot nat (decreases f) =
            if f = 0 then p
            else if p >= len then p
            else
              let ch = String.index input p in
              let cd = int_of_char ch in
              if cd = 0x0A || cd = 0x0D then p + 1
              else skip_line (p + 1) (f - 1)
          in
          let pos2 = skip_line pos1 (len - pos1) in
          if pos2 = pos1 then (ds, st)
          else parse_trig_doc st input pos2 ds (fuel - 1)
        end

(* ================================================================ *)
(* Entry points                                                      *)
(* ================================================================ *)

(** Parse a TriG document string into an rdf_dataset *)
let parse_trig (input: string) : rdf_dataset =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 3 in
  let (ds, _) = parse_trig_doc empty_turtle_state input 0 empty_dataset fuel in
  ds

(** Parse a TriG document with a base IRI *)
let parse_trig_with_base (input: string) (base: string) : rdf_dataset =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 3 in
  let st = { empty_turtle_state with base_iri = base } in
  let (ds, _) = parse_trig_doc st input 0 empty_dataset fuel in
  ds
