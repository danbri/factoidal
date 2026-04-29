module Parser.NQuads

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.Combinators
open RDF.Graph.Executable
open Parser.NTriples

// Issue #70: byte-indexed string primitives on the hot path.
// See Parser.FastString.fst.

(* ================================================================ *)
(* N-Quads Parser                                                    *)
(*                                                                   *)
(* N-Quads extends N-Triples with an optional 4th element (graph     *)
(* name). Format:                                                    *)
(*   subject predicate object graphLabel? '.'                        *)
(* Graph labels can be IRIs <...> or blank nodes _:label.            *)
(* If the graph label is absent, the triple goes into the default    *)
(* graph; otherwise it goes into the named graph.                    *)
(*                                                                   *)
(* W3C spec: https://www.w3.org/TR/n-quads/                          *)
(* ================================================================ *)

(* ================================================================ *)
(* Graph label parser: IRI or blank node (optional 4th element)      *)
(* ================================================================ *)

(** Parse a graph label — either an IRI or a blank node.
    Returns the graph name as an `iri` (string).

    Per W3C N-Quads §2.1 the graph slot may carry a blank-node label
    (`_:bN`). The `named_graph.ng_name` field is typed as `iri` (a
    `string`) — there is no sum type to discriminate IRI vs. bnode at
    the type level. We use a sentinel encoding: blank-node graph
    names are stored as the literal string `"_:<label>"` (with the
    leading "_:") inside the iri slot. The canonical N-Quads
    serialiser in `RDF.Canonical.fst` (`canon_graph_name`) detects
    this prefix and emits the slot as a bnode rather than wrapping
    it as `<_:label>`. See
    `docs/designissues/2026-04-25-nquads-bnode-graph-fix.md`. *)
let parse_graph_label : parser iri =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected graph label" pos
    else
      let ch = fs_byte_index input pos in
      let code = FStar.Char.int_of_char ch in
      if code = 0x3C then (* '<' — IRI *)
        begin match parse_iri_raw input pos with
        | ParseOk iri pos' ->
          if is_iri iri then ParseOk iri pos'
          else ParseFail "graph label IRI must be absolute" pos
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5F then (* '_' — blank node *)
        (* Blank nodes as graph names: parse and prefix with "_:" *)
        begin match parse_bnode input pos with
        | ParseOk bnode_label pos' ->
          ParseOk (String.concat "" ["_:"; bnode_label]) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        ParseFail "expected '<' or '_:' for graph label" pos

(* ================================================================ *)
(* Optional graph label with preceding whitespace                    *)
(* ================================================================ *)

(** Parse optional graph label: whitespace followed by graph label,
    or nothing (returning None). We peek ahead: if the next non-ws
    character is '.', there is no graph label. *)
let parse_opt_graph_label : parser (option iri) =
  fun input pos ->
    let len = fs_byte_length input in
    (* Skip whitespace first *)
    match pws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseOk None pos1
      else
        let ch = fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x2E then (* '.' — no graph label *)
          ParseOk None pos1
        else if code = 0x3C || code = 0x5F then // IRI or bnode
          begin match parse_graph_label input pos1 with
          | ParseOk g pos2 -> ParseOk (Some g) pos2
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        else if code = 0x22 then // '"' — literal in graph position is invalid
          ParseFail "literals are not allowed as graph names in N-Quads" pos1
        else
          ParseOk None pos1
    | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* N-Quad line parser: subject ws predicate ws object ws graph? ws . *)
(* ================================================================ *)

(** Parse a single N-Quad line.
    Returns (triple, option iri) where the option iri is the graph name. *)
let parse_nquad : parser (triple * option iri) =
  fun input pos ->
    (* Skip leading whitespace *)
    match pws input pos with
    | ParseOk () pos1 ->
      begin match parse_subject input pos1 with
      | ParseOk subj pos2 ->
        begin match pws input pos2 with
        | ParseOk () pos3 ->
          begin match parse_iri input pos3 with
          | ParseOk pred pos4 ->
            begin match pws input pos4 with
            | ParseOk () pos5 ->
              begin match parse_object input pos5 with
              | ParseOk obj pos6 ->
                (* Parse optional graph label *)
                begin match parse_opt_graph_label input pos6 with
                | ParseOk graph_opt pos7 ->
                  (* Skip whitespace before dot *)
                  begin match pws input pos7 with
                  | ParseOk () pos8 ->
                    (* Expect '.' *)
                    let len = fs_byte_length input in
                    if pos8 >= len then ParseFail "expected '.'" pos8
                    else
                      let dot = fs_byte_index input pos8 in
                      if FStar.Char.int_of_char dot = 0x2E then
                        if is_iri pred then
                          let t : triple = { s = subj; p = pred; o = obj } in
                          ParseOk (t, graph_opt) (pos8 + 1)
                        else ParseFail "invalid predicate IRI" pos4
                      else
                        ParseFail "expected '.'" pos8
                  | ParseFail msg fpos -> ParseFail msg fpos
                  end
                | ParseFail msg fpos -> ParseFail msg fpos
                end
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* Dataset construction helpers                                      *)
(* ================================================================ *)

(** Find a named graph in the list, or return None *)
let rec find_named_graph (name : iri) (ngs : list named_graph) : option (list named_graph * rdf_graph * list named_graph) =
  match ngs with
  | [] -> None
  | ng :: rest ->
    if ng.ng_name = name then
      Some ([], ng.ng_graph, rest)
    else
      match find_named_graph name rest with
      | Some (before, g, after) -> Some (ng :: before, g, after)
      | None -> None

(** Add a triple to the appropriate graph in the dataset.
    If graph_name is None, add to default graph.
    If graph_name is Some name, add to (or create) the named graph.

    PERF: uses [graph_add_unchecked] (O(1) prepend). The caller-facing
    [parse_nquads*] entry points wrap their result in [dataset_finalise]
    to restore insertion order in O(N) at the end. See
    docs/designissues/2026-04-25-fstar-rdf-graph-perf-prepend-finalise.md. *)
let dataset_add_quad (ds : rdf_dataset) (t : triple) (graph_name : option iri) : rdf_dataset =
  match graph_name with
  | None ->
    (* Add to default graph *)
    { ds with ds_default = graph_add_unchecked t ds.ds_default }
  | Some name ->
    (* Add to named graph, creating it if needed *)
    match find_named_graph name ds.ds_named with
    | Some (before, existing_g, after) ->
      let updated_g = graph_add_unchecked t existing_g in
      let updated_ng : named_graph = { ng_name = name; ng_graph = updated_g } in
      { ds with ds_named = before @ [updated_ng] @ after }
    | None ->
      let new_ng : named_graph = { ng_name = name; ng_graph = [t] } in
      { ds with ds_named = ds.ds_named @ [new_ng] }

(* ================================================================ *)
(* Document parser: line-by-line N-Quads parsing                     *)
(* ================================================================ *)

(** Parse an N-Quads document, accumulating quads into an rdf_dataset.
    Processes line by line:
    - Skip whitespace
    - If '#', skip comment to end of line
    - If end of line or end of input, skip
    - Otherwise, parse a quad *)
let rec parse_nquads_acc (input:string) (pos:nat) (ds:rdf_dataset) (fuel:nat)
  : Tot rdf_dataset (decreases fuel) =
  if fuel = 0 then ds
  else
    let len = fs_byte_length input in
    if pos >= len then ds
    else
      (* Skip whitespace (space/tab) *)
      let pos1 : nat = match pws input pos with
                       | ParseOk () p -> p
                       | _ -> pos in
      if pos1 >= len then ds
      else
        let ch = fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x23 then (* '#' — comment line *)
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then ds  (* no progress — stop *)
          else parse_nquads_acc input pos3 ds (fuel - 1)
        else if code = 0x0A || code = 0x0D then (* empty line *)
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then ds  (* no progress *)
          else parse_nquads_acc input pos2 ds (fuel - 1)
        else
          (* Try to parse a quad *)
          match parse_nquad input pos1 with
          | ParseOk (t, graph_opt) pos2 ->
            let ds' = dataset_add_quad ds t graph_opt in
            (* After the '.', skip optional whitespace, optional comment, then EOL *)
            let pos3 = match pws input pos2 with
                       | ParseOk () p -> p
                       | _ -> pos2 in
            let pos4 = skip_comment input pos3 in
            let pos5 = skip_eol input pos4 in
            let pos_next = if pos5 > pos1 then pos5
                          else if pos4 > pos1 then pos4
                          else pos2 in
            parse_nquads_acc input pos_next ds' (fuel - 1)
          | ParseFail _ _ ->
            (* Skip to next line on parse failure *)
            let rec skip_line (p:nat) (f:nat) : Tot nat (decreases f) =
              if f = 0 then p
              else if p >= len then p
              else
                let c = fs_byte_index input p in
                let cc = FStar.Char.int_of_char c in
                if cc = 0x0A || cc = 0x0D then skip_eol input p
                else skip_line (p + 1) (f - 1)
            in
            let pos2 = skip_line pos1 (len - pos1) in
            if pos2 = pos1 then ds  (* no progress *)
            else parse_nquads_acc input pos2 ds (fuel - 1)

(** Parse a complete N-Quads document string into an rdf_dataset.
    Triples without a graph label go into the default graph.
    Triples with a graph label go into the corresponding named graph. *)
let parse_nquads (input:string) : rdf_dataset =
  let len = fs_byte_length input in
  // PERF: dataset_add_quad uses graph_add_unchecked (O(1) prepend);
  // dataset_finalise reverses each graph once to restore insertion order.
  dataset_finalise (parse_nquads_acc input 0 empty_dataset (len + 1))

(* Count-only variant for `--count` mode (issue #121).
   Same control flow as parse_nquads_acc but the outer accumulator
   is a `nat` counter — no rdf_dataset construction, no dataset_add_quad,
   no dataset_finalise reverse. Per-line parse_nquad still allocates
   and discards a single quad; what we save is the dataset growth. *)
let rec count_nquads_acc (input:string) (pos:nat) (acc:nat) (fuel:nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then acc
  else
    let len = fs_byte_length input in
    if pos >= len then acc
    else
      let pos1 : nat = match pws input pos with
                       | ParseOk () p -> p
                       | _ -> pos in
      if pos1 >= len then acc
      else
        let ch = fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x23 then
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then acc
          else count_nquads_acc input pos3 acc (fuel - 1)
        else if code = 0x0A || code = 0x0D then
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then acc
          else count_nquads_acc input pos2 acc (fuel - 1)
        else
          match parse_nquad input pos1 with
          | ParseOk _ pos2 ->
            let pos3 = match pws input pos2 with
                       | ParseOk () p -> p
                       | _ -> pos2 in
            let pos4 = skip_comment input pos3 in
            let pos5 = skip_eol input pos4 in
            let pos_next = if pos5 > pos1 then pos5
                          else if pos4 > pos1 then pos4
                          else pos2 in
            count_nquads_acc input pos_next (acc + 1) (fuel - 1)
          | ParseFail _ _ ->
            let rec skip_line (p:nat) (f:nat) : Tot nat (decreases f) =
              if f = 0 then p
              else if p >= len then p
              else
                let c = fs_byte_index input p in
                let cc = FStar.Char.int_of_char c in
                if cc = 0x0A || cc = 0x0D then skip_eol input p
                else skip_line (p + 1) (f - 1)
            in
            let pos2 = skip_line pos1 (len - pos1) in
            if pos2 = pos1 then acc
            else count_nquads_acc input pos2 acc (fuel - 1)

let count_nquads_quads (input:string) : nat =
  let len = fs_byte_length input in
  count_nquads_acc input 0 0 (len + 1)

let rec parse_nquads_strict_acc (input:string) (pos:nat) (ds:rdf_dataset) (fuel:nat)
  : Tot (option rdf_dataset) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = fs_byte_length input in
    if pos >= len then Some ds
    else
      let pos1 : nat = match pws input pos with
                       | ParseOk () p -> p
                       | _ -> pos in
      if pos1 >= len then Some ds
      else
        let ch = fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x23 then
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then None
          else parse_nquads_strict_acc input pos3 ds (fuel - 1)
        else if code = 0x0A || code = 0x0D then
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then None
          else parse_nquads_strict_acc input pos2 ds (fuel - 1)
        else
          match parse_nquad input pos1 with
          | ParseOk (t, graph_opt) pos2 ->
            let ds' = dataset_add_quad ds t graph_opt in
            let pos3 = match pws input pos2 with
                       | ParseOk () p -> p
                       | _ -> pos2 in
            let pos4 = skip_comment input pos3 in
            let pos5 = skip_eol input pos4 in
            if pos5 > pos1 then
              parse_nquads_strict_acc input pos5 ds' (fuel - 1)
            else if pos2 >= len then
              parse_nquads_strict_acc input pos2 ds' (fuel - 1)
            else
              None
          | ParseFail _ _ -> None

let parse_nquads_strict (input:string) : option rdf_dataset =
  let len = fs_byte_length input in
  match parse_nquads_strict_acc input 0 empty_dataset (len + 1) with
  | Some ds -> Some (dataset_finalise ds)
  | None -> None

(* ================================================================ *)
(* Convenience: parse N-Quads returning just a flat list of quads    *)
(* ================================================================ *)

(** A quad is a triple plus an optional graph name *)
noeq type nquad = {
  nq_triple : triple;
  nq_graph  : option iri;
}

// The decreases/fuel VC for parse_nquads_flat_acc is right at the edge of
// Z3's default query size. Adding helpers in RDF.Graph.Executable
// (graph_add_unchecked, dataset_finalise) shifted the surrounding context
// just enough to tip it past the threshold. Pin locally to keep the proof
// stable, matching the precedent set in Parser.Turtle for parse_turtle_doc.
#push-options "--split_queries always"
(** Parse an N-Quads document returning a flat list of quads *)
let rec parse_nquads_flat_acc (input:string) (pos:nat) (acc:list nquad) (fuel:nat)
  : Tot (list nquad) (decreases fuel) =
  if fuel = 0 then List.Tot.rev acc
  else
    let len = fs_byte_length input in
    if pos >= len then List.Tot.rev acc
    else
      (* Skip whitespace (space/tab) *)
      let pos1 : nat = match pws input pos with
                       | ParseOk () p -> p
                       | _ -> pos in
      if pos1 >= len then List.Tot.rev acc
      else
        let ch = fs_byte_index input pos1 in
        let code = FStar.Char.int_of_char ch in
        if code = 0x23 then (* '#' — comment line *)
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then List.Tot.rev acc
          else parse_nquads_flat_acc input pos3 acc (fuel - 1)
        else if code = 0x0A || code = 0x0D then (* empty line *)
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then List.Tot.rev acc
          else parse_nquads_flat_acc input pos2 acc (fuel - 1)
        else
          match parse_nquad input pos1 with
          | ParseOk (t, graph_opt) pos2 ->
            let q : nquad = { nq_triple = t; nq_graph = graph_opt } in
            let pos3 = match pws input pos2 with
                       | ParseOk () p -> p
                       | _ -> pos2 in
            let pos4 = skip_comment input pos3 in
            let pos5 = skip_eol input pos4 in
            let pos_next = if pos5 > pos1 then pos5
                          else if pos4 > pos1 then pos4
                          else pos2 in
            parse_nquads_flat_acc input pos_next (q :: acc) (fuel - 1)
          | ParseFail _ _ ->
            let rec skip_line (p:nat) (f:nat) : Tot nat (decreases f) =
              if f = 0 then p
              else if p >= len then p
              else
                let c = fs_byte_index input p in
                let cc = FStar.Char.int_of_char c in
                if cc = 0x0A || cc = 0x0D then skip_eol input p
                else skip_line (p + 1) (f - 1)
            in
            let pos2 = skip_line pos1 (len - pos1) in
            if pos2 = pos1 then List.Tot.rev acc
            else parse_nquads_flat_acc input pos2 acc (fuel - 1)
#pop-options

let parse_nquads_flat (input:string) : list nquad =
  let len = fs_byte_length input in
  parse_nquads_flat_acc input 0 [] (len + 1)
