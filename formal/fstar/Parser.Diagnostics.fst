module Parser.Diagnostics

// Diagnostic source positions and document walks for the npm entry
// point (https://github.com/danbri/factoidal/issues/344,
// https://github.com/danbri/factoidal/issues/681 -- the prefix-
// reporting half). A leaf module: it depends on the parser modules
// and nothing depends on it, so adding it invalidates no existing
// .checked file. Parser.NTriples / Parser.NQuads / Parser.Turtle /
// Parser.TriG's own lenient and strict entry points are unchanged.

open FStar.List.Tot
open Parser.Combinators
open Parser.FastString
open RDF.Graph.Executable
open Parser.NTriples
open Parser.NQuads
open Parser.Turtle
open Parser.TriG

(* ================================================================ *)
(* Source positions                                                  *)
(* ================================================================ *)

// 1-based line and column of a byte offset. line = 1 + the count of
// 0x0A bytes at positions before the offset; column = 1 + the count
// of bytes since the last such 0x0A (or the start of the input) that
// are not UTF-8 continuation bytes (0x80..0xBF), i.e. a count of
// Unicode scalar values on the current line. An offset past the end
// of the input is clamped to the input's length.
noeq type source_position = {
  sp_offset: nat;
  sp_line: nat;
  sp_column: nat;
}

// Scans input[0..stop) once, folding (line, column) forward. Fuel-free:
// the termination measure is the gap (stop - i), following the
// established pattern in this codebase (e.g. Parser.Combinators.
// match_ci_at's (klen - i), Math.Matrix.trace_acc's (n - i)).
let rec position_of_offset_acc (input: string) (stop: nat) (i: nat{i <= stop})
    (line: nat) (col: nat)
  : Tot (nat & nat) (decreases (stop - i)) =
  if i >= stop then (line, col)
  else
    let b = fs_byte_at input i in
    if b = 0x0A then position_of_offset_acc input stop (i + 1) (line + 1) 1
    else if b >= 0x80 && b <= 0xBF then
      // UTF-8 continuation byte: part of a multi-byte scalar value
      // already counted at its leading byte, so it does not advance
      // the column.
      position_of_offset_acc input stop (i + 1) line col
    else position_of_offset_acc input stop (i + 1) line (col + 1)

let position_of_offset (input: string) (offset: nat) : Tot source_position =
  let len = fs_byte_length input in
  let stop = if offset > len then len else offset in
  let (line, col) = position_of_offset_acc input stop 0 1 1 in
  { sp_offset = offset; sp_line = line; sp_column = col }

(* ================================================================ *)
(* Document outcomes                                                 *)
(* ================================================================ *)

// do_value is the LENIENT parse result (statements before and after
// the first error are kept), matching Parser.Turtle.turtle_doc_result
// and Parser.TriG.trig_parse_state's own first-error-wins convention:
// the first ParseFail encountered is recorded in do_error and the
// walk keeps going. do_prefixes stores each `@prefix` / `PREFIX`
// label WITHOUT its trailing colon -- Parser.Turtle.parse_pname_ns
// returns the prefix via Parser.TurtleScanner.scan_prefixed_name_span,
// whose `pns_prefix` span ends AT the colon's own position (not past
// it), so e.g. `@prefix ex: <http://example.org/> .` stores `"ex"`,
// exactly matching turtle_state.prefixes's own stored form.
noeq type document_outcome (a: Type) = {
  do_value: a;
  do_prefixes: list (string & string);
  do_base: string;
  do_error: option (string & nat);
}

// Turtle document parse: triples, prefixes, final base IRI, first
// error. Mode_12 deduplicates the same way Parser.Turtle.
// parse_turtle_diagnostic_12 does -- RDF 1.2 reifier annotations
// (`~` / `{| |}`) can emit the same rdf:reifies triple at more than
// one syntactic occurrence, and graph_dedup_sort is the module's
// existing fix for that. Mode_11 has no such duplication source and
// stays byte-identical to Parser.Turtle.parse_turtle_diagnostic.
let turtle_document (mode: rdf_syntax_mode) (input: string) (base: string)
  : document_outcome (list triple) =
  let len = fs_byte_length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let seed = (match mode with
              | Mode_11 -> empty_turtle_state
              | Mode_12 -> empty_turtle_state_12) in
  let st = { seed with base_iri = base } in
  let r = parse_turtle_doc st input 0 [] None fuel in
  let triples = (match mode with
                 | Mode_11 -> r.tdr_triples
                 | Mode_12 -> graph_dedup_sort r.tdr_triples) in
  {
    do_value = triples;
    do_prefixes = r.tdr_state.prefixes;
    do_base = r.tdr_state.base_iri;
    do_error = r.tdr_error;
  }

// TriG document parse: dataset, prefixes, final base IRI, first
// error. No dedup step for either mode -- Parser.TriG's own Mode_12
// diagnostic entry point (parse_trig_with_base_diagnostic_12) carries
// none either.
let trig_document (mode: rdf_syntax_mode) (input: string) (base: string)
  : document_outcome rdf_dataset =
  let len = fs_byte_length input in
  let fuel = (len + 1) `op_Multiply` 3 in
  let seed = (match mode with
              | Mode_11 -> empty_turtle_state
              | Mode_12 -> empty_turtle_state_12) in
  let st = { seed with base_iri = base } in
  let tps = make_trig_parse_state st in
  let (ds, tps') = parse_trig_doc tps input 0 empty_dataset fuel in
  {
    do_value = dataset_finalise ds;
    do_prefixes = tps'.ts.prefixes;
    do_base = tps'.ts.base_iri;
    do_error = tps'.terr;
  }

(* ================================================================ *)
(* N-Triples / N-Quads: first-error diagnostic walks                 *)
(* ================================================================ *)

// Same per-line discipline as Parser.NTriples.parse_ntriples_strict_acc:
// blank lines and `#` comment lines are skipped; after a statement,
// optional whitespace, then an optional `#` comment to its own end of
// line, then end of line or end of input. The difference from that
// strict walk is the result channel: the first failure is returned as
// a ParseFail carrying its byte offset, instead of collapsing the
// whole walk to `None`, and content left over after a well-formed
// statement's trailing whitespace and comment -- content that reaches
// neither an end-of-line sequence nor end of input -- is itself a
// failure ("expected end of line after statement"), reported at the
// offset where that content starts.
let rec ntriples_diagnostic_acc (mode: rdf_syntax_mode) (input: string) (pos: nat)
    (acc: list triple) (fuel: nat)
  : Tot (parse_result (list triple)) (decreases fuel) =
  if fuel = 0 then ParseFail "fuel exhausted" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk (List.Tot.rev acc) len
    else
      let pos1 : nat = (match pws input pos with
                        | ParseOk () p -> p
                        | _ -> pos) in
      if pos1 >= len then ParseOk (List.Tot.rev acc) len
      else
        let code = FStar.Char.int_of_char (fs_byte_index input pos1) in
        if code = 0x23 then
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then ParseFail "malformed comment line" pos1
          else ntriples_diagnostic_acc mode input pos3 acc (fuel - 1)
        else if code = 0x0A || code = 0x0D then
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then ParseFail "malformed end of line" pos1
          else ntriples_diagnostic_acc mode input pos2 acc (fuel - 1)
        else
          let triple_result = (match mode with
                                | Mode_11 -> parse_triple input pos1
                                | Mode_12 -> parse_triple_12 input pos1) in
          (match triple_result with
           | ParseOk t pos2 ->
             let pos3 = (match pws input pos2 with
                         | ParseOk () p -> p
                         | _ -> pos2) in
             let pos4 = skip_comment input pos3 in
             let pos5 = skip_eol input pos4 in
             if pos5 > pos4 then
               ntriples_diagnostic_acc mode input pos5 (t :: acc) (fuel - 1)
             else if pos4 >= len then
               ntriples_diagnostic_acc mode input pos4 (t :: acc) (fuel - 1)
             else
               ParseFail "expected end of line after statement" pos4
           | ParseFail msg fpos -> ParseFail msg fpos)

let ntriples_diagnostic (mode: rdf_syntax_mode) (input: string) : parse_result (list triple) =
  let len = fs_byte_length input in
  ntriples_diagnostic_acc mode input 0 [] (len + 1)

// Same shape as ntriples_diagnostic_acc, one slot wider (the optional
// graph label), building an rdf_dataset via dataset_add_quad instead
// of a plain triple list -- mirrors Parser.NQuads.parse_nquads_strict_acc's
// per-line discipline the same way ntriples_diagnostic_acc mirrors
// Parser.NTriples.parse_ntriples_strict_acc.
let rec nquads_diagnostic_acc (mode: rdf_syntax_mode) (input: string) (pos: nat)
    (ds: rdf_dataset) (fuel: nat)
  : Tot (parse_result rdf_dataset) (decreases fuel) =
  if fuel = 0 then ParseFail "fuel exhausted" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk ds len
    else
      let pos1 : nat = (match pws input pos with
                        | ParseOk () p -> p
                        | _ -> pos) in
      if pos1 >= len then ParseOk ds len
      else
        let code = FStar.Char.int_of_char (fs_byte_index input pos1) in
        if code = 0x23 then
          let pos2 = skip_comment input pos1 in
          let pos3 = skip_eol input pos2 in
          if pos3 = pos1 then ParseFail "malformed comment line" pos1
          else nquads_diagnostic_acc mode input pos3 ds (fuel - 1)
        else if code = 0x0A || code = 0x0D then
          let pos2 = skip_eol input pos1 in
          if pos2 = pos1 then ParseFail "malformed end of line" pos1
          else nquads_diagnostic_acc mode input pos2 ds (fuel - 1)
        else
          let quad_result = (match mode with
                              | Mode_11 -> parse_nquad input pos1
                              | Mode_12 -> parse_nquad_12 input pos1) in
          (match quad_result with
           | ParseOk (t, graph_opt) pos2 ->
             let ds' = dataset_add_quad ds t graph_opt in
             let pos3 = (match pws input pos2 with
                         | ParseOk () p -> p
                         | _ -> pos2) in
             let pos4 = skip_comment input pos3 in
             let pos5 = skip_eol input pos4 in
             if pos5 > pos4 then
               nquads_diagnostic_acc mode input pos5 ds' (fuel - 1)
             else if pos4 >= len then
               nquads_diagnostic_acc mode input pos4 ds' (fuel - 1)
             else
               ParseFail "expected end of line after statement" pos4
           | ParseFail msg fpos -> ParseFail msg fpos)

let nquads_diagnostic (mode: rdf_syntax_mode) (input: string) : parse_result rdf_dataset =
  let len = fs_byte_length input in
  match nquads_diagnostic_acc mode input 0 empty_dataset (len + 1) with
  | ParseOk ds pos -> ParseOk (dataset_finalise ds) pos
  | ParseFail msg pos -> ParseFail msg pos
