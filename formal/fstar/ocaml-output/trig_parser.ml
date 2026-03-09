(* TriG parser — UNVERIFIED TEST INFRASTRUCTURE.
   Not extracted from F*. Hand-written OCaml for W3C TriG test suites.
   TriG extends Turtle with named graph blocks:
     GRAPH <iri> { triples } or <iri> { triples } or { triples }
   For our purposes we parse TriG and return all triples (ignoring graph names).
   We do this by extracting Turtle content from blocks and parsing with turtle_parser. *)

open RDF_Graph_Executable

exception Parse_error of string

(* Tokenize TriG to handle { } blocks. Strategy:
   - Collect @prefix/@base and PREFIX/BASE directives
   - For each { ... } block, parse contents as Turtle (with accumulated prefixes)
   - Also handle bare triples outside blocks (valid TriG for default graph) *)

let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let skip_ws s pos =
  let len = String.length s in
  let p = ref pos in
  while !p < len && is_ws s.[!p] do incr p done;
  (* Skip comments *)
  while !p < len && s.[!p] = '#' do
    while !p < len && s.[!p] <> '\n' && s.[!p] <> '\r' do incr p done;
    while !p < len && is_ws s.[!p] do incr p done
  done;
  !p

(* Find matching closing brace, handling string literals and nested braces *)
let find_closing_brace s start =
  let len = String.length s in
  let p = ref start in
  let depth = ref 1 in
  while !p < len && !depth > 0 do
    let c = s.[!p] in
    if c = '{' then (incr depth; incr p)
    else if c = '}' then (decr depth; if !depth > 0 then incr p)
    else if c = '#' then begin
      (* Skip comment *)
      while !p < len && s.[!p] <> '\n' do incr p done;
      if !p < len then incr p
    end
    else if c = '\'' then begin
      (* Check for long string ''' or short string ' *)
      if !p + 2 < len && s.[!p+1] = '\'' && s.[!p+2] = '\'' then begin
        p := !p + 3;
        (* Long single-quoted string *)
        while !p + 2 < len && not (s.[!p] = '\'' && s.[!p+1] = '\'' && s.[!p+2] = '\'') do
          if s.[!p] = '\\' then p := !p + 2 else incr p
        done;
        if !p + 2 < len then p := !p + 3
        else raise (Parse_error "Unterminated long string")
      end else begin
        incr p;
        while !p < len && s.[!p] <> '\'' && s.[!p] <> '\n' do
          if s.[!p] = '\\' then p := !p + 2 else incr p
        done;
        if !p < len && s.[!p] = '\'' then incr p
      end
    end
    else if c = '"' then begin
      if !p + 2 < len && s.[!p+1] = '"' && s.[!p+2] = '"' then begin
        p := !p + 3;
        while !p + 2 < len && not (s.[!p] = '"' && s.[!p+1] = '"' && s.[!p+2] = '"') do
          if s.[!p] = '\\' then p := !p + 2 else incr p
        done;
        if !p + 2 < len then p := !p + 3
        else raise (Parse_error "Unterminated long string")
      end else begin
        incr p;
        while !p < len && s.[!p] <> '"' && s.[!p] <> '\n' do
          if s.[!p] = '\\' then p := !p + 2 else incr p
        done;
        if !p < len && s.[!p] = '"' then incr p
      end
    end
    else if c = '<' then begin
      incr p;
      while !p < len && s.[!p] <> '>' do
        if s.[!p] = '\\' then p := !p + 2 else incr p
      done;
      if !p < len then incr p
    end
    else incr p
  done;
  if !depth > 0 then raise (Parse_error "Unmatched '{'");
  !p

(* Check if position starts with a case-insensitive keyword followed by whitespace *)
let starts_with_keyword s pos kw =
  let kw_len = String.length kw in
  let s_len = String.length s in
  if pos + kw_len >= s_len then false
  else
    let sub = String.uppercase_ascii (String.sub s pos kw_len) in
    sub = String.uppercase_ascii kw &&
    (is_ws s.[pos + kw_len] || s.[pos + kw_len] = '<' || s.[pos + kw_len] = '_' || s.[pos + kw_len] = ':')

(* Check if position starts with a prefix/base directive *)
let is_directive s pos =
  let len = String.length s in
  if pos >= len then false
  else
    s.[pos] = '@' ||
    starts_with_keyword s pos "PREFIX" ||
    starts_with_keyword s pos "BASE"

(* Read a directive line (up to and including the '.') *)
let read_directive s pos =
  let len = String.length s in
  let p = ref pos in
  (* For @prefix/@base, read up to and including '.' *)
  (* For PREFIX/BASE, read up to end of line or next statement *)
  if !p < len && s.[!p] = '@' then begin
    while !p < len && s.[!p] <> '.' do incr p done;
    if !p < len then incr p;
    String.sub s pos (!p - pos)
  end else begin
    (* SPARQL-style PREFIX/BASE: read until we hit something that's not part of the directive *)
    while !p < len && s.[!p] <> '\n' && s.[!p] <> '\r' && s.[!p] <> '{' do incr p done;
    let directive = String.sub s pos (!p - pos) in
    (* Add a newline to ensure it's properly terminated *)
    String.trim directive ^ "\n"
  end

(* Skip an IRI <...> or prefixed name or blank node *)
let skip_iri_or_name s pos =
  let len = String.length s in
  let p = ref pos in
  if !p < len && s.[!p] = '<' then begin
    incr p;
    while !p < len && s.[!p] <> '>' do
      if s.[!p] = '\\' then p := !p + 2 else incr p
    done;
    if !p < len then incr p;
    !p
  end else if !p + 1 < len && s.[!p] = '_' && s.[!p+1] = ':' then begin
    p := !p + 2;
    while !p < len && not (is_ws s.[!p]) && s.[!p] <> '{' && s.[!p] <> '.' do incr p done;
    !p
  end else begin
    (* Prefixed name *)
    while !p < len && not (is_ws s.[!p]) && s.[!p] <> '{' && s.[!p] <> '.' && s.[!p] <> ';' do incr p done;
    !p
  end

let parse_trig input base =
  let len = String.length input in
  let all_triples = ref [] in
  let directives = Buffer.create 256 in
  let pos = ref 0 in

  while !pos < len do
    pos := skip_ws input !pos;
    if !pos >= len then ()
    else if is_directive input !pos then begin
      (* Collect directive for use in all subsequent blocks *)
      let dir = read_directive input !pos in
      Buffer.add_string directives dir;
      Buffer.add_char directives '\n';
      pos := !pos + String.length (String.trim dir);
      (* Skip trailing dot and whitespace for @-style directives *)
      if !pos < len && input.[!pos] = '.' then incr pos;
      pos := skip_ws input !pos
    end
    else if !pos < len && input.[!pos] = '{' then begin
      (* Default graph block *)
      incr pos;
      let close = find_closing_brace input !pos in
      let block_content = String.sub input !pos (close - !pos) in
      let turtle_input = Buffer.contents directives ^ block_content in
      (try
        Turtle_parser.reset_bnodes ();
        let triples = Turtle_parser.parse_turtle turtle_input base in
        all_triples := !all_triples @ triples
      with Ntriples_parser.Parse_error msg ->
        raise (Parse_error (Printf.sprintf "In default graph block: %s" msg)));
      pos := close + 1;
      pos := skip_ws input !pos;
      (* Optional dot after closing brace *)
      if !pos < len && input.[!pos] = '.' then incr pos
    end
    else if !pos < len && starts_with_keyword input !pos "GRAPH" then begin
      (* GRAPH <iri> { ... } *)
      pos := !pos + 5;
      pos := skip_ws input !pos;
      if !pos >= len then raise (Parse_error "Expected graph name after GRAPH");
      pos := skip_iri_or_name input !pos;
      pos := skip_ws input !pos;
      if !pos >= len || input.[!pos] <> '{' then
        raise (Parse_error "Expected '{' after GRAPH name");
      incr pos;
      let close = find_closing_brace input !pos in
      let block_content = String.sub input !pos (close - !pos) in
      let turtle_input = Buffer.contents directives ^ block_content in
      (try
        Turtle_parser.reset_bnodes ();
        let triples = Turtle_parser.parse_turtle turtle_input base in
        all_triples := !all_triples @ triples
      with Ntriples_parser.Parse_error msg ->
        raise (Parse_error (Printf.sprintf "In named graph block: %s" msg)));
      pos := close + 1;
      pos := skip_ws input !pos;
      if !pos < len && input.[!pos] = '.' then incr pos
    end
    else if !pos < len then begin
      (* Could be: graphName { ... } or bare triples in default graph *)
      let saved_pos = !pos in
      (* Try to find if this is graphName { ... } pattern *)
      let after_name = skip_iri_or_name input !pos in
      let after_name_ws = skip_ws input after_name in
      if after_name_ws < len && input.[after_name_ws] = '{' then begin
        (* Named graph: name { ... } *)
        pos := after_name_ws + 1;
        let close = find_closing_brace input !pos in
        let block_content = String.sub input !pos (close - !pos) in
        let turtle_input = Buffer.contents directives ^ block_content in
        (try
          Turtle_parser.reset_bnodes ();
          let triples = Turtle_parser.parse_turtle turtle_input base in
          all_triples := !all_triples @ triples
        with Ntriples_parser.Parse_error msg ->
          raise (Parse_error (Printf.sprintf "In named graph block: %s" msg)));
        pos := close + 1;
        pos := skip_ws input !pos;
        if !pos < len && input.[!pos] = '.' then incr pos
      end else begin
        (* Bare triples in default graph — collect until next block or directive *)
        pos := saved_pos;
        let start = !pos in
        (* Find end: next '{' at top level, or next directive, or EOF *)
        let end_pos = ref !pos in
        let found = ref false in
        while !end_pos < len && not !found do
          let c = input.[!end_pos] in
          if c = '{' then found := true
          else if c = '#' then begin
            while !end_pos < len && input.[!end_pos] <> '\n' do incr end_pos done;
            if !end_pos < len then incr end_pos
          end
          else if c = '"' then begin
            if !end_pos + 2 < len && input.[!end_pos+1] = '"' && input.[!end_pos+2] = '"' then begin
              end_pos := !end_pos + 3;
              while !end_pos + 2 < len && not (input.[!end_pos] = '"' && input.[!end_pos+1] = '"' && input.[!end_pos+2] = '"') do
                if input.[!end_pos] = '\\' then end_pos := !end_pos + 2 else incr end_pos
              done;
              if !end_pos + 2 < len then end_pos := !end_pos + 3
            end else begin
              incr end_pos;
              while !end_pos < len && input.[!end_pos] <> '"' && input.[!end_pos] <> '\n' do
                if input.[!end_pos] = '\\' then end_pos := !end_pos + 2 else incr end_pos
              done;
              if !end_pos < len && input.[!end_pos] = '"' then incr end_pos
            end
          end
          else if c = '\'' then begin
            if !end_pos + 2 < len && input.[!end_pos+1] = '\'' && input.[!end_pos+2] = '\'' then begin
              end_pos := !end_pos + 3;
              while !end_pos + 2 < len && not (input.[!end_pos] = '\'' && input.[!end_pos+1] = '\'' && input.[!end_pos+2] = '\'') do
                if input.[!end_pos] = '\\' then end_pos := !end_pos + 2 else incr end_pos
              done;
              if !end_pos + 2 < len then end_pos := !end_pos + 3
            end else begin
              incr end_pos;
              while !end_pos < len && input.[!end_pos] <> '\'' && input.[!end_pos] <> '\n' do
                if input.[!end_pos] = '\\' then end_pos := !end_pos + 2 else incr end_pos
              done;
              if !end_pos < len && input.[!end_pos] = '\'' then incr end_pos
            end
          end
          else if c = '<' then begin
            incr end_pos;
            while !end_pos < len && input.[!end_pos] <> '>' do
              if input.[!end_pos] = '\\' then end_pos := !end_pos + 2 else incr end_pos
            done;
            if !end_pos < len then incr end_pos
          end
          else if c = '\n' || c = '\r' then begin
            incr end_pos;
            let line_start = skip_ws input !end_pos in
            if line_start < len && is_directive input line_start then begin
              end_pos := line_start;
              found := true
            end else
              end_pos := line_start
          end
          else incr end_pos
        done;
        if !end_pos > start then begin
          let chunk = String.sub input start (!end_pos - start) in
          let turtle_input = Buffer.contents directives ^ chunk in
          (try
            Turtle_parser.reset_bnodes ();
            let triples = Turtle_parser.parse_turtle turtle_input base in
            all_triples := !all_triples @ triples
          with Ntriples_parser.Parse_error msg ->
            raise (Parse_error (Printf.sprintf "In bare triples: %s" msg)));
          pos := !end_pos
        end else
          (* Can't make progress — skip a char to avoid infinite loop *)
          incr pos
      end
    end
  done;
  !all_triples
