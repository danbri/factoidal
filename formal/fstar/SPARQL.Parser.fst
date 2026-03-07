module SPARQL.Parser

(** ====================================================================== **)
(** SPARQL 1.1 Parser — Recursive Descent                                  **)
(**                                                                        **)
(** Parses SPARQL query strings into the query AST defined in              **)
(** SPARQL11.Algebra.fst. Extractable to OCaml via F* codegen.             **)
(**                                                                        **)
(** Coverage: PREFIX, BASE, SELECT (vars/*/DISTINCT), WHERE,               **)
(** triple patterns (;/,), FILTER, OPTIONAL, UNION, BIND,                  **)
(** ORDER BY, LIMIT, OFFSET, DISTINCT, REDUCED,                            **)
(** expressions (arithmetic, comparison, boolean, built-in functions),      **)
(** literals (string, integer, decimal, boolean, typed, language-tagged).   **)
(**                                                                        **)
(** This module uses --lax for extraction. The parser is in the TCB        **)
(** (I/O boundary) and will be replaced by an EverParse-extracted          **)
(** verified parser in Phase 2.                                            **)
(** ====================================================================== **)

#push-options "--admit_smt_queries true"

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

(** Parser state: input string + current position **)
noeq type pstate = {
  inp : string;
  pos : nat;
}

let mk_pstate (s : string) : pstate = { inp = s; pos = 0 }

(** Character access **)
let ps_eof (ps : pstate) : bool = ps.pos >= String.length ps.inp

let ps_peek (ps : pstate) : option FStar.Char.char =
  if ps_eof ps then None
  else Some (String.index ps.inp ps.pos)

let ps_advance (ps : pstate) (n : nat) : pstate =
  { ps with pos = ps.pos + n }

let ps_remaining (ps : pstate) : string =
  if ps_eof ps then ""
  else String.sub ps.inp ps.pos (String.length ps.inp - ps.pos)

let ps_char_at (ps : pstate) (offset : nat) : option FStar.Char.char =
  let i = ps.pos + offset in
  if i >= String.length ps.inp then None
  else Some (String.index ps.inp i)

(** ====================================================================== **)
(** Whitespace and comment skipping                                         **)
(** ====================================================================== **)

let is_ws (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let rec skip_ws (ps : pstate) : pstate =
  match ps_peek ps with
  | None -> ps
  | Some c ->
    if is_ws c then skip_ws (ps_advance ps 1)
    else if FStar.Char.int_of_char c = 0x23 (* '#' *) then
      skip_line_comment (ps_advance ps 1)
    else ps

and skip_line_comment (ps : pstate) : pstate =
  match ps_peek ps with
  | None -> ps
  | Some c ->
    let code = FStar.Char.int_of_char c in
    if code = 0x0A || code = 0x0D then skip_ws (ps_advance ps 1)
    else skip_line_comment (ps_advance ps 1)

(** ====================================================================== **)
(** String matching utilities                                               **)
(** ====================================================================== **)

let ps_starts_with (ps : pstate) (s : string) : bool =
  let slen = String.length s in
  let ilen = String.length ps.inp in
  if ps.pos + slen > ilen then false
  else String.sub ps.inp ps.pos slen = s

let ps_starts_with_ci (ps : pstate) (s : string) : bool =
  let slen = String.length s in
  let ilen = String.length ps.inp in
  if ps.pos + slen > ilen then false
  else String.lowercase (String.sub ps.inp ps.pos slen) = String.lowercase s

let ps_consume (ps : pstate) (s : string) : option pstate =
  if ps_starts_with_ci ps s then Some (ps_advance ps (String.length s))
  else None

let ps_expect (ps : pstate) (s : string) : option pstate =
  let ps = skip_ws ps in
  ps_consume ps s

(** ====================================================================== **)
(** Character predicates                                                    **)
(** ====================================================================== **)

let is_alpha (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A)

let is_digit (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code >= 0x30 && code <= 0x39

let is_alnum (c : FStar.Char.char) : bool =
  is_alpha c || is_digit c

let is_pn_chars_base (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  is_alpha c ||
  (code >= 0xC0 && code <= 0xD6) ||
  (code >= 0xD8 && code <= 0xF6) ||
  (code >= 0xF8 && code <= 0x2FF)

let is_pn_chars_u (c : FStar.Char.char) : bool =
  is_pn_chars_base c || FStar.Char.int_of_char c = 0x5F

let is_pn_chars (c : FStar.Char.char) : bool =
  is_pn_chars_u c || is_digit c ||
  FStar.Char.int_of_char c = 0x2D ||  (* '-' *)
  FStar.Char.int_of_char c = 0x2E ||  (* '.' *)
  FStar.Char.int_of_char c = 0xB7

(** ====================================================================== **)
(** Lexical productions                                                     **)
(** ====================================================================== **)

(** Parse an IRI reference: <...> **)
let parse_iriref (ps : pstate) : option (string * pstate) =
  let ps = skip_ws ps in
  match ps_peek ps with
  | Some c when FStar.Char.int_of_char c = 0x3C (* '<' *) ->
    let ps = ps_advance ps 1 in
    let rec collect (ps : pstate) (acc : list FStar.Char.char) : option (string * pstate) =
      match ps_peek ps with
      | None -> None
      | Some c ->
        if FStar.Char.int_of_char c = 0x3E (* '>' *) then
          Some (String.string_of_list (List.Tot.rev acc), ps_advance ps 1)
        else
          collect (ps_advance ps 1) (c :: acc)
    in
    collect ps []
  | _ -> None

(** Parse a variable: ?name or $name **)
let parse_variable (ps : pstate) : option (string * pstate) =
  let ps = skip_ws ps in
  match ps_peek ps with
  | Some c when FStar.Char.int_of_char c = 0x3F || FStar.Char.int_of_char c = 0x24 ->
    let ps = ps_advance ps 1 in
    let rec collect (ps : pstate) (acc : list FStar.Char.char) : option (string * pstate) =
      match ps_peek ps with
      | Some c when is_pn_chars_u c || is_digit c ->
        collect (ps_advance ps 1) (c :: acc)
      | _ ->
        if Nil? acc then None
        else Some (String.string_of_list (List.Tot.rev acc), ps)
    in
    collect ps []
  | _ -> None

(** Parse a prefix label (e.g., "rdf" in "rdf:type") — may be empty **)
let parse_pname_ns (ps : pstate) : option (string * pstate) =
  let ps = skip_ws ps in
  let rec collect (ps : pstate) (acc : list FStar.Char.char) : option (string * pstate) =
    match ps_peek ps with
    | Some c when FStar.Char.int_of_char c = 0x3A (* ':' *) ->
      Some (String.string_of_list (List.Tot.rev acc), ps_advance ps 1)
    | Some c when is_pn_chars c ->
      collect (ps_advance ps 1) (c :: acc)
    | _ ->
      if Nil? acc then None
      else None  (* no colon found — not a pname *)
  in
  collect ps []

(** Parse a prefixed name: prefix:local **)
let parse_pname_ln (ps : pstate) (prefixes : list (string * wf_iri))
  : option (wf_iri * pstate) =
  let ps_orig = ps in
  let ps = skip_ws ps in
  match parse_pname_ns ps with
  | None -> None
  | Some (prefix, ps) ->
    (* Look up prefix *)
    match List.Tot.assoc prefix prefixes with
    | None -> None
    | Some base_iri ->
      (* Collect local name *)
      let rec collect (ps : pstate) (acc : list FStar.Char.char) : (string * pstate) =
        match ps_peek ps with
        | Some c when is_pn_chars c || FStar.Char.int_of_char c = 0x2F (* '/' *) ->
          collect (ps_advance ps 1) (c :: acc)
        | _ -> (String.string_of_list (List.Tot.rev acc), ps)
      in
      let (local, ps) = collect ps [] in
      let full_iri = base_iri ^ local in
      if is_iri full_iri then Some (full_iri, ps) else None

(** Resolve a potentially relative IRI against a base IRI **)
let resolve_relative_iri (base : option wf_iri) (iri : string) : string =
  if String.length iri = 0 then
    (match base with | Some b -> b | None -> iri)
  else
    let chars = list_of_string iri in
    let rec has_scheme (cs : list FStar.Char.char) : bool =
      match cs with
      | [] -> false
      | c :: rest ->
        let code = FStar.Char.int_of_char c in
        if code = 0x3A then true
        else if code = 0x2F then false
        else if is_alpha c || is_digit c || code = 0x2B || code = 0x2D || code = 0x2E then
          has_scheme rest
        else false
    in
    if has_scheme chars then iri
    else
      match base with
      | None -> iri
      | Some b ->
        if String.length iri > 0 && String.sub iri 0 1 = "#" then
          b ^ iri
        else
          let blen = String.length b in
          let rec find_last_slash (i : nat) : nat =
            if i = 0 then 0
            else if String.sub b (i - 1) 1 = "/" then i
            else find_last_slash (i - 1)
          in
          let prefix_str = String.sub b 0 (find_last_slash blen) in
          prefix_str ^ iri

(** Parse any IRI — either <iriref> or prefix:local **)
let parse_iri (ps : pstate) (prefixes : list (string * wf_iri))
  : option (wf_iri * pstate) =
  let ps = skip_ws ps in
  match ps_peek ps with
  | Some c when FStar.Char.int_of_char c = 0x3C ->
    (match parse_iriref ps with
     | Some (iri, ps) ->
       if is_iri iri then Some (iri, ps)
       else
         (* Try resolving against base stored in prefixes *)
         let base = List.Tot.assoc "__base__" prefixes in
         let resolved = resolve_relative_iri base iri in
         if is_iri resolved then Some (resolved, ps) else None
     | None -> None)
  | _ -> parse_pname_ln ps prefixes

(** Parse a string literal: "..." or '...' **)
let rec parse_string_literal (ps : pstate) : option (string * pstate) =
  let ps0 = skip_ws ps in
  let c0 = ps_peek ps0 in
  if c0 = Some (FStar.Char.char_of_int 0x22) || c0 = Some (FStar.Char.char_of_int 0x27) then
    let qcode = (match c0 with | Some c -> FStar.Char.int_of_char c | None -> 0) in
    parse_string_inner ps0 qcode
  else None

and parse_string_inner (ps : pstate) (qcode : int) : option (string * pstate) =
  (* Check for long strings (triple-quoted) *)
  let is_long =
    (match ps_char_at ps 1, ps_char_at ps 2 with
     | Some c1, Some c2 -> FStar.Char.int_of_char c1 = qcode && FStar.Char.int_of_char c2 = qcode
     | _ -> false)
  in
  if is_long then
    let ps = ps_advance ps 3 in
    let rec collect (ps : pstate) (acc : list FStar.Char.char) : option (string * pstate) =
      match ps_peek ps with
      | None -> None
      | Some ch ->
        if FStar.Char.int_of_char ch = qcode then
          (match ps_char_at ps 1, ps_char_at ps 2 with
           | Some c1, Some c2 when FStar.Char.int_of_char c1 = qcode && FStar.Char.int_of_char c2 = qcode ->
             Some (String.string_of_list (List.Tot.rev acc), ps_advance ps 3)
           | _ -> collect (ps_advance ps 1) (ch :: acc))
        else if FStar.Char.int_of_char ch = 0x5C then
          (match ps_char_at ps 1 with
           | None -> None
           | Some c2 ->
             let escaped = match FStar.Char.int_of_char c2 with
               | 0x6E -> FStar.Char.char_of_int 0x0A
               | 0x74 -> FStar.Char.char_of_int 0x09
               | 0x72 -> FStar.Char.char_of_int 0x0D
               | _ -> c2
             in
             collect (ps_advance ps 2) (escaped :: acc))
        else collect (ps_advance ps 1) (ch :: acc)
    in
    collect ps []
  else
    let ps = ps_advance ps 1 in
    let rec collect (ps : pstate) (acc : list FStar.Char.char) : option (string * pstate) =
      match ps_peek ps with
      | None -> None
      | Some ch ->
        if FStar.Char.int_of_char ch = qcode then
          Some (String.string_of_list (List.Tot.rev acc), ps_advance ps 1)
        else if FStar.Char.int_of_char ch = 0x5C then
          (match ps_char_at ps 1 with
           | None -> None
           | Some c2 ->
             let escaped = match FStar.Char.int_of_char c2 with
               | 0x6E -> FStar.Char.char_of_int 0x0A
               | 0x74 -> FStar.Char.char_of_int 0x09
               | 0x72 -> FStar.Char.char_of_int 0x0D
               | 0x5C -> FStar.Char.char_of_int 0x5C
               | 0x22 -> FStar.Char.char_of_int 0x22
               | 0x27 -> FStar.Char.char_of_int 0x27
               | _ -> c2
             in
             collect (ps_advance ps 2) (escaped :: acc))
        else if FStar.Char.int_of_char ch = 0x0A || FStar.Char.int_of_char ch = 0x0D then
          None
        else collect (ps_advance ps 1) (ch :: acc)
    in
    collect ps []

(** Parse an RDF literal: "string"@lang or "string"^^<type> or "string" **)
let parse_rdf_literal (ps : pstate) (prefixes : list (string * wf_iri))
  : option (wf_literal * pstate) =
  match parse_string_literal ps with
  | None -> None
  | Some (lex, ps) ->
    match ps_peek ps with
    | Some c when FStar.Char.int_of_char c = 0x40 (* '@' *) ->
      (* Language tag *)
      let ps = ps_advance ps 1 in
      let rec collect (ps : pstate) (acc : list FStar.Char.char) : (string * pstate) =
        match ps_peek ps with
        | Some c when is_alpha c || is_digit c || FStar.Char.int_of_char c = 0x2D ->
          collect (ps_advance ps 1) (c :: acc)
        | _ -> (String.string_of_list (List.Tot.rev acc), ps)
      in
      let (lang, ps) = collect ps [] in
      if String.length lang = 0 then None
      else
        let lit : wf_literal = {
          lexical_form = lex;
          datatype = rdf_lang_string;
          lang_tag = Some lang;
        } in
        Some (lit, ps)
    | Some c when FStar.Char.int_of_char c = 0x5E (* '^' *) ->
      (match ps_char_at ps 1 with
       | Some c2 when FStar.Char.int_of_char c2 = 0x5E ->
         let ps = ps_advance ps 2 in
         (match parse_iri ps prefixes with
          | Some (dt, ps) ->
            let lit : wf_literal = {
              lexical_form = lex;
              datatype = dt;
              lang_tag = None;
            } in
            Some (lit, ps)
          | None -> None)
       | _ ->
         let lit : wf_literal = {
           lexical_form = lex;
           datatype = xsd_string;
           lang_tag = None;
         } in
         Some (lit, ps))
    | _ ->
      let lit : wf_literal = {
        lexical_form = lex;
        datatype = xsd_string;
        lang_tag = None;
      } in
      Some (lit, ps)

(** Parse a boolean literal **)
let parse_boolean (ps : pstate) : option (bool * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "true" with
  | Some ps -> Some (true, ps)
  | None ->
    match ps_consume ps "false" with
    | Some ps -> Some (false, ps)
    | None -> None

(** Parse an integer or decimal literal from the input **)
let parse_numeric (ps : pstate) : option (expr * pstate) =
  let ps = skip_ws ps in
  let start = ps.pos in
  (* Optional sign *)
  let ps = match ps_peek ps with
    | Some c when FStar.Char.int_of_char c = 0x2B || FStar.Char.int_of_char c = 0x2D ->
      ps_advance ps 1
    | _ -> ps
  in
  (* Collect digits *)
  let rec digits (ps : pstate) : pstate =
    match ps_peek ps with
    | Some c when is_digit c -> digits (ps_advance ps 1)
    | _ -> ps
  in
  let ps_after_int = digits ps in
  if ps_after_int.pos = ps.pos && (match ps_peek ps with | Some c -> FStar.Char.int_of_char c <> 0x2E | None -> true) then
    None  (* no digits consumed and no dot *)
  else
    (* Check for decimal point *)
    match ps_peek ps_after_int with
    | Some c when FStar.Char.int_of_char c = 0x2E (* '.' *) ->
      let ps2 = digits (ps_advance ps_after_int 1) in
      (* Check for exponent *)
      (match ps_peek ps2 with
       | Some c when FStar.Char.int_of_char c = 0x45 || FStar.Char.int_of_char c = 0x65 (* e/E *) ->
         let ps3 = ps_advance ps2 1 in
         let ps3 = match ps_peek ps3 with
           | Some c when FStar.Char.int_of_char c = 0x2B || FStar.Char.int_of_char c = 0x2D -> ps_advance ps3 1
           | _ -> ps3
         in
         let ps3 = digits ps3 in
         let s = String.sub ps.inp start (ps3.pos - start) in
         Some (E_DoubleLit s, ps3)
       | _ ->
         let s = String.sub ps.inp start (ps2.pos - start) in
         Some (E_DecimalLit s, ps2))
    | _ ->
      (* Integer *)
      if ps_after_int.pos > start then
        let s = String.sub ps.inp start (ps_after_int.pos - start) in
        (* Try to convert to int *)
        Some (E_NumericLit 0, ps_after_int)  (* Placeholder — OCaml patch will fix int parsing *)
      else None

(** ====================================================================== **)
(** Prefix and Base declarations                                            **)
(** ====================================================================== **)

let parse_prefix_decl (ps : pstate) (prefixes : list (string * wf_iri))
  : option ((string * wf_iri) * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "PREFIX" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    match parse_pname_ns ps with
    | None -> None
    | Some (prefix, ps) ->
      let ps = skip_ws ps in
      match parse_iriref ps with
      | None -> None
      | Some (iri, ps) ->
        if is_iri iri then
          Some ((prefix, iri), ps)
        else if String.length iri = 0 then
          let dummy : wf_iri = (assert_norm (is_iri "urn:empty:"); "urn:empty:") in
          Some ((prefix, dummy), ps)
        else
          (* Return raw string — prologue will resolve against BASE *)
          Some ((prefix, iri), ps)

let parse_base_decl (ps : pstate) : option (wf_iri * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "BASE" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    match parse_iriref ps with
    | None -> None
    | Some (iri, ps) ->
      if is_iri iri then Some (iri, ps) else None

let rec parse_prologue (ps : pstate) (base : option wf_iri) (prefixes : list (string * wf_iri))
  : (option wf_iri * list (string * wf_iri) * pstate) =
  let ps = skip_ws ps in
  match parse_base_decl ps with
  | Some (iri, ps) -> parse_prologue ps (Some iri) prefixes
  | None ->
    match parse_prefix_decl ps prefixes with
    | Some ((prefix, raw_iri), ps) ->
      (* Resolve prefix IRI against base *)
      let resolved = resolve_relative_iri base raw_iri in
      let iri = if is_iri resolved then resolved else raw_iri in
      parse_prologue ps base ((prefix, iri) :: prefixes)
    | None -> (base, prefixes, ps)

(** ====================================================================== **)
(** Expression parser (recursive descent with precedence)                   **)
(** ====================================================================== **)

(** Forward declarations via mutual recursion **)

let rec parse_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  parse_or_expr ps prefixes

and parse_or_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  match parse_and_expr ps prefixes with
  | None -> None
  | Some (left, ps) ->
    let rec loop (left : expr) (ps : pstate) : (expr * pstate) =
      let ps' = skip_ws ps in
      match ps_consume ps' "||" with
      | Some ps' ->
        (match parse_and_expr ps' prefixes with
         | Some (right, ps') -> loop (E_Or left right) ps'
         | None -> (left, ps))
      | None -> (left, ps)
    in
    Some (loop left ps)

and parse_and_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  match parse_relational_expr ps prefixes with
  | None -> None
  | Some (left, ps) ->
    let rec loop (left : expr) (ps : pstate) : (expr * pstate) =
      let ps' = skip_ws ps in
      match ps_consume ps' "&&" with
      | Some ps' ->
        (match parse_relational_expr ps' prefixes with
         | Some (right, ps') -> loop (E_And left right) ps'
         | None -> (left, ps))
      | None -> (left, ps)
    in
    Some (loop left ps)

and parse_relational_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  match parse_additive_expr ps prefixes with
  | None -> None
  | Some (left, ps) ->
    let ps' = skip_ws ps in
    (* Try IN / NOT IN *)
    (match ps_consume ps' "NOT" with
     | Some ps2 ->
       let ps2 = skip_ws ps2 in
       (match ps_consume ps2 "IN" with
        | Some ps2 ->
          (match parse_expr_list ps2 prefixes with
           | Some (args, ps2) -> Some (E_NotIn left args, ps2)
           | None -> Some (left, ps))
        | None ->
          (* Not "NOT IN", try comparison *)
          parse_comparison left ps' prefixes)
     | None ->
       match ps_consume ps' "IN" with
       | Some ps2 ->
         (match parse_expr_list ps2 prefixes with
          | Some (args, ps2) -> Some (E_In left args, ps2)
          | None -> Some (left, ps))
       | None -> parse_comparison left ps' prefixes)

and parse_comparison (left : expr) (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  match ps_consume ps "<=" with
  | Some ps' ->
    (match parse_additive_expr ps' prefixes with
     | Some (right, ps') -> Some (E_Compare CmpLe left right, ps')
     | None -> Some (left, ps))
  | None ->
    match ps_consume ps ">=" with
    | Some ps' ->
      (match parse_additive_expr ps' prefixes with
       | Some (right, ps') -> Some (E_Compare CmpGe left right, ps')
       | None -> Some (left, ps))
    | None ->
      match ps_consume ps "!=" with
      | Some ps' ->
        (match parse_additive_expr ps' prefixes with
         | Some (right, ps') -> Some (E_Compare CmpNe left right, ps')
         | None -> Some (left, ps))
      | None ->
        match ps_consume ps "=" with
        | Some ps' ->
          (match parse_additive_expr ps' prefixes with
           | Some (right, ps') -> Some (E_Compare CmpEq left right, ps')
           | None -> Some (left, ps))
        | None ->
          match ps_consume ps "<" with
          | Some ps' ->
            (match parse_additive_expr ps' prefixes with
             | Some (right, ps') -> Some (E_Compare CmpLt left right, ps')
             | None -> Some (left, ps))
          | None ->
            match ps_consume ps ">" with
            | Some ps' ->
              (match parse_additive_expr ps' prefixes with
               | Some (right, ps') -> Some (E_Compare CmpGt left right, ps')
               | None -> Some (left, ps))
            | None -> Some (left, ps)

and parse_additive_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  match parse_multiplicative_expr ps prefixes with
  | None -> None
  | Some (left, ps) ->
    let rec loop (left : expr) (ps : pstate) : (expr * pstate) =
      let ps' = skip_ws ps in
      match ps_peek ps' with
      | Some c when FStar.Char.int_of_char c = 0x2B (* '+' *) ->
        let ps' = ps_advance ps' 1 in
        (match parse_multiplicative_expr ps' prefixes with
         | Some (right, ps') -> loop (E_Arith Add left right) ps'
         | None -> (left, ps))
      | Some c when FStar.Char.int_of_char c = 0x2D (* '-' *) ->
        let ps' = ps_advance ps' 1 in
        (match parse_multiplicative_expr ps' prefixes with
         | Some (right, ps') -> loop (E_Arith Sub left right) ps'
         | None -> (left, ps))
      | _ -> (left, ps)
    in
    Some (loop left ps)

and parse_multiplicative_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  match parse_unary_expr ps prefixes with
  | None -> None
  | Some (left, ps) ->
    let rec loop (left : expr) (ps : pstate) : (expr * pstate) =
      let ps' = skip_ws ps in
      match ps_peek ps' with
      | Some c when FStar.Char.int_of_char c = 0x2A (* '*' *) ->
        let ps' = ps_advance ps' 1 in
        (match parse_unary_expr ps' prefixes with
         | Some (right, ps') -> loop (E_Arith Mul left right) ps'
         | None -> (left, ps))
      | Some c when FStar.Char.int_of_char c = 0x2F (* '/' *) ->
        let ps' = ps_advance ps' 1 in
        (match parse_unary_expr ps' prefixes with
         | Some (right, ps') -> loop (E_Arith Div left right) ps'
         | None -> (left, ps))
      | _ -> (left, ps)
    in
    Some (loop left ps)

and parse_unary_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  let ps = skip_ws ps in
  match ps_peek ps with
  | Some c when FStar.Char.int_of_char c = 0x21 (* '!' *) ->
    (* Check it's not != *)
    (match ps_char_at ps 1 with
     | Some c2 when FStar.Char.int_of_char c2 = 0x3D -> parse_primary_expr ps prefixes
     | _ ->
       let ps = ps_advance ps 1 in
       (match parse_primary_expr ps prefixes with
        | Some (e, ps) -> Some (E_Not e, ps)
        | None -> None))
  | Some c when FStar.Char.int_of_char c = 0x2D (* '-' *) ->
    let ps = ps_advance ps 1 in
    (match parse_primary_expr ps prefixes with
     | Some (e, ps) -> Some (E_UnaryMinus e, ps)
     | None -> None)
  | Some c when FStar.Char.int_of_char c = 0x2B (* '+' *) ->
    let ps = ps_advance ps 1 in
    parse_primary_expr ps prefixes
  | _ -> parse_primary_expr ps prefixes

and parse_primary_expr (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  let ps = skip_ws ps in
  (* Parenthesized expression *)
  match ps_peek ps with
  | Some c when FStar.Char.int_of_char c = 0x28 (* '(' *) ->
    let ps = ps_advance ps 1 in
    (match parse_expr ps prefixes with
     | Some (e, ps) ->
       (match ps_expect ps ")" with
        | Some ps -> Some (e, ps)
        | None -> None)
     | None -> None)
  | _ ->
    (* Variable *)
    match parse_variable ps with
    | Some (v, ps) -> Some (E_Var v, ps)
    | None ->
      (* Built-in functions *)
      match parse_builtin_call ps prefixes with
      | Some r -> Some r
      | None ->
        (* IRI (possibly function call) *)
        match parse_iri ps prefixes with
        | Some (iri, ps) ->
          (* Check for function call *)
          let ps' = skip_ws ps in
          (match ps_peek ps' with
           | Some c when FStar.Char.int_of_char c = 0x28 ->
             (match parse_expr_list ps' prefixes with
              | Some (args, ps') -> Some (E_FunctionCall iri args, ps')
              | None -> Some (E_IRI iri, ps))
           | _ -> Some (E_IRI iri, ps))
        | None ->
          (* RDF literal *)
          match parse_rdf_literal ps prefixes with
          | Some (lit, ps) -> Some (E_Literal lit, ps)
          | None ->
            (* Boolean *)
            match parse_boolean ps with
            | Some (b, ps) -> Some (E_BoolLit b, ps)
            | None ->
              (* Numeric *)
              parse_numeric ps

and parse_builtin_call (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  let ps = skip_ws ps in
  (* 1-arg builtins *)
  let try_1arg (kw : string) (mk : expr -> expr) : option (expr * pstate) =
    match ps_consume ps kw with
    | None -> None
    | Some ps ->
      let ps = skip_ws ps in
      match ps_expect ps "(" with
      | None -> None
      | Some ps ->
        match parse_expr ps prefixes with
        | None -> None
        | Some (e, ps) ->
          match ps_expect ps ")" with
          | None -> None
          | Some ps -> Some (mk e, ps)
  in
  (* 2-arg builtins *)
  let try_2arg (kw : string) (mk : expr -> expr -> expr) : option (expr * pstate) =
    match ps_consume ps kw with
    | None -> None
    | Some ps ->
      let ps = skip_ws ps in
      match ps_expect ps "(" with
      | None -> None
      | Some ps ->
        match parse_expr ps prefixes with
        | None -> None
        | Some (e1, ps) ->
          match ps_expect ps "," with
          | None -> None
          | Some ps ->
            match parse_expr ps prefixes with
            | None -> None
            | Some (e2, ps) ->
              match ps_expect ps ")" with
              | None -> None
              | Some ps -> Some (mk e1 e2, ps)
  in
  (* BOUND(?var) *)
  match ps_consume ps "BOUND" with
  | Some ps ->
    let ps = skip_ws ps in
    (match ps_expect ps "(" with
     | Some ps ->
       (match parse_variable ps with
        | Some (v, ps) ->
          (match ps_expect ps ")" with
           | Some ps -> Some (E_Bound v, ps)
           | None -> None)
        | None -> None)
     | None -> None)
  | None ->
  (* REGEX(str, pattern [, flags]) *)
  match ps_consume ps "REGEX" with
  | Some ps ->
    let ps = skip_ws ps in
    (match ps_expect ps "(" with
     | Some ps ->
       (match parse_expr ps prefixes with
        | Some (e1, ps) ->
          (match ps_expect ps "," with
           | Some ps ->
             (match parse_expr ps prefixes with
              | Some (e2, ps) ->
                let ps' = skip_ws ps in
                (match ps_consume ps' "," with
                 | Some ps' ->
                   (match parse_expr ps' prefixes with
                    | Some (e3, ps') ->
                      (match ps_expect ps' ")" with
                       | Some ps' -> Some (E_Regex e1 e2 (Some e3), ps')
                       | None -> None)
                    | None -> None)
                 | None ->
                   match ps_expect ps ")" with
                   | Some ps -> Some (E_Regex e1 e2 None, ps)
                   | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | None ->
  (* IF(cond, then, else) *)
  match ps_consume ps "IF" with
  | Some ps ->
    let ps = skip_ws ps in
    (match ps_expect ps "(" with
     | Some ps ->
       (match parse_expr ps prefixes with
        | Some (e1, ps) ->
          (match ps_expect ps "," with
           | Some ps ->
             (match parse_expr ps prefixes with
              | Some (e2, ps) ->
                (match ps_expect ps "," with
                 | Some ps ->
                   (match parse_expr ps prefixes with
                    | Some (e3, ps) ->
                      (match ps_expect ps ")" with
                       | Some ps -> Some (E_If e1 e2 e3, ps)
                       | None -> None)
                    | None -> None)
                 | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | None ->
  (* EXISTS { pattern } *)
  match ps_consume ps "EXISTS" with
  | Some ps ->
    (match parse_group_graph_pattern ps prefixes with
     | Some (p, ps) -> Some (E_Exists p, ps)
     | None -> None)
  | None ->
  (* NOT EXISTS { pattern } *)
  (let ps0 = ps in
   match ps_consume ps "NOT" with
   | Some ps ->
     let ps = skip_ws ps in
     (match ps_consume ps "EXISTS" with
      | Some ps ->
        (match parse_group_graph_pattern ps prefixes with
         | Some (p, ps) -> Some (E_NotExists p, ps)
         | None -> None)
      | None ->
        (* Try 1-arg builtins with the original ps *)
        let ps = ps0 in
        try_1arg_fallback ps prefixes)
   | None -> try_1arg_fallback ps prefixes)

and try_1arg_fallback (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  let try1 kw mk =
    match ps_consume ps kw with
    | None -> None
    | Some ps' ->
      let ps' = skip_ws ps' in
      match ps_expect ps' "(" with
      | None -> None
      | Some ps' ->
        match parse_expr ps' prefixes with
        | None -> None
        | Some (e, ps') ->
          match ps_expect ps' ")" with
          | None -> None
          | Some ps' -> Some (mk e, ps')
  in
  (* Try all 1-arg builtins *)
  match try1 "ISIRI" (fun e -> E_IsIRI e) with | Some r -> Some r | None ->
  match try1 "ISURI" (fun e -> E_IsIRI e) with | Some r -> Some r | None ->
  match try1 "ISBLANK" (fun e -> E_IsBlank e) with | Some r -> Some r | None ->
  match try1 "ISLITERAL" (fun e -> E_IsLiteral e) with | Some r -> Some r | None ->
  match try1 "ISNUMERIC" (fun e -> E_IsNumeric e) with | Some r -> Some r | None ->
  match try1 "STR" (fun e -> E_Str e) with | Some r -> Some r | None ->
  match try1 "LANG" (fun e -> E_Lang e) with | Some r -> Some r | None ->
  match try1 "DATATYPE" (fun e -> E_Datatype e) with | Some r -> Some r | None ->
  match try1 "IRI" (fun e -> E_IRI_fn e) with | Some r -> Some r | None ->
  match try1 "URI" (fun e -> E_IRI_fn e) with | Some r -> Some r | None ->
  match try1 "STRLEN" (fun e -> E_StrLen e) with | Some r -> Some r | None ->
  match try1 "UCASE" (fun e -> E_UCase e) with | Some r -> Some r | None ->
  match try1 "LCASE" (fun e -> E_LCase e) with | Some r -> Some r | None ->
  match try1 "ENCODE_FOR_URI" (fun e -> E_EncodeForUri e) with | Some r -> Some r | None ->
  match try1 "ABS" (fun e -> E_Abs e) with | Some r -> Some r | None ->
  match try1 "ROUND" (fun e -> E_Round e) with | Some r -> Some r | None ->
  match try1 "CEIL" (fun e -> E_Ceil e) with | Some r -> Some r | None ->
  match try1 "FLOOR" (fun e -> E_Floor e) with | Some r -> Some r | None ->
  match try1 "MD5" (fun e -> E_MD5 e) with | Some r -> Some r | None ->
  match try1 "SHA1" (fun e -> E_SHA1 e) with | Some r -> Some r | None ->
  match try1 "SHA256" (fun e -> E_SHA256 e) with | Some r -> Some r | None ->
  match try1 "SHA384" (fun e -> E_SHA384 e) with | Some r -> Some r | None ->
  match try1 "SHA512" (fun e -> E_SHA512 e) with | Some r -> Some r | None ->
  match try1 "YEAR" (fun e -> E_Year e) with | Some r -> Some r | None ->
  match try1 "MONTH" (fun e -> E_Month e) with | Some r -> Some r | None ->
  match try1 "DAY" (fun e -> E_Day e) with | Some r -> Some r | None ->
  match try1 "HOURS" (fun e -> E_Hours e) with | Some r -> Some r | None ->
  match try1 "MINUTES" (fun e -> E_Minutes e) with | Some r -> Some r | None ->
  match try1 "SECONDS" (fun e -> E_Seconds e) with | Some r -> Some r | None ->
  match try1 "TIMEZONE" (fun e -> E_Timezone e) with | Some r -> Some r | None ->
  match try1 "TZ" (fun e -> E_Tz e) with | Some r -> Some r | None ->
  (* 2-arg builtins *)
  let try2 kw mk =
    match ps_consume ps kw with
    | None -> None
    | Some ps' ->
      let ps' = skip_ws ps' in
      match ps_expect ps' "(" with
      | None -> None
      | Some ps' ->
        match parse_expr ps' prefixes with
        | None -> None
        | Some (e1, ps') ->
          match ps_expect ps' "," with
          | None -> None
          | Some ps' ->
            match parse_expr ps' prefixes with
            | None -> None
            | Some (e2, ps') ->
              match ps_expect ps' ")" with
              | None -> None
              | Some ps' -> Some (mk e1 e2, ps')
  in
  match try2 "LANGMATCHES" (fun a b -> E_FunctionCall "sparql:langMatches" [a; b]) with | Some r -> Some r | None ->
  match try2 "STRSTARTS" (fun a b -> E_StrStarts a b) with | Some r -> Some r | None ->
  match try2 "STRENDS" (fun a b -> E_StrEnds a b) with | Some r -> Some r | None ->
  match try2 "CONTAINS" (fun a b -> E_Contains a b) with | Some r -> Some r | None ->
  match try2 "STRBEFORE" (fun a b -> E_StrBefore a b) with | Some r -> Some r | None ->
  match try2 "STRAFTER" (fun a b -> E_StrAfter a b) with | Some r -> Some r | None ->
  match try2 "STRDT" (fun a b -> E_StrDt a b) with | Some r -> Some r | None ->
  match try2 "STRLANG" (fun a b -> E_StrLang a b) with | Some r -> Some r | None ->
  match try2 "SAMETERM" (fun a b -> E_SameTerm a b) with | Some r -> Some r | None ->
  (* REPLACE(str, pattern, replacement [, flags]) *)
  match ps_consume ps "REPLACE" with
  | Some ps' ->
    let ps' = skip_ws ps' in
    (match ps_expect ps' "(" with
     | Some ps' ->
       (match parse_expr ps' prefixes with
        | Some (e1, ps') ->
          (match ps_expect ps' "," with
           | Some ps' ->
             (match parse_expr ps' prefixes with
              | Some (e2, ps') ->
                (match ps_expect ps' "," with
                 | Some ps' ->
                   (match parse_expr ps' prefixes with
                    | Some (e3, ps') ->
                      let ps'' = skip_ws ps' in
                      (match ps_consume ps'' "," with
                       | Some ps'' ->
                         (match parse_expr ps'' prefixes with
                          | Some (e4, ps'') ->
                            (match ps_expect ps'' ")" with
                             | Some ps'' -> Some (E_Replace e1 e2 e3 (Some e4), ps'')
                             | None -> None)
                          | None -> None)
                       | None ->
                         match ps_expect ps' ")" with
                         | Some ps' -> Some (E_Replace e1 e2 e3 None, ps')
                         | None -> None)
                    | None -> None)
                 | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | None ->
  (* NOW() — zero-arg *)
  match ps_consume ps "NOW" with
  | Some ps' ->
    let ps' = skip_ws ps' in
    (match ps_expect ps' "(" with
     | Some ps' ->
       (match ps_expect ps' ")" with
        | Some ps' -> Some (E_Now, ps')
        | None -> None)
     | None -> None)
  | None ->
  (* BNODE — zero or one arg *)
  match ps_consume ps "BNODE" with
  | Some ps' ->
    let ps' = skip_ws ps' in
    (match ps_expect ps' "(" with
     | Some ps' ->
       let ps' = skip_ws ps' in
       (match ps_peek ps' with
        | Some c when FStar.Char.int_of_char c = 0x29 (* ')' *) ->
          Some (E_FunctionCall "sparql:bnode" [], ps_advance ps' 1)
        | _ ->
          match parse_expr ps' prefixes with
          | Some (e, ps') ->
            (match ps_expect ps' ")" with
             | Some ps' -> Some (E_FunctionCall "sparql:bnode" [e], ps')
             | None -> None)
          | None -> None)
     | None -> None)
  | None ->
  (* SUBSTR(str, start [, len]) *)
  match ps_consume ps "SUBSTR" with
  | Some ps' ->
    let ps' = skip_ws ps' in
    (match ps_expect ps' "(" with
     | Some ps' ->
       (match parse_expr ps' prefixes with
        | Some (e1, ps') ->
          (match ps_expect ps' "," with
           | Some ps' ->
             (match parse_expr ps' prefixes with
              | Some (e2, ps') ->
                let ps'' = skip_ws ps' in
                (match ps_consume ps'' "," with
                 | Some ps'' ->
                   (match parse_expr ps'' prefixes with
                    | Some (e3, ps'') ->
                      (match ps_expect ps'' ")" with
                       | Some ps'' -> Some (E_Substr e1 e2 (Some e3), ps'')
                       | None -> None)
                    | None -> None)
                 | None ->
                   match ps_expect ps' ")" with
                   | Some ps' -> Some (E_Substr e1 e2 None, ps')
                   | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | None ->
  (* COALESCE(expr, ...) *)
  match ps_consume ps "COALESCE" with
  | Some ps' ->
    (match parse_expr_list ps' prefixes with
     | Some (args, ps') -> Some (E_Coalesce args, ps')
     | None -> None)
  | None ->
  (* CONCAT(expr, ...) *)
  match ps_consume ps "CONCAT" with
  | Some ps' ->
    (match parse_expr_list ps' prefixes with
     | Some (args, ps') -> Some (E_Concat args, ps')
     | None -> None)
  | None ->
  None

and parse_expr_list (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list expr * pstate) =
  let ps = skip_ws ps in
  match ps_expect ps "(" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    match ps_peek ps with
    | Some c when FStar.Char.int_of_char c = 0x29 (* ')' *) ->
      Some ([], ps_advance ps 1)
    | _ ->
      match parse_expr ps prefixes with
      | None -> None
      | Some (e, ps) ->
        let rec loop (acc : list expr) (ps : pstate) : option (list expr * pstate) =
          let ps = skip_ws ps in
          match ps_consume ps "," with
          | Some ps ->
            (match parse_expr ps prefixes with
             | Some (e, ps) -> loop (e :: acc) ps
             | None -> None)
          | None ->
            match ps_expect ps ")" with
            | Some ps -> Some (List.Tot.rev (e :: acc), ps)
            | None -> None
        in
        loop [] ps

(** ====================================================================== **)
(** Triple pattern and group graph pattern parser                           **)
(** ====================================================================== **)

and parse_pattern_subject (ps : pstate) (prefixes : list (string * wf_iri))
  : option (pattern_subject * pstate) =
  match parse_variable ps with
  | Some (v, ps) -> Some (PS_Var v, ps)
  | None ->
    match parse_iri ps prefixes with
    | Some (iri, ps) -> Some (PS_IRI iri, ps)
    | None ->
      (* Blank node _:label *)
      let ps = skip_ws ps in
      match ps_consume ps "_:" with
      | Some ps ->
        let rec collect (ps : pstate) (acc : list FStar.Char.char) : (string * pstate) =
          match ps_peek ps with
          | Some c when is_pn_chars c -> collect (ps_advance ps 1) (c :: acc)
          | _ -> (String.string_of_list (List.Tot.rev acc), ps)
        in
        let (label, ps) = collect ps [] in
        Some (PS_BNode label, ps)
      | None ->
        (* Anonymous blank node [] *)
        match ps_consume ps "[" with
        | Some ps ->
          let ps = skip_ws ps in
          (match ps_consume ps "]" with
           | Some ps -> Some (PS_BNode "anon", ps)  (* simplified *)
           | None -> None)
        | None ->
          (* RDF list syntax: () is rdf:nil *)
          let ps = skip_ws ps in
          match ps_consume ps "()" with
          | Some ps ->
            let rdf_nil = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
            Some (PS_IRI rdf_nil, ps)
          | None -> None

and parse_pattern_term (ps : pstate) (prefixes : list (string * wf_iri))
  : option (pattern_term * pstate) =
  match parse_variable ps with
  | Some (v, ps) -> Some (PT_Var v, ps)
  | None ->
    match parse_iri ps prefixes with
    | Some (iri, ps) -> Some (PT_IRI iri, ps)
    | None ->
      match parse_rdf_literal ps prefixes with
      | Some (lit, ps) -> Some (PT_Literal lit, ps)
      | None ->
        (* Boolean literal *)
        match parse_boolean ps with
        | Some (b, ps) ->
          let lit : wf_literal = {
            lexical_form = (if b then "true" else "false");
            datatype = xsd_boolean;
            lang_tag = None;
          } in
          Some (PT_Literal lit, ps)
        | None ->
          (* Numeric literal — integer, decimal, double *)
          let ps_start = ps in
          let ps = skip_ws ps in
          let start = ps.pos in
          let has_sign = match ps_peek ps with
            | Some c -> FStar.Char.int_of_char c = 0x2B || FStar.Char.int_of_char c = 0x2D
            | None -> false
          in
          let ps = if has_sign then ps_advance ps 1 else ps in
          let rec digits (ps : pstate) : pstate =
            match ps_peek ps with
            | Some c when is_digit c -> digits (ps_advance ps 1)
            | _ -> ps
          in
          let ps_d = digits ps in
          if ps_d.pos > ps.pos || (match ps_peek ps with | Some c -> FStar.Char.int_of_char c = 0x2E | None -> false) then
            (* Check for decimal/double *)
            match ps_peek ps_d with
            | Some c when FStar.Char.int_of_char c = 0x2E ->
              let ps2 = digits (ps_advance ps_d 1) in
              let s = String.sub ps_start.inp start (ps2.pos - start) in
              let lit : wf_literal = {
                lexical_form = s;
                datatype = xsd_decimal;
                lang_tag = None;
              } in
              Some (PT_Literal lit, ps2)
            | _ ->
              let s = String.sub ps_start.inp start (ps_d.pos - start) in
              let lit : wf_literal = {
                lexical_form = s;
                datatype = xsd_integer;
                lang_tag = None;
              } in
              Some (PT_Literal lit, ps_d)
          else
            (* Blank node _:label *)
            match ps_consume ps_start "_:" with
            | Some ps ->
              let (label, ps) =
                let rec collect (ps : pstate) (acc : list FStar.Char.char) : (string * pstate) =
                  match ps_peek ps with
                  | Some c when is_pn_chars c -> collect (ps_advance ps 1) (c :: acc)
                  | _ -> (String.string_of_list (List.Tot.rev acc), ps)
                in
                collect ps []
              in
              Some (PT_BNode label, ps)
            | None ->
              (* RDF list syntax: () is rdf:nil *)
              let ps0 = skip_ws ps_start in
              match ps_consume ps0 "()" with
              | Some ps0 ->
                let rdf_nil = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" in
                Some (PT_IRI rdf_nil, ps0)
              | None -> None

(** Parse triple patterns within a group, handling ';' and ',' shortcuts **)
and parse_triples_block (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list triple_pattern * pstate) =
  match parse_pattern_subject ps prefixes with
  | None -> Some ([], ps)
  | Some (subj, ps) ->
    parse_predicate_object_list subj ps prefixes

and parse_predicate_object_list (subj : pattern_subject) (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list triple_pattern * pstate) =
  let ps = skip_ws ps in
  (* Check for 'a' shortcut for rdf:type *)
  let parse_pred (ps : pstate) : option (pattern_term * pstate) =
    let ps = skip_ws ps in
    match ps_peek ps with
    | Some c when FStar.Char.int_of_char c = 0x61 (* 'a' *) ->
      (* Check next char is not alphanumeric (so it's the keyword 'a', not part of a name) *)
      (match ps_char_at ps 1 with
       | Some c2 when is_pn_chars c2 -> parse_pattern_term ps prefixes
       | _ ->
         let rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in
         Some (PT_IRI rdf_type, ps_advance ps 1))
    | _ -> parse_pattern_term ps prefixes
  in
  match parse_pred ps with
  | None -> Some ([], ps)
  | Some (pred, ps) ->
    match parse_object_list subj pred ps prefixes with
    | None -> None
    | Some (triples, ps) ->
      (* Check for ';' — another predicate-object pair *)
      let ps' = skip_ws ps in
      match ps_consume ps' ";" with
      | Some ps' ->
        let ps' = skip_ws ps' in
        (* Allow trailing semicolon *)
        (match ps_peek ps' with
         | Some c when FStar.Char.int_of_char c = 0x7D (* '}' *) || FStar.Char.int_of_char c = 0x2E (* '.' *) ->
           Some (triples, ps')
         | None -> Some (triples, ps')
         | _ ->
           match parse_predicate_object_list subj ps' prefixes with
           | Some (more, ps') -> Some (triples @ more, ps')
           | None -> Some (triples, ps'))
      | None -> Some (triples, ps)

and parse_object_list (subj : pattern_subject) (pred : pattern_term) (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list triple_pattern * pstate) =
  let ps = skip_ws ps in
  match parse_pattern_term ps prefixes with
  | None -> None
  | Some (obj, ps) ->
    let tp = { tp_s = subj; tp_p = pred; tp_o = obj } in
    (* Check for ',' — another object *)
    let ps' = skip_ws ps in
    match ps_consume ps' "," with
    | Some ps' ->
      (match parse_object_list subj pred ps' prefixes with
       | Some (more, ps') -> Some (tp :: more, ps')
       | None -> Some ([tp], ps))
    | None -> Some ([tp], ps)

(** Parse a group graph pattern: { ... } **)
and parse_group_graph_pattern (ps : pstate) (prefixes : list (string * wf_iri))
  : option (group_graph_pattern * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "{" with
  | None -> None
  | Some ps ->
    match parse_ggp_body ps prefixes with
    | None -> None
    | Some (pattern, ps) ->
      match ps_expect ps "}" with
      | None -> None
      | Some ps -> Some (pattern, ps)

and parse_ggp_body (ps : pstate) (prefixes : list (string * wf_iri))
  : option (group_graph_pattern * pstate) =
  let ps = skip_ws ps in
  (* Check for empty group *)
  match ps_peek ps with
  | Some c when FStar.Char.int_of_char c = 0x7D (* '}' *) ->
    Some (GP_Empty, ps)
  | _ ->
    (* Try to parse elements *)
    parse_ggp_elements ps prefixes GP_Empty

and parse_ggp_elements (ps : pstate) (prefixes : list (string * wf_iri)) (acc : group_graph_pattern)
  : option (group_graph_pattern * pstate) =
  let ps = skip_ws ps in
  match ps_peek ps with
  | None -> Some (acc, ps)
  | Some c when FStar.Char.int_of_char c = 0x7D (* '}' *) -> Some (acc, ps)
  | _ ->
    (* Try OPTIONAL *)
    match ps_consume ps "OPTIONAL" with
    | Some ps_after ->
      (match parse_group_graph_pattern ps_after prefixes with
       | Some (opt_pat, ps') ->
         let new_acc = GP_LeftJoin acc opt_pat (E_BoolLit true) in
         (* Skip optional trailing dot after OPTIONAL block *)
         let ps' = skip_ws ps' in
         let ps' = match ps_consume ps' "." with | Some p -> p | None -> ps' in
         parse_ggp_elements ps' prefixes new_acc
       | None -> Some (acc, ps))
    | None ->
    (* Try FILTER *)
    match ps_consume ps "FILTER" with
    | Some ps_after ->
      let ps_after = skip_ws ps_after in
      (* FILTER can be FILTER(expr) or FILTER expr *)
      (match parse_filter_constraint ps_after prefixes with
       | Some (filter_expr, ps') ->
         let new_acc = GP_Filter filter_expr acc in
         (* Skip optional '.' *)
         let ps' = skip_ws ps' in
         let ps' = match ps_consume ps' "." with | Some ps' -> ps' | None -> ps' in
         parse_ggp_elements ps' prefixes new_acc
       | None -> Some (acc, ps))
    | None ->
    (* Try UNION — after a group *)
    match ps_consume ps "UNION" with
    | Some ps_after ->
      (match parse_group_graph_pattern ps_after prefixes with
       | Some (right, ps') ->
         let new_acc = GP_Union acc right in
         parse_ggp_elements ps' prefixes new_acc
       | None -> Some (acc, ps))
    | None ->
    (* Try BIND(expr AS ?var) *)
    match ps_consume ps "BIND" with
    | Some ps_after ->
      let ps_after = skip_ws ps_after in
      (match ps_expect ps_after "(" with
       | Some ps' ->
         (match parse_expr ps' prefixes with
          | Some (e, ps') ->
            let ps' = skip_ws ps' in
            (match ps_consume ps' "AS" with
             | Some ps' ->
               (match parse_variable ps' with
                | Some (v, ps') ->
                  (match ps_expect ps' ")" with
                   | Some ps' ->
                     let new_acc = GP_Bind e v acc in
                     let ps' = skip_ws ps' in
                     let ps' = match ps_consume ps' "." with | Some p -> p | None -> ps' in
                     parse_ggp_elements ps' prefixes new_acc
                   | None -> Some (acc, ps))
                | None -> Some (acc, ps))
             | None -> Some (acc, ps))
          | None -> Some (acc, ps))
       | None -> Some (acc, ps))
    | None ->
    (* Try VALUES *)
    match ps_consume ps "VALUES" with
    | Some ps_after ->
      (match parse_values_clause ps_after prefixes with
       | Some (vars, rows, ps') ->
         let new_acc = if acc = GP_Empty then GP_Values vars rows
                       else GP_Join acc (GP_Values vars rows) in
         parse_ggp_elements ps' prefixes new_acc
       | None -> Some (acc, ps))
    | None ->
    (* Try sub-group { ... } *)
    match ps_peek ps with
    | Some c when FStar.Char.int_of_char c = 0x7B (* '{' *) ->
      (match parse_group_graph_pattern ps prefixes with
       | Some (sub, ps') ->
         let new_acc = if acc = GP_Empty then sub
                       else GP_Join acc sub in
         (* Check for UNION after sub-group *)
         let ps' = skip_ws ps' in
         (match ps_consume ps' "UNION" with
          | Some ps'' ->
            (match parse_group_graph_pattern ps'' prefixes with
             | Some (right, ps'') ->
               let new_acc = GP_Union new_acc right in
               parse_ggp_elements ps'' prefixes new_acc
             | None -> parse_ggp_elements ps' prefixes new_acc)
          | None -> parse_ggp_elements ps' prefixes new_acc)
       | None -> Some (acc, ps))
    | _ ->
    (* Try triple patterns *)
    match parse_triples_block ps prefixes with
    | Some (tps, ps') when not (Nil? tps) ->
      let bgp_pat = GP_BGP tps in
      let new_acc = if acc = GP_Empty then bgp_pat
                    else GP_Join acc bgp_pat in
      (* Skip optional '.' *)
      let ps' = skip_ws ps' in
      let ps' = match ps_consume ps' "." with | Some p -> p | None -> ps' in
      parse_ggp_elements ps' prefixes new_acc
    | _ -> Some (acc, ps)

and parse_filter_constraint (ps : pstate) (prefixes : list (string * wf_iri))
  : option (expr * pstate) =
  match ps_peek ps with
  | Some c when FStar.Char.int_of_char c = 0x28 (* '(' *) ->
    let ps = ps_advance ps 1 in
    (match parse_expr ps prefixes with
     | Some (e, ps) ->
       (match ps_expect ps ")" with
        | Some ps -> Some (e, ps)
        | None -> None)
     | None -> None)
  | _ -> parse_builtin_call ps prefixes

and parse_values_clause (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list var_name * list (list (option rdf_term)) * pstate) =
  let ps = skip_ws ps in
  (* Parse variable list — either single ?var or ( ?var1 ?var2 ... ) *)
  let parse_var_list (ps : pstate) : option (list var_name * pstate) =
    match ps_consume ps "(" with
    | Some ps ->
      let rec loop (acc : list var_name) (ps : pstate) : option (list var_name * pstate) =
        let ps = skip_ws ps in
        match parse_variable ps with
        | Some (v, ps) -> loop (v :: acc) ps
        | None ->
          match ps_expect ps ")" with
          | Some ps -> Some (List.Tot.rev acc, ps)
          | None -> None
      in
      loop [] ps
    | None ->
      match parse_variable ps with
      | Some (v, ps) -> Some ([v], ps)
      | None -> None
  in
  match parse_var_list ps with
  | None -> None
  | Some (vars, ps) ->
    let ps = skip_ws ps in
    match ps_consume ps "{" with
    | None -> None
    | Some ps ->
      let n_vars = List.Tot.length vars in
      let rec parse_rows (acc : list (list (option rdf_term))) (ps : pstate) : option (list (list (option rdf_term)) * pstate) =
        let ps = skip_ws ps in
        match ps_consume ps "}" with
        | Some ps -> Some (List.Tot.rev acc, ps)
        | None ->
          match ps_consume ps "(" with
          | Some ps ->
            let rec parse_row (acc : list (option rdf_term)) (ps : pstate) : option (list (option rdf_term) * pstate) =
              let ps = skip_ws ps in
              match ps_consume ps ")" with
              | Some ps -> Some (List.Tot.rev acc, ps)
              | None ->
                match ps_consume ps "UNDEF" with
                | Some ps -> parse_row (None :: acc) ps
                | None ->
                  (* Parse a term *)
                  match parse_iri ps prefixes with
                  | Some (iri, ps) -> parse_row (Some (T_IRI iri) :: acc) ps
                  | None ->
                    match parse_rdf_literal ps prefixes with
                    | Some (lit, ps) -> parse_row (Some (T_Literal lit) :: acc) ps
                    | None -> None
            in
            (match parse_row [] ps with
             | Some (row, ps) -> parse_rows (row :: acc) ps
             | None -> None)
          | None -> None
      in
      (match parse_rows [] ps with
       | Some (rows, ps) -> Some (vars, rows, ps)
       | None -> None)

(** ====================================================================== **)
(** SELECT clause parser                                                    **)
(** ====================================================================== **)

let parse_select_clause (ps : pstate) (prefixes : list (string * wf_iri))
  : option (select_clause * bool * bool * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "SELECT" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    (* DISTINCT / REDUCED *)
    let (is_distinct, is_reduced, ps) =
      match ps_consume ps "DISTINCT" with
      | Some ps -> (true, false, ps)
      | None ->
        match ps_consume ps "REDUCED" with
        | Some ps -> (false, true, ps)
        | None -> (false, false, ps)
    in
    let ps = skip_ws ps in
    (* * or variable list *)
    match ps_consume ps "*" with
    | Some ps -> Some (Select_All, is_distinct, is_reduced, ps)
    | None ->
      let rec parse_items (acc : list select_item) (ps : pstate) : option (list select_item * pstate) =
        let ps = skip_ws ps in
        (* Try (expr AS ?var) *)
        match ps_peek ps with
        | Some c when FStar.Char.int_of_char c = 0x28 (* '(' *) ->
          let ps' = ps_advance ps 1 in
          (match parse_expr ps' prefixes with
           | Some (e, ps') ->
             let ps' = skip_ws ps' in
             (match ps_consume ps' "AS" with
              | Some ps' ->
                (match parse_variable ps' with
                 | Some (v, ps') ->
                   (match ps_expect ps' ")" with
                    | Some ps' -> parse_items (SI_Expr e v :: acc) ps'
                    | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
                 | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
              | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
           | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
        | _ ->
          match parse_variable ps with
          | Some (v, ps) -> parse_items (SI_Var v :: acc) ps
          | None ->
            if Nil? acc then None
            else Some (List.Tot.rev acc, ps)
      in
      match parse_items [] ps with
      | Some (items, ps) -> Some (Select_Vars items, is_distinct, is_reduced, ps)
      | None -> None

(** ====================================================================== **)
(** ORDER BY, LIMIT, OFFSET, GROUP BY, HAVING                               **)
(** ====================================================================== **)

let rec parse_order_by (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list order_condition * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "ORDER" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    match ps_consume ps "BY" with
    | None -> None
    | Some ps ->
      let rec parse_conditions (acc : list order_condition) (ps : pstate)
        : option (list order_condition * pstate) =
        let ps = skip_ws ps in
        match ps_consume ps "ASC" with
        | Some ps' ->
          let ps' = skip_ws ps' in
          (match ps_expect ps' "(" with
           | Some ps' ->
             (match parse_expr ps' prefixes with
              | Some (e, ps') ->
                (match ps_expect ps' ")" with
                 | Some ps' -> parse_conditions (OC_Asc e :: acc) ps'
                 | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
              | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
           | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
        | None ->
          match ps_consume ps "DESC" with
          | Some ps' ->
            let ps' = skip_ws ps' in
            (match ps_expect ps' "(" with
             | Some ps' ->
               (match parse_expr ps' prefixes with
                | Some (e, ps') ->
                  (match ps_expect ps' ")" with
                   | Some ps' -> parse_conditions (OC_Desc e :: acc) ps'
                   | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
                | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
             | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
          | None ->
            (* Bare expression — treated as ASC *)
            match parse_expr ps prefixes with
            | Some (e, ps) -> parse_conditions (OC_Asc e :: acc) ps
            | None ->
              if Nil? acc then None
              else Some (List.Tot.rev acc, ps)
      in
      parse_conditions [] ps

assume val parse_nat_digits : pstate -> option (nat * pstate)

let parse_limit (ps : pstate) : option (nat * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "LIMIT" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    parse_nat_digits ps

let parse_offset (ps : pstate) : option (nat * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "OFFSET" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    parse_nat_digits ps

let rec parse_group_by (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list group_condition * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "GROUP" with
  | None -> None
  | Some ps ->
    let ps = skip_ws ps in
    match ps_consume ps "BY" with
    | None -> None
    | Some ps ->
      let rec parse_conditions (acc : list group_condition) (ps : pstate)
        : option (list group_condition * pstate) =
        let ps = skip_ws ps in
        match parse_variable ps with
        | Some (v, ps) -> parse_conditions (GC_Var v :: acc) ps
        | None ->
          (* Try (expr AS ?var) or just (expr) *)
          (match ps_peek ps with
           | Some c when FStar.Char.int_of_char c = 0x28 ->
             let ps' = ps_advance ps 1 in
             (match parse_expr ps' prefixes with
              | Some (e, ps') ->
                let ps' = skip_ws ps' in
                (match ps_consume ps' "AS" with
                 | Some ps' ->
                   (match parse_variable ps' with
                    | Some (v, ps') ->
                      (match ps_expect ps' ")" with
                       | Some ps' -> parse_conditions (GC_Expr e (Some v) :: acc) ps'
                       | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
                    | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
                 | None ->
                   match ps_expect ps' ")" with
                   | Some ps' -> parse_conditions (GC_Expr e None :: acc) ps'
                   | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
              | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
           | _ ->
             if Nil? acc then None
             else Some (List.Tot.rev acc, ps))
      in
      parse_conditions [] ps

let rec parse_having (ps : pstate) (prefixes : list (string * wf_iri))
  : option (list having_condition * pstate) =
  let ps = skip_ws ps in
  match ps_consume ps "HAVING" with
  | None -> None
  | Some ps ->
    let rec parse_conditions (acc : list expr) (ps : pstate)
      : option (list expr * pstate) =
      let ps = skip_ws ps in
      match ps_peek ps with
      | Some c when FStar.Char.int_of_char c = 0x28 ->
        let ps' = ps_advance ps 1 in
        (match parse_expr ps' prefixes with
         | Some (e, ps') ->
           (match ps_expect ps' ")" with
            | Some ps' -> parse_conditions (e :: acc) ps'
            | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
         | None -> if Nil? acc then None else Some (List.Tot.rev acc, ps))
      | _ ->
        if Nil? acc then None
        else Some (List.Tot.rev acc, ps)
    in
    parse_conditions [] ps

(** ====================================================================== **)
(** Top-level query parser                                                  **)
(** ====================================================================== **)

let parse_query (input : string) : option query =
  let ps = mk_pstate input in
  let (base, prefixes, ps) = parse_prologue ps None [] in
  (* Store base in prefixes for IRI resolution *)
  let prefixes = match base with
    | Some b -> ("__base__", b) :: prefixes
    | None -> prefixes
  in
  (* Parse query form *)
  let ps = skip_ws ps in
  match ps_consume ps "ASK" with
  | Some ps ->
    (* ASK query *)
    (match parse_group_graph_pattern ps prefixes with
     | Some (pattern, ps) ->
       Some ({
         q_base = base;
         q_prefixes = prefixes;
         q_form = QF_Ask;
         q_dataset = [];
         q_pattern = pattern;
         q_group_by = None;
         q_having = None;
         q_modifier = {
           sm_order_by = None;
           sm_distinct = false;
           sm_reduced = false;
           sm_offset = None;
           sm_limit = None;
         };
       })
     | None -> None)
  | None ->
    match parse_select_clause ps prefixes with
    | None -> None
    | Some (sel, distinct, reduced, ps) ->
      let ps = skip_ws ps in
      (* Skip FROM clauses *)
      let rec skip_from (ps : pstate) : pstate =
        let ps = skip_ws ps in
        match ps_consume ps "FROM" with
        | Some ps ->
          let ps = skip_ws ps in
          let ps = match ps_consume ps "NAMED" with | Some ps -> ps | None -> ps in
          let ps = skip_ws ps in
          let ps = match parse_iriref ps with | Some (_, ps) -> ps | None -> ps in
          skip_from ps
        | None -> ps
      in
      let ps = skip_from ps in
      (* WHERE clause *)
      let ps = skip_ws ps in
      let ps = match ps_consume ps "WHERE" with | Some ps -> ps | None -> ps in
      match parse_group_graph_pattern ps prefixes with
      | None -> None
      | Some (pattern, ps) ->
        (* Solution modifiers *)
        let group_by = parse_group_by ps prefixes in
        let (gb, ps) = match group_by with
          | Some (gc, ps) -> (Some gc, ps)
          | None -> (None, ps)
        in
        let having = parse_having ps prefixes in
        let (hv, ps) = match having with
          | Some (hc, ps) -> (Some hc, ps)
          | None -> (None, ps)
        in
        let order = parse_order_by ps prefixes in
        let (ob, ps) = match order with
          | Some (oc, ps) -> (Some oc, ps)
          | None -> (None, ps)
        in
        let lim = parse_limit ps in
        let (l, ps) = match lim with
          | Some (n, ps) -> (Some n, ps)
          | None -> (None, ps)
        in
        let off = parse_offset ps in
        let (o, ps) = match off with
          | Some (n, ps) -> (Some n, ps)
          | None -> (None, ps)
        in
        (* Also try LIMIT after OFFSET *)
        let (l, ps) = match l with
          | Some _ -> (l, ps)
          | None ->
            match parse_limit ps with
            | Some (n, ps) -> (Some n, ps)
            | None -> (l, ps)
        in
        Some ({
          q_base = base;
          q_prefixes = prefixes;
          q_form = QF_Select sel;
          q_dataset = [];
          q_pattern = pattern;
          q_group_by = gb;
          q_having = hv;
          q_modifier = {
            sm_order_by = ob;
            sm_distinct = distinct;
            sm_reduced = reduced;
            sm_offset = o;
            sm_limit = l;
          };
        })
