open Prims
let rec drop_ws (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with | 32::r -> drop_ws r | 9::r -> drop_ws r | uu___ -> cs
let lstrip (s : Prims.string) : Prims.string=
  FStar_String.string_of_list (drop_ws (FStar_String.list_of_string s))
let starts_with (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  let n = FStar_String.strlen pfx in
  ((FStar_String.strlen s) >= n) &&
    ((FStar_String.sub s Prims.int_zero n) = pfx)
let rec chars_prefix_match (n : FStar_Char.char Prims.list)
  (h : FStar_Char.char Prims.list) : Prims.bool=
  match (n, h) with
  | ([], uu___) -> true
  | (uu___, []) -> false
  | (a::n', b::h') -> (a = b) && (chars_prefix_match n' h')
let rec chars_drop (k : Prims.nat) (l : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match (k, l) with
  | (uu___, uu___1) when uu___ = Prims.int_zero -> l
  | (uu___, []) -> []
  | (uu___, uu___1::t) -> chars_drop (k - Prims.int_one) t
let rec replace_all_chars (fuel : Prims.nat)
  (cs : FStar_Char.char Prims.list) (needle : FStar_Char.char Prims.list)
  (repl : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  if fuel = Prims.int_zero
  then cs
  else
    (match cs with
     | [] -> []
     | c::rest ->
         if (Prims.uu___is_Cons needle) && (chars_prefix_match needle cs)
         then
           FStar_List_Tot_Base.op_At repl
             (replace_all_chars (fuel - Prims.int_one)
                (chars_drop (FStar_List_Tot_Base.length needle) cs) needle
                repl)
         else c ::
           (replace_all_chars (fuel - Prims.int_one) rest needle repl))
let replace_all (s : Prims.string) (needle : Prims.string)
  (repl : Prims.string) : Prims.string=
  let cs = FStar_String.list_of_string s in
  FStar_String.string_of_list
    (replace_all_chars ((FStar_String.strlen s) + Prims.int_one) cs
       (FStar_String.list_of_string needle)
       (FStar_String.list_of_string repl))
let line_kind (line : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option=
  let t = lstrip line in
  if starts_with t "RULE"
  then FStar_Pervasives_Native.Some true
  else
    if starts_with t "DATA"
    then FStar_Pervasives_Native.Some false
    else FStar_Pervasives_Native.None
let line_body (line : Prims.string) : Prims.string=
  let t = lstrip line in
  if (FStar_String.strlen t) >= (Prims.of_int (4))
  then
    FStar_String.sub t (Prims.of_int (4))
      ((FStar_String.strlen t) - (Prims.of_int (4)))
  else ""
let is_block_kw (cs : FStar_Char.char Prims.list) : Prims.bool=
  (((chars_prefix_match [82; 85; 76; 69] cs) ||
      (chars_prefix_match [68; 65; 84; 65] cs))
     || (chars_prefix_match [80; 82; 69; 70; 73; 88] cs))
    || (chars_prefix_match [66; 65; 83; 69] cs)
let is_prefix_seg (s : Prims.string) : Prims.bool=
  let t = lstrip s in (starts_with t "PREFIX") || (starts_with t "BASE")
let compute_header (first : Prims.string) (segs : Prims.string Prims.list) :
  Prims.string=
  FStar_String.concat "\n" (first ::
    (FStar_List_Tot_Base.filter is_prefix_seg segs))
let rec scan_blocks (cs : FStar_Char.char Prims.list) (depth : Prims.int)
  (prev_ws : Prims.bool) (curr : FStar_Char.char Prims.list)
  (blocks : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then
    FStar_List_Tot_Base.rev
      ((FStar_String.string_of_list (FStar_List_Tot_Base.rev curr)) ::
      blocks)
  else
    (match cs with
     | [] ->
         FStar_List_Tot_Base.rev
           ((FStar_String.string_of_list (FStar_List_Tot_Base.rev curr)) ::
           blocks)
     | c::rest ->
         if ((depth = Prims.int_zero) && prev_ws) && (is_block_kw cs)
         then
           scan_blocks rest depth false [c]
             ((FStar_String.string_of_list (FStar_List_Tot_Base.rev curr)) ::
             blocks) (fuel - Prims.int_one)
         else
           (let depth' =
              if c = 123
              then depth + Prims.int_one
              else if c = 125 then depth - Prims.int_one else depth in
            let ws = (((c = 32) || (c = 10)) || (c = 9)) || (c = 13) in
            scan_blocks rest depth' ws (c :: curr) blocks
              (fuel - Prims.int_one)))
let rec rule_texts (header : Prims.string) (ls : Prims.string Prims.list) :
  Prims.string Prims.list=
  match ls with
  | [] -> []
  | l::rest ->
      (match line_kind l with
       | FStar_Pervasives_Native.Some true ->
           let body = replace_all (line_body l) "NOT {" "FILTER NOT EXISTS {" in
           (FStar_String.concat "" [header; "\nCONSTRUCT "; body]) ::
             (rule_texts header rest)
       | FStar_Pervasives_Native.Some false ->
           (FStar_String.concat ""
              [header; "\nCONSTRUCT "; line_body l; " WHERE {}"])
           :: (rule_texts header rest)
       | FStar_Pervasives_Native.None -> rule_texts header rest)
let translate_srl (srl : Prims.string) : Prims.string Prims.list=
  match scan_blocks (FStar_String.list_of_string srl) Prims.int_zero true []
          [] ((FStar_String.strlen srl) + (Prims.of_int (2)))
  with
  | [] -> []
  | first::blocks -> rule_texts (compute_header first blocks) blocks
let str_has_char (c : FStar_Char.char) (s : Prims.string) : Prims.bool=
  FStar_List_Tot_Base.mem c (FStar_String.list_of_string s)
let block_valid (header : Prims.string) (block : Prims.string) : Prims.bool=
  match line_kind block with
  | FStar_Pervasives_Native.Some true ->
      let txt =
        FStar_String.concat ""
          [header;
          "\nCONSTRUCT ";
          replace_all (line_body block) "NOT {" "FILTER NOT EXISTS {"] in
      (match SPARQL11_Parser.parse_sparql_12_with_base
               FStar_Pervasives_Native.None txt
       with
       | SPARQL11_Parser.ParseOk (uu___, uu___1) -> true
       | uu___ -> false)
  | FStar_Pervasives_Native.Some false ->
      let body = line_body block in
      if (str_has_char 63 body) || (str_has_char 36 body)
      then false
      else
        (match SPARQL11_Parser.parse_sparql_12_with_base
                 FStar_Pervasives_Native.None
                 (FStar_String.concat ""
                    [header; "\nCONSTRUCT "; body; " WHERE {}"])
         with
         | SPARQL11_Parser.ParseOk (uu___1, uu___2) -> true
         | uu___1 -> false)
  | FStar_Pervasives_Native.None -> true
let rec all_blocks_valid (header : Prims.string)
  (bs : Prims.string Prims.list) : Prims.bool=
  match bs with
  | [] -> true
  | b::rest -> (block_valid header b) && (all_blocks_valid header rest)
let srl_valid_syntax (srl : Prims.string) : Prims.bool=
  match scan_blocks (FStar_String.list_of_string srl) Prims.int_zero true []
          [] ((FStar_String.strlen srl) + (Prims.of_int (2)))
  with
  | [] -> true
  | first::blocks -> all_blocks_valid (compute_header first blocks) blocks
let is_var_name_char (c : FStar_Char.char) : Prims.bool=
  Prims.op_Negation
    (((((((((((((((((((c = 32) || (c = 10)) || (c = 9)) || (c = 13)) ||
                     (c = 46))
                    || (c = 123))
                   || (c = 125))
                  || (c = 40))
                 || (c = 41))
                || (c = 59))
               || (c = 44))
              || (c = 63))
             || (c = 36))
            || (c = 60))
           || (c = 62))
          || (c = 34))
         || (c = 39))
        || (c = 91))
       || (c = 93))
let rec take_while (p : FStar_Char.char -> Prims.bool)
  (cs : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match cs with
  | c::r -> if p c then c :: (take_while p r) else []
  | [] -> []
let rec drop_while (p : FStar_Char.char -> Prims.bool)
  (cs : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match cs with | c::r -> if p c then drop_while p r else cs | [] -> []
let rec collect_vars (cs : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | c::rest ->
         if (c = 63) || (c = 36)
         then
           (match take_while is_var_name_char rest with
            | [] -> collect_vars rest (fuel - Prims.int_one)
            | nm -> (FStar_String.string_of_list nm) ::
                (collect_vars (drop_while is_var_name_char rest)
                   (fuel - Prims.int_one)))
         else collect_vars rest (fuel - Prims.int_one))
let vars_in (s : Prims.string) : Prims.string Prims.list=
  collect_vars (FStar_String.list_of_string s)
    ((FStar_String.strlen s) + Prims.int_one)
let rec split_at_needle (cs : FStar_Char.char Prims.list)
  (needle : FStar_Char.char Prims.list) (acc : FStar_Char.char Prims.list)
  (fuel : Prims.nat) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match cs with
     | [] -> FStar_Pervasives_Native.None
     | c::rest ->
         if chars_prefix_match needle cs
         then
           FStar_Pervasives_Native.Some
             ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
               (FStar_String.string_of_list
                  (chars_drop (FStar_List_Tot_Base.length needle) cs)))
         else split_at_needle rest needle (c :: acc) (fuel - Prims.int_one))
let rec all_mem (xs : Prims.string Prims.list) (ys : Prims.string Prims.list)
  : Prims.bool=
  match xs with
  | [] -> true
  | x::r -> (FStar_List_Tot_Base.mem x ys) && (all_mem r ys)
let rec capture_parens (cs : FStar_Char.char Prims.list) (depth : Prims.int)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  (Prims.string * FStar_Char.char Prims.list)=
  if fuel = Prims.int_zero
  then ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), cs)
  else
    (match cs with
     | [] ->
         ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), [])
     | 41::rest ->
         if depth = Prims.int_zero
         then
           ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
             rest)
         else
           capture_parens rest (depth - Prims.int_one) (41 :: acc)
             (fuel - Prims.int_one)
     | 40::rest ->
         capture_parens rest (depth + Prims.int_one) (40 :: acc)
           (fuel - Prims.int_one)
     | c::rest -> capture_parens rest depth (c :: acc) (fuel - Prims.int_one))
let filter_safe (body : Prims.string) : Prims.bool=
  match split_at_needle (FStar_String.list_of_string body)
          [70; 73; 76; 84; 69; 82] []
          ((FStar_String.strlen body) + Prims.int_one)
  with
  | FStar_Pervasives_Native.Some (before, after) ->
      (match drop_ws (FStar_String.list_of_string after) with
       | 40::inner ->
           let uu___ =
             capture_parens inner Prims.int_zero []
               ((FStar_String.strlen body) + Prims.int_one) in
           (match uu___ with
            | (expr, uu___1) -> all_mem (vars_in expr) (vars_in before))
       | uu___ -> true)
  | FStar_Pervasives_Native.None -> true
let block_well_formed (header : Prims.string) (block : Prims.string) :
  Prims.bool=
  match line_kind block with
  | FStar_Pervasives_Native.Some true ->
      let hv_ok =
        match split_at_needle (FStar_String.list_of_string (line_body block))
                [87; 72; 69; 82; 69] []
                ((FStar_String.strlen block) + Prims.int_one)
        with
        | FStar_Pervasives_Native.Some (head, body) ->
            (all_mem (vars_in head) (vars_in body)) && (filter_safe body)
        | FStar_Pervasives_Native.None -> true in
      let parse_ok =
        match SPARQL11_Parser.parse_sparql_12_with_base
                FStar_Pervasives_Native.None
                (FStar_String.concat ""
                   [header;
                   "\nCONSTRUCT ";
                   replace_all (line_body block) "NOT {"
                     "FILTER NOT EXISTS {"])
        with
        | SPARQL11_Parser.ParseOk (uu___, uu___1) -> true
        | uu___ -> false in
      hv_ok && parse_ok
  | uu___ -> true
let rec all_blocks_well_formed (header : Prims.string)
  (bs : Prims.string Prims.list) : Prims.bool=
  match bs with
  | [] -> true
  | b::rest ->
      (block_well_formed header b) && (all_blocks_well_formed header rest)
let srl_well_formed (srl : Prims.string) : Prims.bool=
  match scan_blocks (FStar_String.list_of_string srl) Prims.int_zero true []
          [] ((FStar_String.strlen srl) + (Prims.of_int (2)))
  with
  | [] -> true
  | first::blocks ->
      all_blocks_well_formed (compute_header first blocks) blocks
let str_contains (s : Prims.string) (needle : Prims.string) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some
    (split_at_needle (FStar_String.list_of_string s)
       (FStar_String.list_of_string needle) []
       ((FStar_String.strlen s) + Prims.int_one))
let rec collect_pnames (cs : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | c::rest ->
         if is_var_name_char c
         then
           let run = take_while is_var_name_char cs in
           let s = FStar_String.string_of_list run in
           FStar_List_Tot_Base.op_At (if str_contains s ":" then [s] else [])
             (collect_pnames (drop_while is_var_name_char cs)
                (fuel - Prims.int_one))
         else collect_pnames rest (fuel - Prims.int_one))
let rule_head (block : Prims.string) : Prims.string=
  match split_at_needle (FStar_String.list_of_string (line_body block))
          [87; 72; 69; 82; 69] []
          ((FStar_String.strlen block) + Prims.int_one)
  with
  | FStar_Pervasives_Native.Some (h, uu___) -> h
  | FStar_Pervasives_Native.None -> line_body block
let rule_body (block : Prims.string) : Prims.string=
  match split_at_needle (FStar_String.list_of_string (line_body block))
          [87; 72; 69; 82; 69] []
          ((FStar_String.strlen block) + Prims.int_one)
  with
  | FStar_Pervasives_Native.Some (uu___, b) -> b
  | FStar_Pervasives_Native.None -> ""
let rec any_mem (xs : Prims.string Prims.list) (ys : Prims.string Prims.list)
  : Prims.bool=
  match xs with
  | [] -> false
  | x::r -> (FStar_List_Tot_Base.mem x ys) || (any_mem r ys)
let block_new_term_recursive (block : Prims.string)
  (all_body_pnames : Prims.string Prims.list) : Prims.bool=
  match line_kind block with
  | FStar_Pervasives_Native.Some true ->
      let h = rule_head block in
      if (str_contains h "[]") || (str_contains h "_:")
      then
        any_mem
          (collect_pnames (FStar_String.list_of_string h)
             ((FStar_String.strlen h) + Prims.int_one)) all_body_pnames
      else false
  | uu___ -> false
let rec any_block_nt_recursive (bs : Prims.string Prims.list)
  (all_body_pnames : Prims.string Prims.list) : Prims.bool=
  match bs with
  | [] -> false
  | b::rest ->
      (block_new_term_recursive b all_body_pnames) ||
        (any_block_nt_recursive rest all_body_pnames)
let rec capture_braces (cs : FStar_Char.char Prims.list) (depth : Prims.int)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  (Prims.string * FStar_Char.char Prims.list)=
  if fuel = Prims.int_zero
  then ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), cs)
  else
    (match cs with
     | [] ->
         ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), [])
     | 125::rest ->
         if depth = Prims.int_zero
         then
           ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
             rest)
         else
           capture_braces rest (depth - Prims.int_one) (125 :: acc)
             (fuel - Prims.int_one)
     | 123::rest ->
         capture_braces rest (depth + Prims.int_one) (123 :: acc)
           (fuel - Prims.int_one)
     | c::rest -> capture_braces rest depth (c :: acc) (fuel - Prims.int_one))
let rec extract_not_contents (cs : FStar_Char.char Prims.list)
  (fuel : Prims.nat) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | uu___1::rest ->
         if chars_prefix_match [78; 79; 84] cs
         then
           (match drop_ws (chars_drop (Prims.of_int (3)) cs) with
            | 123::inner ->
                let uu___2 = capture_braces inner Prims.int_zero [] fuel in
                (match uu___2 with
                 | (content, after) -> content ::
                     (extract_not_contents after (fuel - Prims.int_one)))
            | uu___2 -> extract_not_contents rest (fuel - Prims.int_one))
         else extract_not_contents rest (fuel - Prims.int_one))
let rec collect_literals (cs : FStar_Char.char Prims.list) (fuel : Prims.nat)
  : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | 34::rest ->
         let run = take_while (fun c -> Prims.op_Negation (c = 34)) rest in
         (FStar_String.concat ""
            ["\""; FStar_String.string_of_list run; "\""])
           ::
           (collect_literals
              (chars_drop Prims.int_one
                 (drop_while (fun c -> Prims.op_Negation (c = 34)) rest))
              (fuel - Prims.int_one))
     | uu___1::rest -> collect_literals rest (fuel - Prims.int_one))
let sig_tokens (s : Prims.string) : Prims.string Prims.list=
  FStar_List_Tot_Base.op_At
    (collect_pnames (FStar_String.list_of_string s)
       ((FStar_String.strlen s) + Prims.int_one))
    (collect_literals (FStar_String.list_of_string s)
       ((FStar_String.strlen s) + Prims.int_one))
let rec all_contained (toks : Prims.string Prims.list) (hay : Prims.string) :
  Prims.bool=
  match toks with
  | [] -> true
  | t::r -> (str_contains hay t) && (all_contained r hay)
let neg_matches_head (not_content : Prims.string)
  (heads : Prims.string Prims.list) : Prims.bool=
  let toks = sig_tokens not_content in
  (Prims.uu___is_Cons toks) &&
    (FStar_List_Tot_Base.existsb (fun h -> all_contained toks h) heads)
let srl_stratifiable (srl : Prims.string) : Prims.bool=
  match scan_blocks (FStar_String.list_of_string srl) Prims.int_zero true []
          [] ((FStar_String.strlen srl) + (Prims.of_int (2)))
  with
  | [] -> true
  | uu___::blocks ->
      let all_body_pnames =
        FStar_List_Tot_Base.concatMap
          (fun b ->
             let bd = rule_body b in
             collect_pnames (FStar_String.list_of_string bd)
               ((FStar_String.strlen bd) + Prims.int_one)) blocks in
      let heads =
        FStar_List_Tot_Base.concatMap
          (fun b ->
             match line_kind b with
             | FStar_Pervasives_Native.Some true -> [rule_head b]
             | uu___1 -> []) blocks in
      let not_blocks =
        FStar_List_Tot_Base.concatMap
          (fun b ->
             match line_kind b with
             | FStar_Pervasives_Native.Some true ->
                 extract_not_contents
                   (FStar_String.list_of_string (rule_body b))
                   ((FStar_String.strlen b) + Prims.int_one)
             | uu___1 -> []) blocks in
      Prims.op_Negation
        ((any_block_nt_recursive blocks all_body_pnames) ||
           (FStar_List_Tot_Base.existsb (fun nb -> neg_matches_head nb heads)
              not_blocks))
let parse_constructs (srl : Prims.string) :
  SPARQL11_Algebra.query Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match SPARQL11_Parser.parse_sparql_12_with_base
               FStar_Pervasives_Native.None t
       with
       | SPARQL11_Parser.ParseOk (q, uu___) -> [q]
       | uu___ -> []) (translate_srl srl)
let rules_step (g : RDF_Graph.rdf_graph)
  (qs : SPARQL11_Algebra.query Prims.list) : RDF_Graph.rdf_graph=
  let inferred =
    FStar_List_Tot_Base.concatMap
      (fun q ->
         SPARQL11_Algebra.eval_construct_query q g
           { RDF_Graph.ds_default = g; RDF_Graph.ds_named = [] }) qs in
  SPARQL11_Algebra.dedup_triples (FStar_List_Tot_Base.op_At g inferred)
let rec rules_fixpoint (g : RDF_Graph.rdf_graph)
  (qs : SPARQL11_Algebra.query Prims.list) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  if fuel = Prims.int_zero
  then g
  else
    (let g' = rules_step g qs in
     if (FStar_List_Tot_Base.length g') = (FStar_List_Tot_Base.length g)
     then g'
     else rules_fixpoint g' qs (fuel - Prims.int_one))
let run_rules (data : RDF_Graph.rdf_graph) (srl : Prims.string) :
  RDF_Graph.rdf_graph=
  let qs = parse_constructs srl in
  let closure =
    rules_fixpoint (SPARQL11_Algebra.dedup_triples data) qs
      ((FStar_List_Tot_Base.length data) + (Prims.of_int (100))) in
  FStar_List_Tot_Base.filter
    (fun t ->
       Prims.op_Negation
         (FStar_List_Tot_Base.existsb (fun d -> RDF_Triple.triple_eq t d)
            data)) closure
