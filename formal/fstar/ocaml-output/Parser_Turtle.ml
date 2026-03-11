open Prims
type turtle_state =
  {
  prefixes: (Prims.string * Prims.string) Prims.list ;
  base_iri: Prims.string ;
  bnode_counter: Prims.nat }
let __proj__Mkturtle_state__item__prefixes (projectee : turtle_state) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { prefixes; base_iri; bnode_counter;_} -> prefixes
let __proj__Mkturtle_state__item__base_iri (projectee : turtle_state) :
  Prims.string=
  match projectee with | { prefixes; base_iri; bnode_counter;_} -> base_iri
let __proj__Mkturtle_state__item__bnode_counter (projectee : turtle_state) :
  Prims.nat=
  match projectee with
  | { prefixes; base_iri; bnode_counter;_} -> bnode_counter
let empty_turtle_state : turtle_state=
  { prefixes = []; base_iri = ""; bnode_counter = Prims.int_zero }
let fresh_bnode (st : turtle_state) :
  (RDF_Graph_Executable.bnode_id * turtle_state)=
  let id =
    FStar_String.concat "" ["_anon"; Prims.string_of_int st.bnode_counter] in
  (id,
    {
      prefixes = (st.prefixes);
      base_iri = (st.base_iri);
      bnode_counter = (st.bnode_counter + Prims.int_one)
    })
let rec lookup_prefix (pfx : Prims.string)
  (ps : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match ps with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = pfx
      then FStar_Pervasives_Native.Some v
      else lookup_prefix pfx rest
let resolve_prefixed_name (st : turtle_state) (prefix : Prims.string)
  (local : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  match lookup_prefix prefix st.prefixes with
  | FStar_Pervasives_Native.Some base ->
      FStar_Pervasives_Native.Some (FStar_String.concat "" [base; local])
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec find_last_slash (s : Prims.string) (pos : Prims.nat) : Prims.nat=
  if pos = Prims.int_zero
  then Prims.int_zero
  else
    (let idx = pos - Prims.int_one in
     if
       (idx < (FStar_String.strlen s)) &&
         ((FStar_Char.int_of_char (FStar_String.index s idx)) =
            (Prims.of_int (0x2F)))
     then pos
     else find_last_slash s idx)
let remove_last_segment (base : Prims.string) : Prims.string=
  let len = FStar_String.strlen base in
  if len = Prims.int_zero
  then ""
  else
    (let cut_pos = find_last_slash base len in
     if cut_pos = Prims.int_zero
     then base
     else FStar_String.sub base Prims.int_zero cut_pos)
let resolve_iri (st : turtle_state) (rel : Prims.string) : Prims.string=
  if (FStar_String.strlen rel) = Prims.int_zero
  then st.base_iri
  else
    (let len = FStar_String.strlen rel in
     if RDF_Graph_Executable.string_contains_colon rel
     then rel
     else
       if
         (FStar_Char.int_of_char (FStar_String.index rel Prims.int_zero)) =
           (Prims.of_int (0x2F))
       then FStar_String.concat "" [st.base_iri; rel]
       else
         if
           (FStar_Char.int_of_char (FStar_String.index rel Prims.int_zero)) =
             (Prims.of_int (0x23))
         then FStar_String.concat "" [st.base_iri; rel]
         else
           (let base_dir = remove_last_segment st.base_iri in
            FStar_String.concat "" [base_dir; rel]))
let is_turtle_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let rec skip_to_eol (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then pos
     else
       (let c = FStar_String.index input pos in
        let code = FStar_Char.int_of_char c in
        if (code = (Prims.of_int (0x0A))) || (code = (Prims.of_int (0x0D)))
        then pos
        else skip_to_eol input (pos + Prims.int_one) (fuel - Prims.int_one)))
let rec skip_ws_and_comments (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then pos
     else
       (let c = FStar_String.index input pos in
        let code = FStar_Char.int_of_char c in
        if is_turtle_ws c
        then
          skip_ws_and_comments input (pos + Prims.int_one)
            (fuel - Prims.int_one)
        else
          if code = (Prims.of_int (0x23))
          then
            (let pos' = skip_to_eol input (pos + Prims.int_one) (len - pos) in
             skip_ws_and_comments input pos' (fuel - Prims.int_one))
          else pos))
let turtle_ws (input : Prims.string) (pos : Prims.nat) :
  unit Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  let fuel = (len - pos) + Prims.int_one in
  if fuel >= Prims.int_zero
  then Parser_Combinators.ParseOk ((), (skip_ws_and_comments input pos fuel))
  else Parser_Combinators.ParseOk ((), pos)
let is_pn_chars_base (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((((((((code >= (Prims.of_int (0x41))) &&
                (code <= (Prims.of_int (0x5A))))
               ||
               ((code >= (Prims.of_int (0x61))) &&
                  (code <= (Prims.of_int (0x7A)))))
              ||
              ((code >= (Prims.of_int (0x00C0))) &&
                 (code <= (Prims.of_int (0x00D6)))))
             ||
             ((code >= (Prims.of_int (0x00D8))) &&
                (code <= (Prims.of_int (0x00F6)))))
            ||
            ((code >= (Prims.of_int (0x00F8))) &&
               (code <= (Prims.of_int (0x02FF)))))
           ||
           ((code >= (Prims.of_int (0x0370))) &&
              (code <= (Prims.of_int (0x037D)))))
          ||
          ((code >= (Prims.of_int (0x037F))) &&
             (code <= (Prims.of_int (0x1FFF)))))
         ||
         ((code >= (Prims.of_int (0x200C))) &&
            (code <= (Prims.of_int (0x200D)))))
        ||
        ((code >= (Prims.of_int (0x2070))) &&
           (code <= (Prims.of_int (0x218F)))))
       ||
       ((code >= (Prims.of_int (0x2C00))) &&
          (code <= (Prims.of_int (0x2FEF)))))
      ||
      ((code >= (Prims.of_int (0x3001))) && (code <= (Prims.of_int (0xD7FF)))))
     ||
     ((code >= (Prims.of_int (0xF900))) && (code <= (Prims.of_int (0xFDCF)))))
    ||
    ((code >= (Prims.of_int (0xFDF0))) && (code <= (Prims.of_int (0xFFFD))))
let is_pn_chars_u (c : FStar_Char.char) : Prims.bool=
  (is_pn_chars_base c) ||
    ((FStar_Char.int_of_char c) = (Prims.of_int (0x5F)))
let is_pn_chars (c : FStar_Char.char) : Prims.bool=
  (is_pn_chars_u c) ||
    (let code = FStar_Char.int_of_char c in
     ((((code = (Prims.of_int (0x2D))) ||
          ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
         || (code = (Prims.of_int (0xB7))))
        ||
        ((code >= (Prims.of_int (0x0300))) &&
           (code <= (Prims.of_int (0x036F)))))
       ||
       ((code >= (Prims.of_int (0x203F))) &&
          (code <= (Prims.of_int (0x2040)))))
let rec parse_pname_ns_acc (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("prefix name too long", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("expected ':' in prefixed name", pos)
     else
       (let c = FStar_String.index input pos in
        let code = FStar_Char.int_of_char c in
        if code = (Prims.of_int (0x3A))
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if (is_pn_chars c) || (code = (Prims.of_int (0x2E)))
          then
            parse_pname_ns_acc input (pos + Prims.int_one) (c :: acc)
              (fuel - Prims.int_one)
          else
            Parser_Combinators.ParseFail
              ("invalid character in prefix name", pos)))
let parse_pname_ns (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected prefix name", pos)
  else
    (let c = FStar_String.index input pos in
     let code = FStar_Char.int_of_char c in
     if code = (Prims.of_int (0x3A))
     then Parser_Combinators.ParseOk ("", (pos + Prims.int_one))
     else
       if is_pn_chars_base c
       then
         (let fuel = len - pos in
          parse_pname_ns_acc input (pos + Prims.int_one) [c] fuel)
       else Parser_Combinators.ParseFail ("expected prefix name", pos))
let is_pn_local_char (c : FStar_Char.char) : Prims.bool=
  (is_pn_chars c) ||
    (let code = FStar_Char.int_of_char c in
     (((code = (Prims.of_int (0x3A))) || (code = (Prims.of_int (0x2E)))) ||
        (code = (Prims.of_int (0x25))))
       || (code = (Prims.of_int (0x5C))))
let is_pn_local_start (c : FStar_Char.char) : Prims.bool=
  (is_pn_chars_u c) ||
    (let code = FStar_Char.int_of_char c in
     (((code = (Prims.of_int (0x3A))) ||
         ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
        || (code = (Prims.of_int (0x25))))
       || (code = (Prims.of_int (0x5C))))
let parse_pn_local (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseOk ("", pos)
  else
    (let c = FStar_String.index input pos in
     if is_pn_local_start c
     then
       match Parser_Combinators.ptake_while is_pn_local_char input pos with
       | Parser_Combinators.ParseOk (s, pos') ->
           let slen = FStar_String.strlen s in
           (if slen > Prims.int_one
            then
              let last = FStar_String.index s (slen - Prims.int_one) in
              (if
                 ((FStar_Char.int_of_char last) = (Prims.of_int (0x2E))) &&
                   (pos' > Prims.int_zero)
               then
                 Parser_Combinators.ParseOk
                   ((FStar_String.sub s Prims.int_zero (slen - Prims.int_one)),
                     (pos' - Prims.int_one))
               else Parser_Combinators.ParseOk (s, pos'))
            else
              if slen = Prims.int_one
              then
                (let last = FStar_String.index s Prims.int_zero in
                 if
                   ((FStar_Char.int_of_char last) = (Prims.of_int (0x2E))) &&
                     (pos' > Prims.int_zero)
                 then Parser_Combinators.ParseOk ("", (pos' - Prims.int_one))
                 else Parser_Combinators.ParseOk (s, pos'))
              else Parser_Combinators.ParseOk ("", pos))
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
     else Parser_Combinators.ParseOk ("", pos))
let parse_prefixed_name (input : Prims.string) (pos : Prims.nat) :
  (Prims.string * Prims.string) Parser_Combinators.parse_result=
  match parse_pname_ns input pos with
  | Parser_Combinators.ParseOk (ns, pos') ->
      (match parse_pn_local input pos' with
       | Parser_Combinators.ParseOk (local, pos'') ->
           Parser_Combinators.ParseOk ((ns, local), pos'')
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_turtle_iri (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) :
  RDF_Graph_Executable.iri Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected IRI", pos)
  else
    (let c = FStar_String.index input pos in
     let code = FStar_Char.int_of_char c in
     if code = (Prims.of_int (0x3C))
     then
       match Parser_NTriples.parse_iri_raw input pos with
       | Parser_Combinators.ParseOk (i, pos') ->
           let resolved = resolve_iri st i in
           (if RDF_Graph_Executable.is_iri resolved
            then Parser_Combinators.ParseOk (resolved, pos')
            else Parser_Combinators.ParseFail ("resolved IRI invalid", pos))
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
     else
       (match parse_prefixed_name input pos with
        | Parser_Combinators.ParseOk ((prefix, local), pos') ->
            (match resolve_prefixed_name st prefix local with
             | FStar_Pervasives_Native.Some resolved ->
                 Parser_Combinators.ParseOk (resolved, pos')
             | FStar_Pervasives_Native.None ->
                 Parser_Combinators.ParseFail
                   ((FStar_String.concat "" ["undefined prefix: "; prefix]),
                     pos))
        | Parser_Combinators.ParseFail (msg, fpos) ->
            Parser_Combinators.ParseFail (msg, fpos)))
let parse_at_prefix (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) :
  (Prims.string * Prims.string) Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "@prefix" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      (match turtle_ws input pos1 with
       | Parser_Combinators.ParseOk ((), pos2) ->
           (match parse_pname_ns input pos2 with
            | Parser_Combinators.ParseOk (ns, pos3) ->
                (match turtle_ws input pos3 with
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     (match Parser_NTriples.parse_iri_raw input pos4 with
                      | Parser_Combinators.ParseOk (raw_iri, pos5) ->
                          let iri_val = resolve_iri st raw_iri in
                          (match turtle_ws input pos5 with
                           | Parser_Combinators.ParseOk ((), pos6) ->
                               let len = FStar_String.strlen input in
                               if pos6 < len
                               then
                                 let dot = FStar_String.index input pos6 in
                                 (if
                                    (FStar_Char.int_of_char dot) =
                                      (Prims.of_int (0x2E))
                                  then
                                    Parser_Combinators.ParseOk
                                      ((ns, iri_val), (pos6 + Prims.int_one))
                                  else
                                    Parser_Combinators.ParseFail
                                      ("expected '.' after @prefix directive",
                                        pos6))
                               else
                                 Parser_Combinators.ParseFail
                                   ("expected '.' after @prefix directive",
                                     pos6))
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos)))
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_sparql_prefix (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) :
  (Prims.string * Prims.string) Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "PREFIX" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      (match turtle_ws input pos1 with
       | Parser_Combinators.ParseOk ((), pos2) ->
           (match parse_pname_ns input pos2 with
            | Parser_Combinators.ParseOk (ns, pos3) ->
                (match turtle_ws input pos3 with
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     (match Parser_NTriples.parse_iri_raw input pos4 with
                      | Parser_Combinators.ParseOk (raw_iri, pos5) ->
                          let iri_val = resolve_iri st raw_iri in
                          Parser_Combinators.ParseOk ((ns, iri_val), pos5)
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos)))
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_at_base (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) : Prims.string Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "@base" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      (match turtle_ws input pos1 with
       | Parser_Combinators.ParseOk ((), pos2) ->
           (match Parser_NTriples.parse_iri_raw input pos2 with
            | Parser_Combinators.ParseOk (raw_iri, pos3) ->
                let iri_val = resolve_iri st raw_iri in
                (match turtle_ws input pos3 with
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     let len = FStar_String.strlen input in
                     if pos4 < len
                     then
                       let dot = FStar_String.index input pos4 in
                       (if
                          (FStar_Char.int_of_char dot) =
                            (Prims.of_int (0x2E))
                        then
                          Parser_Combinators.ParseOk
                            (iri_val, (pos4 + Prims.int_one))
                        else
                          Parser_Combinators.ParseFail
                            ("expected '.' after @base directive", pos4))
                     else
                       Parser_Combinators.ParseFail
                         ("expected '.' after @base directive", pos4))
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_sparql_base (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) : Prims.string Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "BASE" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      (match turtle_ws input pos1 with
       | Parser_Combinators.ParseOk ((), pos2) ->
           (match Parser_NTriples.parse_iri_raw input pos2 with
            | Parser_Combinators.ParseOk (raw_iri, pos3) ->
                let iri_val = resolve_iri st raw_iri in
                Parser_Combinators.ParseOk (iri_val, pos3)
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_prefix_directive (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) :
  (Prims.string * Prims.string) Parser_Combinators.parse_result=
  match parse_at_prefix st input pos with
  | Parser_Combinators.ParseOk (v, p) -> Parser_Combinators.ParseOk (v, p)
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      parse_sparql_prefix st input pos
let parse_base_directive (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) : Prims.string Parser_Combinators.parse_result=
  match parse_at_base st input pos with
  | Parser_Combinators.ParseOk (v, p) -> Parser_Combinators.ParseOk (v, p)
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      parse_sparql_base st input pos
let is_digit_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let parse_numeric_literal (input : Prims.string) (pos : Prims.nat) :
  (Prims.string * RDF_Graph_Executable.wf_iri)
    Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected numeric literal", pos)
  else
    (let c0 = FStar_String.index input pos in
     let code0 = FStar_Char.int_of_char c0 in
     let sign_str =
       if code0 = (Prims.of_int (0x2B))
       then "+"
       else if code0 = (Prims.of_int (0x2D)) then "-" else "" in
     let dpos =
       if code0 = (Prims.of_int (0x2B))
       then pos + Prims.int_one
       else
         if code0 = (Prims.of_int (0x2D)) then pos + Prims.int_one else pos in
     let rec collect_num p acc has_dot has_e fuel =
       if fuel = Prims.int_zero
       then Parser_Combinators.ParseOk ((acc, has_dot, has_e), p)
       else
         if p >= len
         then Parser_Combinators.ParseOk ((acc, has_dot, has_e), p)
         else
           (let ch = FStar_String.index input p in
            let cd = FStar_Char.int_of_char ch in
            if is_digit_char ch
            then
              collect_num (p + Prims.int_one) (ch :: acc) has_dot has_e
                (fuel - Prims.int_one)
            else
              if
                ((cd = (Prims.of_int (0x2E))) && (Prims.op_Negation has_dot))
                  && (Prims.op_Negation has_e)
              then
                (if (p + Prims.int_one) < len
                 then
                   let next = FStar_String.index input (p + Prims.int_one) in
                   (if is_digit_char next
                    then
                      collect_num (p + Prims.int_one) (ch :: acc) true has_e
                        (fuel - Prims.int_one)
                    else
                      Parser_Combinators.ParseOk ((acc, has_dot, has_e), p))
                 else Parser_Combinators.ParseOk ((acc, has_dot, has_e), p))
              else
                if
                  ((cd = (Prims.of_int (0x65))) ||
                     (cd = (Prims.of_int (0x45))))
                    && (Prims.op_Negation has_e)
                then
                  (if (p + Prims.int_one) < len
                   then
                     let enext = FStar_String.index input (p + Prims.int_one) in
                     let ecode = FStar_Char.int_of_char enext in
                     (if
                        (ecode = (Prims.of_int (0x2B))) ||
                          (ecode = (Prims.of_int (0x2D)))
                      then
                        collect_num (p + (Prims.of_int (2))) (enext :: ch ::
                          acc) has_dot true (fuel - Prims.int_one)
                      else
                        if is_digit_char enext
                        then
                          collect_num (p + Prims.int_one) (ch :: acc) has_dot
                            true (fuel - Prims.int_one)
                        else
                          Parser_Combinators.ParseOk
                            ((acc, has_dot, has_e), p))
                   else Parser_Combinators.ParseOk ((acc, has_dot, has_e), p))
                else Parser_Combinators.ParseOk ((acc, has_dot, has_e), p)) in
     if
       (dpos < len) &&
         ((FStar_Char.int_of_char (FStar_String.index input dpos)) =
            (Prims.of_int (0x2E)))
     then
       (if
          ((dpos + Prims.int_one) < len) &&
            (is_digit_char (FStar_String.index input (dpos + Prims.int_one)))
        then
          let fuel = len - dpos in
          match collect_num (dpos + Prims.int_one)
                  [FStar_String.index input dpos] false true fuel
          with
          | Parser_Combinators.ParseOk ((acc, uu___1, has_e), pos') ->
              let num_str =
                FStar_String.string_of_list (FStar_List_Tot_Base.rev acc) in
              let lexical = FStar_String.concat "" [sign_str; num_str] in
              let dt =
                if has_e
                then RDF_Graph_Executable.xsd_double
                else RDF_Graph_Executable.xsd_decimal in
              Parser_Combinators.ParseOk ((lexical, dt), pos')
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
        else Parser_Combinators.ParseFail ("expected digit after '.'", dpos))
     else
       if dpos <= len
       then
         (let fuel = len - dpos in
          match collect_num dpos [] false false fuel with
          | Parser_Combinators.ParseOk ((acc, has_dot, has_e), pos') ->
              if (FStar_List_Tot_Base.length acc) = Prims.int_zero
              then
                Parser_Combinators.ParseFail
                  ("expected numeric literal", pos)
              else
                (let num_str =
                   FStar_String.string_of_list (FStar_List_Tot_Base.rev acc) in
                 let lexical = FStar_String.concat "" [sign_str; num_str] in
                 let dt =
                   if has_e
                   then RDF_Graph_Executable.xsd_double
                   else
                     if has_dot
                     then RDF_Graph_Executable.xsd_decimal
                     else RDF_Graph_Executable.xsd_integer in
                 Parser_Combinators.ParseOk ((lexical, dt), pos'))
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos))
       else Parser_Combinators.ParseFail ("expected numeric literal", pos))
let rec parse_long_string_body (qch : FStar_Char.char) (input : Prims.string)
  (pos : Prims.nat) (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("unterminated long string", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated long string", pos)
     else
       (let ch = FStar_String.index input pos in
        let code = FStar_Char.int_of_char ch in
        if ch = qch
        then
          (if (pos + (Prims.of_int (2))) < len
           then
             let c1 = FStar_String.index input (pos + Prims.int_one) in
             let c2 = FStar_String.index input (pos + (Prims.of_int (2))) in
             (if (c1 = qch) && (c2 = qch)
              then
                Parser_Combinators.ParseOk
                  ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
                    (pos + (Prims.of_int (3))))
              else
                parse_long_string_body qch input (pos + Prims.int_one) (ch ::
                  acc) (fuel - Prims.int_one))
           else
             parse_long_string_body qch input (pos + Prims.int_one) (ch ::
               acc) (fuel - Prims.int_one))
        else
          if code = (Prims.of_int (0x5C))
          then
            (if (pos + Prims.int_one) >= len
             then
               Parser_Combinators.ParseFail
                 ("backslash at end of long string", pos)
             else
               (let esc = FStar_String.index input (pos + Prims.int_one) in
                let esc_code = FStar_Char.int_of_char esc in
                if esc_code = (Prims.of_int (0x74))
                then
                  parse_long_string_body qch input (pos + (Prims.of_int (2)))
                    ((FStar_Char.char_of_int (Prims.of_int (0x09))) :: acc)
                    (fuel - Prims.int_one)
                else
                  if esc_code = (Prims.of_int (0x6E))
                  then
                    parse_long_string_body qch input
                      (pos + (Prims.of_int (2)))
                      ((FStar_Char.char_of_int (Prims.of_int (0x0A))) :: acc)
                      (fuel - Prims.int_one)
                  else
                    if esc_code = (Prims.of_int (0x72))
                    then
                      parse_long_string_body qch input
                        (pos + (Prims.of_int (2)))
                        ((FStar_Char.char_of_int (Prims.of_int (0x0D))) ::
                        acc) (fuel - Prims.int_one)
                    else
                      if esc_code = (Prims.of_int (0x5C))
                      then
                        parse_long_string_body qch input
                          (pos + (Prims.of_int (2)))
                          ((FStar_Char.char_of_int (Prims.of_int (0x5C))) ::
                          acc) (fuel - Prims.int_one)
                      else
                        if esc_code = (Prims.of_int (0x22))
                        then
                          parse_long_string_body qch input
                            (pos + (Prims.of_int (2)))
                            ((FStar_Char.char_of_int (Prims.of_int (0x22)))
                            :: acc) (fuel - Prims.int_one)
                        else
                          if esc_code = (Prims.of_int (0x27))
                          then
                            parse_long_string_body qch input
                              (pos + (Prims.of_int (2)))
                              ((FStar_Char.char_of_int (Prims.of_int (0x27)))
                              :: acc) (fuel - Prims.int_one)
                          else
                            if esc_code = (Prims.of_int (0x62))
                            then
                              parse_long_string_body qch input
                                (pos + (Prims.of_int (2)))
                                ((FStar_Char.char_of_int
                                    (Prims.of_int (0x08))) :: acc)
                                (fuel - Prims.int_one)
                            else
                              if esc_code = (Prims.of_int (0x66))
                              then
                                parse_long_string_body qch input
                                  (pos + (Prims.of_int (2)))
                                  ((FStar_Char.char_of_int
                                      (Prims.of_int (0x0C))) :: acc)
                                  (fuel - Prims.int_one)
                              else
                                if esc_code = (Prims.of_int (0x75))
                                then
                                  (if (pos + (Prims.of_int (6))) > len
                                   then
                                     Parser_Combinators.ParseFail
                                       ("incomplete \\u escape", pos)
                                   else
                                     (let h0 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (2)))) in
                                      let h1 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (3)))) in
                                      let h2 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (4)))) in
                                      let h3 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (5)))) in
                                      let cp =
                                        (((h0 * (Prims.of_int (4096))) +
                                            (h1 * (Prims.of_int (256))))
                                           + (h2 * (Prims.of_int (16))))
                                          + h3 in
                                      if
                                        Prims.op_Negation
                                          (Parser_NTriples.valid_codepoint cp)
                                      then
                                        Parser_Combinators.ParseFail
                                          ("surrogate codepoint in \\u escape",
                                            pos)
                                      else
                                        parse_long_string_body qch input
                                          (pos + (Prims.of_int (6)))
                                          ((Parser_NTriples.safe_char_of_int
                                              cp) :: acc)
                                          (fuel - Prims.int_one)))
                                else
                                  if esc_code = (Prims.of_int (0x55))
                                  then
                                    (if (pos + (Prims.of_int (10))) > len
                                     then
                                       Parser_Combinators.ParseFail
                                         ("incomplete \\U escape", pos)
                                     else
                                       (let h0 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (2)))) in
                                        let h1 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (3)))) in
                                        let h2 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (4)))) in
                                        let h3 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (5)))) in
                                        let h4 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (6)))) in
                                        let h5 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (7)))) in
                                        let h6 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (8)))) in
                                        let h7 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (9)))) in
                                        let cp =
                                          (((((((h0 *
                                                   (Prims.parse_int "268435456"))
                                                  +
                                                  (h1 *
                                                     (Prims.parse_int "16777216")))
                                                 +
                                                 (h2 *
                                                    (Prims.parse_int "1048576")))
                                                +
                                                (h3 *
                                                   (Prims.parse_int "65536")))
                                               + (h4 * (Prims.of_int (4096))))
                                              + (h5 * (Prims.of_int (256))))
                                             + (h6 * (Prims.of_int (16))))
                                            + h7 in
                                        if
                                          Prims.op_Negation
                                            (Parser_NTriples.valid_codepoint
                                               cp)
                                        then
                                          Parser_Combinators.ParseFail
                                            ("surrogate codepoint in \\U escape",
                                              pos)
                                        else
                                          parse_long_string_body qch input
                                            (pos + (Prims.of_int (10)))
                                            ((Parser_NTriples.safe_char_of_int
                                                cp) :: acc)
                                            (fuel - Prims.int_one)))
                                  else
                                    Parser_Combinators.ParseFail
                                      ((FStar_String.concat ""
                                          ["invalid escape in long string: \\";
                                          FStar_String.string_of_char esc]),
                                        pos)))
          else
            parse_long_string_body qch input (pos + Prims.int_one) (ch ::
              acc) (fuel - Prims.int_one)))
let rec parse_single_string_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("string too long", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated string literal", pos)
     else
       (let ch = FStar_String.index input pos in
        let code = FStar_Char.int_of_char ch in
        if code = (Prims.of_int (0x27))
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if code = (Prims.of_int (0x5C))
          then
            (if (pos + Prims.int_one) >= len
             then
               Parser_Combinators.ParseFail
                 ("backslash at end of string", pos)
             else
               (let esc = FStar_String.index input (pos + Prims.int_one) in
                let esc_code = FStar_Char.int_of_char esc in
                if esc_code = (Prims.of_int (0x74))
                then
                  parse_single_string_body input (pos + (Prims.of_int (2)))
                    ((FStar_Char.char_of_int (Prims.of_int (0x09))) :: acc)
                    (fuel - Prims.int_one)
                else
                  if esc_code = (Prims.of_int (0x6E))
                  then
                    parse_single_string_body input (pos + (Prims.of_int (2)))
                      ((FStar_Char.char_of_int (Prims.of_int (0x0A))) :: acc)
                      (fuel - Prims.int_one)
                  else
                    if esc_code = (Prims.of_int (0x72))
                    then
                      parse_single_string_body input
                        (pos + (Prims.of_int (2)))
                        ((FStar_Char.char_of_int (Prims.of_int (0x0D))) ::
                        acc) (fuel - Prims.int_one)
                    else
                      if esc_code = (Prims.of_int (0x5C))
                      then
                        parse_single_string_body input
                          (pos + (Prims.of_int (2)))
                          ((FStar_Char.char_of_int (Prims.of_int (0x5C))) ::
                          acc) (fuel - Prims.int_one)
                      else
                        if esc_code = (Prims.of_int (0x27))
                        then
                          parse_single_string_body input
                            (pos + (Prims.of_int (2)))
                            ((FStar_Char.char_of_int (Prims.of_int (0x27)))
                            :: acc) (fuel - Prims.int_one)
                        else
                          if esc_code = (Prims.of_int (0x22))
                          then
                            parse_single_string_body input
                              (pos + (Prims.of_int (2)))
                              ((FStar_Char.char_of_int (Prims.of_int (0x22)))
                              :: acc) (fuel - Prims.int_one)
                          else
                            if esc_code = (Prims.of_int (0x62))
                            then
                              parse_single_string_body input
                                (pos + (Prims.of_int (2)))
                                ((FStar_Char.char_of_int
                                    (Prims.of_int (0x08))) :: acc)
                                (fuel - Prims.int_one)
                            else
                              if esc_code = (Prims.of_int (0x66))
                              then
                                parse_single_string_body input
                                  (pos + (Prims.of_int (2)))
                                  ((FStar_Char.char_of_int
                                      (Prims.of_int (0x0C))) :: acc)
                                  (fuel - Prims.int_one)
                              else
                                if esc_code = (Prims.of_int (0x75))
                                then
                                  (if (pos + (Prims.of_int (6))) > len
                                   then
                                     Parser_Combinators.ParseFail
                                       ("incomplete \\u escape", pos)
                                   else
                                     (let h0 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (2)))) in
                                      let h1 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (3)))) in
                                      let h2 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (4)))) in
                                      let h3 =
                                        Parser_NTriples.hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (5)))) in
                                      let cp =
                                        (((h0 * (Prims.of_int (4096))) +
                                            (h1 * (Prims.of_int (256))))
                                           + (h2 * (Prims.of_int (16))))
                                          + h3 in
                                      if
                                        Prims.op_Negation
                                          (Parser_NTriples.valid_codepoint cp)
                                      then
                                        Parser_Combinators.ParseFail
                                          ("surrogate codepoint in \\u escape",
                                            pos)
                                      else
                                        parse_single_string_body input
                                          (pos + (Prims.of_int (6)))
                                          ((Parser_NTriples.safe_char_of_int
                                              cp) :: acc)
                                          (fuel - Prims.int_one)))
                                else
                                  if esc_code = (Prims.of_int (0x55))
                                  then
                                    (if (pos + (Prims.of_int (10))) > len
                                     then
                                       Parser_Combinators.ParseFail
                                         ("incomplete \\U escape", pos)
                                     else
                                       (let h0 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (2)))) in
                                        let h1 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (3)))) in
                                        let h2 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (4)))) in
                                        let h3 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (5)))) in
                                        let h4 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (6)))) in
                                        let h5 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (7)))) in
                                        let h6 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (8)))) in
                                        let h7 =
                                          Parser_NTriples.hex_val
                                            (FStar_String.index input
                                               (pos + (Prims.of_int (9)))) in
                                        let cp =
                                          (((((((h0 *
                                                   (Prims.parse_int "268435456"))
                                                  +
                                                  (h1 *
                                                     (Prims.parse_int "16777216")))
                                                 +
                                                 (h2 *
                                                    (Prims.parse_int "1048576")))
                                                +
                                                (h3 *
                                                   (Prims.parse_int "65536")))
                                               + (h4 * (Prims.of_int (4096))))
                                              + (h5 * (Prims.of_int (256))))
                                             + (h6 * (Prims.of_int (16))))
                                            + h7 in
                                        if
                                          Prims.op_Negation
                                            (Parser_NTriples.valid_codepoint
                                               cp)
                                        then
                                          Parser_Combinators.ParseFail
                                            ("surrogate codepoint in \\U escape",
                                              pos)
                                        else
                                          parse_single_string_body input
                                            (pos + (Prims.of_int (10)))
                                            ((Parser_NTriples.safe_char_of_int
                                                cp) :: acc)
                                            (fuel - Prims.int_one)))
                                  else
                                    Parser_Combinators.ParseFail
                                      ((FStar_String.concat ""
                                          ["invalid escape: \\";
                                          FStar_String.string_of_char esc]),
                                        pos)))
          else
            if
              (code = (Prims.of_int (0x0A))) ||
                (code = (Prims.of_int (0x0D)))
            then
              Parser_Combinators.ParseFail
                ("unescaped newline in short string literal", pos)
            else
              parse_single_string_body input (pos + Prims.int_one) (ch ::
                acc) (fuel - Prims.int_one)))
let parse_turtle_string (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected string literal", pos)
  else
    (let c0 = FStar_String.index input pos in
     let code0 = FStar_Char.int_of_char c0 in
     if code0 = (Prims.of_int (0x22))
     then
       (if (pos + (Prims.of_int (2))) < len
        then
          let c1 = FStar_String.index input (pos + Prims.int_one) in
          let c2 = FStar_String.index input (pos + (Prims.of_int (2))) in
          (if
             ((FStar_Char.int_of_char c1) = (Prims.of_int (0x22))) &&
               ((FStar_Char.int_of_char c2) = (Prims.of_int (0x22)))
           then
             let fuel = len - pos in
             parse_long_string_body
               (FStar_Char.char_of_int (Prims.of_int (0x22))) input
               (pos + (Prims.of_int (3))) [] fuel
           else Parser_NTriples.parse_string_literal input pos)
        else Parser_NTriples.parse_string_literal input pos)
     else
       if code0 = (Prims.of_int (0x27))
       then
         (if (pos + (Prims.of_int (2))) < len
          then
            let c1 = FStar_String.index input (pos + Prims.int_one) in
            let c2 = FStar_String.index input (pos + (Prims.of_int (2))) in
            (if
               ((FStar_Char.int_of_char c1) = (Prims.of_int (0x27))) &&
                 ((FStar_Char.int_of_char c2) = (Prims.of_int (0x27)))
             then
               let fuel = len - pos in
               parse_long_string_body
                 (FStar_Char.char_of_int (Prims.of_int (0x27))) input
                 (pos + (Prims.of_int (3))) [] fuel
             else
               (let fuel = len - pos in
                parse_single_string_body input (pos + Prims.int_one) [] fuel))
          else
            (let fuel = len - pos in
             parse_single_string_body input (pos + Prims.int_one) [] fuel))
       else Parser_Combinators.ParseFail ("expected string literal", pos))
let parse_turtle_literal (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) :
  RDF_Graph_Executable.literal Parser_Combinators.parse_result=
  match parse_turtle_string input pos with
  | Parser_Combinators.ParseOk (lexical, pos') ->
      let len = FStar_String.strlen input in
      if pos' >= len
      then
        Parser_Combinators.ParseOk
          ({
             RDF_Graph_Executable.lexical_form = lexical;
             RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_string;
             RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
           }, pos')
      else
        (let next = FStar_String.index input pos' in
         let next_code = FStar_Char.int_of_char next in
         if next_code = (Prims.of_int (0x40))
         then
           match Parser_NTriples.parse_lang_tag input pos' with
           | Parser_Combinators.ParseOk (lang, pos'') ->
               Parser_Combinators.ParseOk
                 ({
                    RDF_Graph_Executable.lexical_form = lexical;
                    RDF_Graph_Executable.datatype =
                      RDF_Graph_Executable.rdf_lang_string;
                    RDF_Graph_Executable.lang_tag =
                      (FStar_Pervasives_Native.Some lang)
                  }, pos'')
           | Parser_Combinators.ParseFail (msg, fpos) ->
               Parser_Combinators.ParseFail (msg, fpos)
         else
           if next_code = (Prims.of_int (0x5E))
           then
             (if (pos' + Prims.int_one) < len
              then
                let next2 = FStar_String.index input (pos' + Prims.int_one) in
                (if (FStar_Char.int_of_char next2) = (Prims.of_int (0x5E))
                 then
                   match parse_turtle_iri st input
                           (pos' + (Prims.of_int (2)))
                   with
                   | Parser_Combinators.ParseOk (dt, pos'') ->
                       (if RDF_Graph_Executable.is_iri dt
                        then
                          Parser_Combinators.ParseOk
                            ({
                               RDF_Graph_Executable.lexical_form = lexical;
                               RDF_Graph_Executable.datatype = dt;
                               RDF_Graph_Executable.lang_tag =
                                 FStar_Pervasives_Native.None
                             }, pos'')
                        else
                          Parser_Combinators.ParseFail
                            ("invalid datatype IRI", pos'))
                   | Parser_Combinators.ParseFail (msg, fpos) ->
                       Parser_Combinators.ParseFail (msg, fpos)
                 else
                   Parser_Combinators.ParseOk
                     ({
                        RDF_Graph_Executable.lexical_form = lexical;
                        RDF_Graph_Executable.datatype =
                          RDF_Graph_Executable.xsd_string;
                        RDF_Graph_Executable.lang_tag =
                          FStar_Pervasives_Native.None
                      }, pos'))
              else
                Parser_Combinators.ParseOk
                  ({
                     RDF_Graph_Executable.lexical_form = lexical;
                     RDF_Graph_Executable.datatype =
                       RDF_Graph_Executable.xsd_string;
                     RDF_Graph_Executable.lang_tag =
                       FStar_Pervasives_Native.None
                   }, pos'))
           else
             Parser_Combinators.ParseOk
               ({
                  RDF_Graph_Executable.lexical_form = lexical;
                  RDF_Graph_Executable.datatype =
                    RDF_Graph_Executable.xsd_string;
                  RDF_Graph_Executable.lang_tag =
                    FStar_Pervasives_Native.None
                }, pos'))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_boolean_literal (input : Prims.string) (pos : Prims.nat) :
  RDF_Graph_Executable.literal Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "true" input pos with
  | Parser_Combinators.ParseOk (uu___, pos') ->
      let len = FStar_String.strlen input in
      if (pos' < len) && (is_pn_chars (FStar_String.index input pos'))
      then Parser_Combinators.ParseFail ("expected boolean literal", pos)
      else
        Parser_Combinators.ParseOk
          ({
             RDF_Graph_Executable.lexical_form = "true";
             RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_boolean;
             RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
           }, pos')
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      (match Parser_Combinators.pstring "false" input pos with
       | Parser_Combinators.ParseOk (uu___2, pos') ->
           let len = FStar_String.strlen input in
           if (pos' < len) && (is_pn_chars (FStar_String.index input pos'))
           then
             Parser_Combinators.ParseFail ("expected boolean literal", pos)
           else
             Parser_Combinators.ParseOk
               ({
                  RDF_Graph_Executable.lexical_form = "false";
                  RDF_Graph_Executable.datatype =
                    RDF_Graph_Executable.xsd_boolean;
                  RDF_Graph_Executable.lang_tag =
                    FStar_Pervasives_Native.None
                }, pos')
       | Parser_Combinators.ParseFail (uu___2, uu___3) ->
           Parser_Combinators.ParseFail ("expected boolean literal", pos))
let rdf_type_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let parse_a_keyword (input : Prims.string) (pos : Prims.nat) :
  RDF_Graph_Executable.wf_iri Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected 'a'", pos)
  else
    (let c = FStar_String.index input pos in
     if (FStar_Char.int_of_char c) = (Prims.of_int (0x61))
     then
       let next_pos = pos + Prims.int_one in
       (if next_pos >= len
        then Parser_Combinators.ParseOk (rdf_type_iri, next_pos)
        else
          (let nc = FStar_String.index input next_pos in
           if
             (is_turtle_ws nc) ||
               ((FStar_Char.int_of_char nc) = (Prims.of_int (0x23)))
           then Parser_Combinators.ParseOk (rdf_type_iri, next_pos)
           else Parser_Combinators.ParseFail ("expected 'a' keyword", pos)))
     else Parser_Combinators.ParseFail ("expected 'a'", pos))
let rdf_first_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
type object_result =
  {
  or_term: RDF_Graph_Executable.rdf_term ;
  or_triples: RDF_Graph_Executable.triple Prims.list ;
  or_state: turtle_state }
let __proj__Mkobject_result__item__or_term (projectee : object_result) :
  RDF_Graph_Executable.rdf_term=
  match projectee with | { or_term; or_triples; or_state;_} -> or_term
let __proj__Mkobject_result__item__or_triples (projectee : object_result) :
  RDF_Graph_Executable.triple Prims.list=
  match projectee with | { or_term; or_triples; or_state;_} -> or_triples
let __proj__Mkobject_result__item__or_state (projectee : object_result) :
  turtle_state=
  match projectee with | { or_term; or_triples; or_state;_} -> or_state
type subject_result =
  {
  sr_subject: RDF_Graph_Executable.subject ;
  sr_triples: RDF_Graph_Executable.triple Prims.list ;
  sr_state: turtle_state }
let __proj__Mksubject_result__item__sr_subject (projectee : subject_result) :
  RDF_Graph_Executable.subject=
  match projectee with | { sr_subject; sr_triples; sr_state;_} -> sr_subject
let __proj__Mksubject_result__item__sr_triples (projectee : subject_result) :
  RDF_Graph_Executable.triple Prims.list=
  match projectee with | { sr_subject; sr_triples; sr_state;_} -> sr_triples
let __proj__Mksubject_result__item__sr_state (projectee : subject_result) :
  turtle_state=
  match projectee with | { sr_subject; sr_triples; sr_state;_} -> sr_state
let rec parse_turtle_object (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  object_result Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("expected object", pos)
     else
       (let c = FStar_String.index input pos in
        let code = FStar_Char.int_of_char c in
        if code = (Prims.of_int (0x3C))
        then
          match parse_turtle_iri st input pos with
          | Parser_Combinators.ParseOk (i, pos') ->
              (if RDF_Graph_Executable.is_iri i
               then
                 Parser_Combinators.ParseOk
                   ({
                      or_term = (RDF_Graph_Executable.T_IRI i);
                      or_triples = [];
                      or_state = st
                    }, pos')
               else Parser_Combinators.ParseFail ("invalid IRI", pos))
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
        else
          if code = (Prims.of_int (0x5F))
          then
            (match Parser_NTriples.parse_bnode input pos with
             | Parser_Combinators.ParseOk (b, pos') ->
                 Parser_Combinators.ParseOk
                   ({
                      or_term = (RDF_Graph_Executable.T_BNode b);
                      or_triples = [];
                      or_state = st
                    }, pos')
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos))
          else
            if
              (code = (Prims.of_int (0x22))) ||
                (code = (Prims.of_int (0x27)))
            then
              (match parse_turtle_literal st input pos with
               | Parser_Combinators.ParseOk (lit, pos') ->
                   if RDF_Graph_Executable.literal_wf lit
                   then
                     Parser_Combinators.ParseOk
                       ({
                          or_term = (RDF_Graph_Executable.T_Literal lit);
                          or_triples = [];
                          or_state = st
                        }, pos')
                   else Parser_Combinators.ParseFail ("invalid literal", pos)
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos))
            else
              if code = (Prims.of_int (0x5B))
              then
                (let uu___5 = fresh_bnode st in
                 match uu___5 with
                 | (bnode_id, st1) ->
                     (match turtle_ws input (pos + Prims.int_one) with
                      | Parser_Combinators.ParseOk ((), pos2) ->
                          if
                            (pos2 < len) &&
                              ((FStar_Char.int_of_char
                                  (FStar_String.index input pos2))
                                 = (Prims.of_int (0x5D)))
                          then
                            Parser_Combinators.ParseOk
                              ({
                                 or_term =
                                   (RDF_Graph_Executable.T_BNode bnode_id);
                                 or_triples = [];
                                 or_state = st1
                               }, (pos2 + Prims.int_one))
                          else
                            (match parse_predicate_object_list st1
                                     (RDF_Graph_Executable.S_BNode bnode_id)
                                     input pos2 (fuel - Prims.int_one)
                             with
                             | Parser_Combinators.ParseOk
                                 ((triples, st2), pos3) ->
                                 (match turtle_ws input pos3 with
                                  | Parser_Combinators.ParseOk ((), pos4) ->
                                      if
                                        (pos4 < len) &&
                                          ((FStar_Char.int_of_char
                                              (FStar_String.index input pos4))
                                             = (Prims.of_int (0x5D)))
                                      then
                                        Parser_Combinators.ParseOk
                                          ({
                                             or_term =
                                               (RDF_Graph_Executable.T_BNode
                                                  bnode_id);
                                             or_triples = triples;
                                             or_state = st2
                                           }, (pos4 + Prims.int_one))
                                      else
                                        Parser_Combinators.ParseFail
                                          ("expected ']'", pos4))
                             | Parser_Combinators.ParseFail (msg, fpos) ->
                                 Parser_Combinators.ParseFail (msg, fpos))))
              else
                if code = (Prims.of_int (0x28))
                then
                  parse_collection st input (pos + Prims.int_one)
                    (fuel - Prims.int_one)
                else
                  (match parse_boolean_literal input pos with
                   | Parser_Combinators.ParseOk (lit, pos') ->
                       Parser_Combinators.ParseOk
                         ({
                            or_term = (RDF_Graph_Executable.T_Literal lit);
                            or_triples = [];
                            or_state = st
                          }, pos')
                   | Parser_Combinators.ParseFail (uu___7, uu___8) ->
                       (match parse_numeric_literal input pos with
                        | Parser_Combinators.ParseOk ((lexical, dt), pos') ->
                            let lit =
                              {
                                RDF_Graph_Executable.lexical_form = lexical;
                                RDF_Graph_Executable.datatype = dt;
                                RDF_Graph_Executable.lang_tag =
                                  FStar_Pervasives_Native.None
                              } in
                            if RDF_Graph_Executable.literal_wf lit
                            then
                              Parser_Combinators.ParseOk
                                ({
                                   or_term =
                                     (RDF_Graph_Executable.T_Literal lit);
                                   or_triples = [];
                                   or_state = st
                                 }, pos')
                            else
                              Parser_Combinators.ParseFail
                                ("invalid numeric literal", pos)
                        | Parser_Combinators.ParseFail (uu___9, uu___10) ->
                            (match parse_prefixed_name input pos with
                             | Parser_Combinators.ParseOk
                                 ((prefix, local), pos') ->
                                 (match resolve_prefixed_name st prefix local
                                  with
                                  | FStar_Pervasives_Native.Some resolved ->
                                      if RDF_Graph_Executable.is_iri resolved
                                      then
                                        Parser_Combinators.ParseOk
                                          ({
                                             or_term =
                                               (RDF_Graph_Executable.T_IRI
                                                  resolved);
                                             or_triples = [];
                                             or_state = st
                                           }, pos')
                                      else
                                        Parser_Combinators.ParseFail
                                          ("invalid resolved IRI", pos)
                                  | FStar_Pervasives_Native.None ->
                                      Parser_Combinators.ParseFail
                                        ((FStar_String.concat ""
                                            ["undefined prefix: "; prefix]),
                                          pos))
                             | Parser_Combinators.ParseFail
                                 (uu___11, uu___12) ->
                                 Parser_Combinators.ParseFail
                                   ("expected object", pos))))))
and parse_collection (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  object_result Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit in collection", pos)
  else
    (let len = FStar_String.strlen input in
     match turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then Parser_Combinators.ParseFail ("unterminated collection", pos1)
         else
           if
             (FStar_Char.int_of_char (FStar_String.index input pos1)) =
               (Prims.of_int (0x29))
           then
             Parser_Combinators.ParseOk
               ({
                  or_term = (RDF_Graph_Executable.T_IRI rdf_nil_iri);
                  or_triples = [];
                  or_state = st
                }, (pos1 + Prims.int_one))
           else
             (match parse_turtle_object st input pos1 (fuel - Prims.int_one)
              with
              | Parser_Combinators.ParseOk (first_obj, pos2) ->
                  let uu___3 = fresh_bnode first_obj.or_state in
                  (match uu___3 with
                   | (node_id, st2) ->
                       let node_subj = RDF_Graph_Executable.S_BNode node_id in
                       let first_triple =
                         {
                           RDF_Graph_Executable.s = node_subj;
                           RDF_Graph_Executable.p = rdf_first_iri;
                           RDF_Graph_Executable.o = (first_obj.or_term)
                         } in
                       (match parse_collection_rest st2 node_subj input pos2
                                (fuel - Prims.int_one)
                        with
                        | Parser_Combinators.ParseOk
                            ((rest_triples, rest_term, st3), pos3) ->
                            let rest_triple =
                              {
                                RDF_Graph_Executable.s = node_subj;
                                RDF_Graph_Executable.p = rdf_rest_iri;
                                RDF_Graph_Executable.o = rest_term
                              } in
                            let all_triples =
                              FStar_List_Tot_Base.op_At first_obj.or_triples
                                (FStar_List_Tot_Base.op_At
                                   [first_triple; rest_triple] rest_triples) in
                            Parser_Combinators.ParseOk
                              ({
                                 or_term =
                                   (RDF_Graph_Executable.T_BNode node_id);
                                 or_triples = all_triples;
                                 or_state = st3
                               }, pos3)
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos)))
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos)))
and parse_collection_rest (st : turtle_state)
  (prev_subj : RDF_Graph_Executable.subject) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.rdf_term *
    turtle_state) Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail ("recursion limit in collection rest", pos)
  else
    (let len = FStar_String.strlen input in
     match turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then Parser_Combinators.ParseFail ("unterminated collection", pos1)
         else
           if
             (FStar_Char.int_of_char (FStar_String.index input pos1)) =
               (Prims.of_int (0x29))
           then
             Parser_Combinators.ParseOk
               (([], (RDF_Graph_Executable.T_IRI rdf_nil_iri), st),
                 (pos1 + Prims.int_one))
           else
             (match parse_turtle_object st input pos1 (fuel - Prims.int_one)
              with
              | Parser_Combinators.ParseOk (next_obj, pos2) ->
                  let uu___3 = fresh_bnode next_obj.or_state in
                  (match uu___3 with
                   | (node_id, st2) ->
                       let node_subj = RDF_Graph_Executable.S_BNode node_id in
                       let first_triple =
                         {
                           RDF_Graph_Executable.s = node_subj;
                           RDF_Graph_Executable.p = rdf_first_iri;
                           RDF_Graph_Executable.o = (next_obj.or_term)
                         } in
                       (match parse_collection_rest st2 node_subj input pos2
                                (fuel - Prims.int_one)
                        with
                        | Parser_Combinators.ParseOk
                            ((rest_triples, rest_term, st3), pos3) ->
                            let rest_triple =
                              {
                                RDF_Graph_Executable.s = node_subj;
                                RDF_Graph_Executable.p = rdf_rest_iri;
                                RDF_Graph_Executable.o = rest_term
                              } in
                            let all_triples =
                              FStar_List_Tot_Base.op_At next_obj.or_triples
                                (FStar_List_Tot_Base.op_At
                                   [first_triple; rest_triple] rest_triples) in
                            Parser_Combinators.ParseOk
                              ((all_triples,
                                 (RDF_Graph_Executable.T_BNode node_id), st3),
                                pos3)
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos)))
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos)))
and parse_object_list (st : turtle_state)
  (subj : RDF_Graph_Executable.subject) (pred : RDF_Graph_Executable.wf_iri)
  (input : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * turtle_state)
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit in object list", pos)
  else
    (match parse_turtle_object st input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseOk (obj_res, pos1) ->
         let t =
           {
             RDF_Graph_Executable.s = subj;
             RDF_Graph_Executable.p = pred;
             RDF_Graph_Executable.o = (obj_res.or_term)
           } in
         let triples1 = FStar_List_Tot_Base.op_At obj_res.or_triples [t] in
         (match turtle_ws input pos1 with
          | Parser_Combinators.ParseOk ((), pos2) ->
              let len = FStar_String.strlen input in
              if
                (pos2 < len) &&
                  ((FStar_Char.int_of_char (FStar_String.index input pos2)) =
                     (Prims.of_int (0x2C)))
              then
                (match turtle_ws input (pos2 + Prims.int_one) with
                 | Parser_Combinators.ParseOk ((), pos3) ->
                     (match parse_object_list obj_res.or_state subj pred
                              input pos3 (fuel - Prims.int_one)
                      with
                      | Parser_Combinators.ParseOk
                          ((more_triples, st2), pos4) ->
                          Parser_Combinators.ParseOk
                            (((FStar_List_Tot_Base.op_At triples1
                                 more_triples), st2), pos4)
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos)))
              else
                Parser_Combinators.ParseOk
                  ((triples1, (obj_res.or_state)), pos2))
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos))
and parse_turtle_predicate (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  RDF_Graph_Executable.wf_iri Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit", pos)
  else
    (match parse_a_keyword input pos with
     | Parser_Combinators.ParseOk (iri_val, pos') ->
         Parser_Combinators.ParseOk (iri_val, pos')
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         (match parse_turtle_iri st input pos with
          | Parser_Combinators.ParseOk (i, pos') ->
              if RDF_Graph_Executable.is_iri i
              then Parser_Combinators.ParseOk (i, pos')
              else
                Parser_Combinators.ParseFail ("invalid predicate IRI", pos)
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)))
and parse_predicate_object_list (st : turtle_state)
  (subj : RDF_Graph_Executable.subject) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * turtle_state)
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("recursion limit in predicate-object list", pos)
  else
    (match parse_turtle_predicate st input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseOk (pred, pos1) ->
         (match turtle_ws input pos1 with
          | Parser_Combinators.ParseOk ((), pos2) ->
              (match parse_object_list st subj pred input pos2
                       (fuel - Prims.int_one)
               with
               | Parser_Combinators.ParseOk ((triples1, st1), pos3) ->
                   (match turtle_ws input pos3 with
                    | Parser_Combinators.ParseOk ((), pos4) ->
                        let len = FStar_String.strlen input in
                        if
                          (pos4 < len) &&
                            ((FStar_Char.int_of_char
                                (FStar_String.index input pos4))
                               = (Prims.of_int (0x3B)))
                        then
                          (match turtle_ws input (pos4 + Prims.int_one) with
                           | Parser_Combinators.ParseOk ((), pos5) ->
                               if pos5 >= len
                               then
                                 Parser_Combinators.ParseOk
                                   ((triples1, st1), pos5)
                               else
                                 (let nc = FStar_String.index input pos5 in
                                  let ncode = FStar_Char.int_of_char nc in
                                  if
                                    ((ncode = (Prims.of_int (0x2E))) ||
                                       (ncode = (Prims.of_int (0x5D))))
                                      || (ncode = (Prims.of_int (0x3B)))
                                  then
                                    (if ncode = (Prims.of_int (0x3B))
                                     then
                                       parse_trailing_semicolons st1 triples1
                                         subj input pos5
                                         (fuel - Prims.int_one)
                                     else
                                       Parser_Combinators.ParseOk
                                         ((triples1, st1), pos5))
                                  else
                                    (match parse_predicate_object_list st1
                                             subj input pos5
                                             (fuel - Prims.int_one)
                                     with
                                     | Parser_Combinators.ParseOk
                                         ((more_triples, st2), pos6) ->
                                         Parser_Combinators.ParseOk
                                           (((FStar_List_Tot_Base.op_At
                                                triples1 more_triples), st2),
                                             pos6)
                                     | Parser_Combinators.ParseFail
                                         (msg, fpos) ->
                                         Parser_Combinators.ParseFail
                                           (msg, fpos))))
                        else
                          Parser_Combinators.ParseOk ((triples1, st1), pos4))
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)))
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos))
and parse_trailing_semicolons (st : turtle_state)
  (triples : RDF_Graph_Executable.triple Prims.list)
  (subj : RDF_Graph_Executable.subject) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * turtle_state)
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ((triples, st), pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseOk ((triples, st), pos)
     else
       (let c = FStar_String.index input pos in
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x3B))
        then
          match turtle_ws input (pos + Prims.int_one) with
          | Parser_Combinators.ParseOk ((), pos2) ->
              (if pos2 >= len
               then Parser_Combinators.ParseOk ((triples, st), pos2)
               else
                 (let nc = FStar_String.index input pos2 in
                  let ncode = FStar_Char.int_of_char nc in
                  if
                    ((ncode = (Prims.of_int (0x2E))) ||
                       (ncode = (Prims.of_int (0x5D))))
                      || (ncode = (Prims.of_int (0x3B)))
                  then
                    parse_trailing_semicolons st triples subj input pos2
                      (fuel - Prims.int_one)
                  else
                    (match parse_predicate_object_list st subj input pos2
                             (fuel - Prims.int_one)
                     with
                     | Parser_Combinators.ParseOk ((more_triples, st2), pos3)
                         ->
                         Parser_Combinators.ParseOk
                           (((FStar_List_Tot_Base.op_At triples more_triples),
                              st2), pos3)
                     | Parser_Combinators.ParseFail (msg, fpos) ->
                         Parser_Combinators.ParseFail (msg, fpos))))
        else Parser_Combinators.ParseOk ((triples, st), pos)))
let parse_turtle_subject (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  subject_result Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("expected subject", pos)
     else
       (let c = FStar_String.index input pos in
        let code = FStar_Char.int_of_char c in
        if code = (Prims.of_int (0x3C))
        then
          match parse_turtle_iri st input pos with
          | Parser_Combinators.ParseOk (i, pos') ->
              (if RDF_Graph_Executable.is_iri i
               then
                 Parser_Combinators.ParseOk
                   ({
                      sr_subject = (RDF_Graph_Executable.S_IRI i);
                      sr_triples = [];
                      sr_state = st
                    }, pos')
               else Parser_Combinators.ParseFail ("invalid subject IRI", pos))
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
        else
          if code = (Prims.of_int (0x5F))
          then
            (match Parser_NTriples.parse_bnode input pos with
             | Parser_Combinators.ParseOk (b, pos') ->
                 Parser_Combinators.ParseOk
                   ({
                      sr_subject = (RDF_Graph_Executable.S_BNode b);
                      sr_triples = [];
                      sr_state = st
                    }, pos')
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos))
          else
            if code = (Prims.of_int (0x5B))
            then
              (let uu___4 = fresh_bnode st in
               match uu___4 with
               | (bnode_id, st1) ->
                   (match turtle_ws input (pos + Prims.int_one) with
                    | Parser_Combinators.ParseOk ((), pos2) ->
                        if
                          (pos2 < len) &&
                            ((FStar_Char.int_of_char
                                (FStar_String.index input pos2))
                               = (Prims.of_int (0x5D)))
                        then
                          Parser_Combinators.ParseOk
                            ({
                               sr_subject =
                                 (RDF_Graph_Executable.S_BNode bnode_id);
                               sr_triples = [];
                               sr_state = st1
                             }, (pos2 + Prims.int_one))
                        else
                          (match parse_predicate_object_list st1
                                   (RDF_Graph_Executable.S_BNode bnode_id)
                                   input pos2 (fuel - Prims.int_one)
                           with
                           | Parser_Combinators.ParseOk
                               ((triples, st2), pos3) ->
                               (match turtle_ws input pos3 with
                                | Parser_Combinators.ParseOk ((), pos4) ->
                                    if
                                      (pos4 < len) &&
                                        ((FStar_Char.int_of_char
                                            (FStar_String.index input pos4))
                                           = (Prims.of_int (0x5D)))
                                    then
                                      Parser_Combinators.ParseOk
                                        ({
                                           sr_subject =
                                             (RDF_Graph_Executable.S_BNode
                                                bnode_id);
                                           sr_triples = triples;
                                           sr_state = st2
                                         }, (pos4 + Prims.int_one))
                                    else
                                      Parser_Combinators.ParseFail
                                        ("expected ']'", pos4))
                           | Parser_Combinators.ParseFail (msg, fpos) ->
                               Parser_Combinators.ParseFail (msg, fpos))))
            else
              if code = (Prims.of_int (0x28))
              then
                (match parse_collection st input (pos + Prims.int_one)
                         (fuel - Prims.int_one)
                 with
                 | Parser_Combinators.ParseOk (obj_res, pos') ->
                     (match obj_res.or_term with
                      | RDF_Graph_Executable.T_IRI i ->
                          Parser_Combinators.ParseOk
                            ({
                               sr_subject = (RDF_Graph_Executable.S_IRI i);
                               sr_triples = (obj_res.or_triples);
                               sr_state = (obj_res.or_state)
                             }, pos')
                      | RDF_Graph_Executable.T_BNode b ->
                          Parser_Combinators.ParseOk
                            ({
                               sr_subject = (RDF_Graph_Executable.S_BNode b);
                               sr_triples = (obj_res.or_triples);
                               sr_state = (obj_res.or_state)
                             }, pos')
                      | uu___5 ->
                          Parser_Combinators.ParseFail
                            ("collection did not produce a valid subject",
                              pos))
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos))
              else
                (match parse_prefixed_name input pos with
                 | Parser_Combinators.ParseOk ((prefix, local), pos') ->
                     (match resolve_prefixed_name st prefix local with
                      | FStar_Pervasives_Native.Some resolved ->
                          if RDF_Graph_Executable.is_iri resolved
                          then
                            Parser_Combinators.ParseOk
                              ({
                                 sr_subject =
                                   (RDF_Graph_Executable.S_IRI resolved);
                                 sr_triples = [];
                                 sr_state = st
                               }, pos')
                          else
                            Parser_Combinators.ParseFail
                              ("invalid resolved IRI", pos)
                      | FStar_Pervasives_Native.None ->
                          Parser_Combinators.ParseFail
                            ((FStar_String.concat ""
                                ["undefined prefix: "; prefix]), pos))
                 | Parser_Combinators.ParseFail (uu___6, uu___7) ->
                     Parser_Combinators.ParseFail ("expected subject", pos))))
let parse_turtle_statement (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * turtle_state)
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("recursion limit", pos)
  else
    (let len = FStar_String.strlen input in
     match turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then Parser_Combinators.ParseOk (([], st), pos1)
         else
           (match parse_prefix_directive st input pos1 with
            | Parser_Combinators.ParseOk ((prefix, iri_val), pos2) ->
                let new_prefixes = (prefix, iri_val) :: (st.prefixes) in
                Parser_Combinators.ParseOk
                  (([],
                     {
                       prefixes = new_prefixes;
                       base_iri = (st.base_iri);
                       bnode_counter = (st.bnode_counter)
                     }), pos2)
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                (match parse_base_directive st input pos1 with
                 | Parser_Combinators.ParseOk (base_val, pos2) ->
                     Parser_Combinators.ParseOk
                       (([],
                          {
                            prefixes = (st.prefixes);
                            base_iri = base_val;
                            bnode_counter = (st.bnode_counter)
                          }), pos2)
                 | Parser_Combinators.ParseFail (uu___4, uu___5) ->
                     (match parse_turtle_subject st input pos1 fuel with
                      | Parser_Combinators.ParseOk (subj_res, pos2) ->
                          (match turtle_ws input pos2 with
                           | Parser_Combinators.ParseOk ((), pos3) ->
                               if pos3 >= len
                               then
                                 (if
                                    (FStar_List_Tot_Base.length
                                       subj_res.sr_triples)
                                      > Prims.int_zero
                                  then
                                    Parser_Combinators.ParseOk
                                      (((subj_res.sr_triples),
                                         (subj_res.sr_state)), pos3)
                                  else
                                    Parser_Combinators.ParseFail
                                      ("expected predicate after subject",
                                        pos3))
                               else
                                 (let nc = FStar_String.index input pos3 in
                                  let ncode = FStar_Char.int_of_char nc in
                                  if ncode = (Prims.of_int (0x2E))
                                  then
                                    (if
                                       (FStar_List_Tot_Base.length
                                          subj_res.sr_triples)
                                         > Prims.int_zero
                                     then
                                       Parser_Combinators.ParseOk
                                         (((subj_res.sr_triples),
                                            (subj_res.sr_state)),
                                           (pos3 + Prims.int_one))
                                     else
                                       Parser_Combinators.ParseFail
                                         ("expected predicate after subject",
                                           pos3))
                                  else
                                    if
                                      (ncode = (Prims.of_int (0x7D))) &&
                                        ((FStar_List_Tot_Base.length
                                            subj_res.sr_triples)
                                           > Prims.int_zero)
                                    then
                                      Parser_Combinators.ParseOk
                                        (((subj_res.sr_triples),
                                           (subj_res.sr_state)), pos3)
                                    else
                                      (match parse_predicate_object_list
                                               subj_res.sr_state
                                               subj_res.sr_subject input pos3
                                               (fuel - Prims.int_one)
                                       with
                                       | Parser_Combinators.ParseOk
                                           ((po_triples, st2), pos4) ->
                                           let all_triples =
                                             FStar_List_Tot_Base.op_At
                                               subj_res.sr_triples po_triples in
                                           (match turtle_ws input pos4 with
                                            | Parser_Combinators.ParseOk
                                                ((), pos5) ->
                                                if
                                                  (pos5 < len) &&
                                                    ((FStar_Char.int_of_char
                                                        (FStar_String.index
                                                           input pos5))
                                                       =
                                                       (Prims.of_int (0x2E)))
                                                then
                                                  Parser_Combinators.ParseOk
                                                    ((all_triples, st2),
                                                      (pos5 + Prims.int_one))
                                                else
                                                  if
                                                    (pos5 < len) &&
                                                      ((FStar_Char.int_of_char
                                                          (FStar_String.index
                                                             input pos5))
                                                         =
                                                         (Prims.of_int (0x7D)))
                                                  then
                                                    Parser_Combinators.ParseOk
                                                      ((all_triples, st2),
                                                        pos5)
                                                  else
                                                    Parser_Combinators.ParseFail
                                                      ("expected '.' after triple",
                                                        pos5))
                                       | Parser_Combinators.ParseFail
                                           (msg, fpos) ->
                                           Parser_Combinators.ParseFail
                                             (msg, fpos))))
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos)))))
type turtle_doc_result =
  {
  tdr_triples: RDF_Graph_Executable.triple Prims.list ;
  tdr_state: turtle_state ;
  tdr_has_error: Prims.bool }
let __proj__Mkturtle_doc_result__item__tdr_triples
  (projectee : turtle_doc_result) : RDF_Graph_Executable.triple Prims.list=
  match projectee with
  | { tdr_triples; tdr_state; tdr_has_error;_} -> tdr_triples
let __proj__Mkturtle_doc_result__item__tdr_state
  (projectee : turtle_doc_result) : turtle_state=
  match projectee with
  | { tdr_triples; tdr_state; tdr_has_error;_} -> tdr_state
let __proj__Mkturtle_doc_result__item__tdr_has_error
  (projectee : turtle_doc_result) : Prims.bool=
  match projectee with
  | { tdr_triples; tdr_state; tdr_has_error;_} -> tdr_has_error
let rec parse_turtle_doc (st : turtle_state) (input : Prims.string)
  (pos : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (has_error : Prims.bool) (fuel : Prims.nat) : turtle_doc_result=
  if fuel = Prims.int_zero
  then
    {
      tdr_triples = (FStar_List_Tot_Base.rev acc);
      tdr_state = st;
      tdr_has_error = has_error
    }
  else
    (let len = FStar_String.strlen input in
     match turtle_ws input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         if pos1 >= len
         then
           {
             tdr_triples = (FStar_List_Tot_Base.rev acc);
             tdr_state = st;
             tdr_has_error = has_error
           }
         else
           (match parse_turtle_statement st input pos1 fuel with
            | Parser_Combinators.ParseOk ((triples, st'), pos2) ->
                if pos2 = pos1
                then
                  {
                    tdr_triples =
                      (FStar_List_Tot_Base.rev
                         (FStar_List_Tot_Base.op_At
                            (FStar_List_Tot_Base.rev triples) acc));
                    tdr_state = st';
                    tdr_has_error = has_error
                  }
                else
                  parse_turtle_doc st' input pos2
                    (FStar_List_Tot_Base.op_At
                       (FStar_List_Tot_Base.rev triples) acc) has_error
                    (fuel - Prims.int_one)
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                let pos2 = skip_to_eol input pos1 (len - pos1) in
                if pos2 = pos1
                then
                  {
                    tdr_triples = (FStar_List_Tot_Base.rev acc);
                    tdr_state = st;
                    tdr_has_error = true
                  }
                else
                  parse_turtle_doc st input pos2 acc true
                    (fuel - Prims.int_one)))
let parse_turtle (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list=
  let len = FStar_String.strlen input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (2)) in
  let r =
    parse_turtle_doc empty_turtle_state input Prims.int_zero [] false fuel in
  r.tdr_triples
let parse_turtle_with_base (input : Prims.string) (base : Prims.string) :
  RDF_Graph_Executable.triple Prims.list=
  let len = FStar_String.strlen input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (2)) in
  let st =
    {
      prefixes = (empty_turtle_state.prefixes);
      base_iri = base;
      bnode_counter = (empty_turtle_state.bnode_counter)
    } in
  let r = parse_turtle_doc st input Prims.int_zero [] false fuel in
  r.tdr_triples
let parse_turtle_strict (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list FStar_Pervasives_Native.option=
  let len = FStar_String.strlen input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (2)) in
  let r =
    parse_turtle_doc empty_turtle_state input Prims.int_zero [] false fuel in
  if r.tdr_has_error
  then FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.Some (r.tdr_triples)
let parse_turtle_with_base_strict (input : Prims.string)
  (base : Prims.string) :
  RDF_Graph_Executable.triple Prims.list FStar_Pervasives_Native.option=
  let len = FStar_String.strlen input in
  let fuel = (len + Prims.int_one) * (Prims.of_int (2)) in
  let st =
    {
      prefixes = (empty_turtle_state.prefixes);
      base_iri = base;
      bnode_counter = (empty_turtle_state.bnode_counter)
    } in
  let r = parse_turtle_doc st input Prims.int_zero [] false fuel in
  if r.tdr_has_error
  then FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.Some (r.tdr_triples)
