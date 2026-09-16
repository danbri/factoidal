open Prims
let rec join_with_acc (sep : Prims.string) (xs : Prims.string Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> acc
  | x::[] -> x :: acc
  | x::rest -> join_with_acc sep rest (sep :: x :: acc)
let join_with (sep : Prims.string) (xs : Prims.string Prims.list) :
  Prims.string=
  FStar_String.concat "" (FStar_List_Tot_Base.rev (join_with_acc sep xs []))
type prefix_table = (Prims.string * Prims.string) Prims.list
let ts_starts_with_strict (s : Prims.string) (pfx : Prims.string) :
  Prims.bool=
  let pl = Parser_FastString.fs_byte_length pfx in
  let sl = Parser_FastString.fs_byte_length s in
  (sl > pl) && ((Parser_FastString.fs_byte_sub s Prims.int_zero pl) = pfx)
let rec ts_find_prefix (table : prefix_table) (iri : Prims.string) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  match table with
  | [] -> FStar_Pervasives_Native.None
  | (ns, abbr)::rest ->
      if ts_starts_with_strict iri ns
      then FStar_Pervasives_Native.Some (ns, abbr)
      else ts_find_prefix rest iri
let ts_local_ok (local : Prims.string) : Prims.bool=
  ((Parser_FastString.fs_byte_length local) = Prims.int_zero) ||
    (Parser_Turtle.validate_pn_local local)
let ts_abbreviate_iri (table : prefix_table) (iri : Prims.string) :
  Prims.string=
  match ts_find_prefix table iri with
  | FStar_Pervasives_Native.Some (ns, abbr) ->
      let nsl = Parser_FastString.fs_byte_length ns in
      let il = Parser_FastString.fs_byte_length iri in
      if nsl < il
      then
        let local = Parser_FastString.fs_byte_sub iri nsl (il - nsl) in
        (if ts_local_ok local
         then Prims.strcat abbr local
         else Prims.strcat "<" (Prims.strcat iri ">"))
      else Prims.strcat "<" (Prims.strcat iri ">")
  | FStar_Pervasives_Native.None -> Prims.strcat "<" (Prims.strcat iri ">")
type ('table, 'iri) compacts_to_pname_safe = Obj.t
type turtle_render_options =
  {
  tro_prefixes: prefix_table ;
  tro_literal_shorthand: Prims.bool }
let __proj__Mkturtle_render_options__item__tro_prefixes
  (projectee : turtle_render_options) : prefix_table=
  match projectee with
  | { tro_prefixes; tro_literal_shorthand;_} -> tro_prefixes
let __proj__Mkturtle_render_options__item__tro_literal_shorthand
  (projectee : turtle_render_options) : Prims.bool=
  match projectee with
  | { tro_prefixes; tro_literal_shorthand;_} -> tro_literal_shorthand
let turtle_render_defaults : turtle_render_options=
  { tro_prefixes = []; tro_literal_shorthand = true }
let ts_digit_byte (b : Prims.nat) : Prims.bool=
  (b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))
let rec ts_scan_digits (s : Prims.string) (len : Prims.nat) (pos : Prims.nat)
  : Prims.nat=
  if pos >= len
  then pos
  else
    if ts_digit_byte (Parser_FastString.fs_byte_at s pos)
    then ts_scan_digits s len (pos + Prims.int_one)
    else pos
let ts_exponent_suffix (s : Prims.string) (len : Prims.nat) (pos : Prims.nat)
  : Prims.bool=
  if pos >= len
  then false
  else
    (let e = Parser_FastString.fs_byte_at s pos in
     if
       Prims.op_Negation
         ((e = (Prims.of_int (0x65))) || (e = (Prims.of_int (0x45))))
     then false
     else
       (let spos = pos + Prims.int_one in
        if spos >= len
        then false
        else
          (let sb = Parser_FastString.fs_byte_at s spos in
           let dpos =
             if (sb = (Prims.of_int (0x2B))) || (sb = (Prims.of_int (0x2D)))
             then spos + Prims.int_one
             else spos in
           if dpos >= len then false else (ts_scan_digits s len dpos) = len)))
let ts_optional_sign_end (s : Prims.string) (len : Prims.nat) : Prims.nat=
  if len = Prims.int_zero
  then Prims.int_zero
  else
    (let b0 = Parser_FastString.fs_byte_at s Prims.int_zero in
     if (b0 = (Prims.of_int (0x2B))) || (b0 = (Prims.of_int (0x2D)))
     then Prims.int_one
     else Prims.int_zero)
let is_turtle_integer_lexical (s : Prims.string) : Prims.bool=
  let len = Parser_FastString.fs_byte_length s in
  let dpos = ts_optional_sign_end s len in
  if (len = Prims.int_zero) || (dpos >= len)
  then false
  else (ts_scan_digits s len dpos) = len
let is_turtle_decimal_lexical (s : Prims.string) : Prims.bool=
  let len = Parser_FastString.fs_byte_length s in
  let dpos = ts_optional_sign_end s len in
  if (len = Prims.int_zero) || (dpos >= len)
  then false
  else
    (let ipos = ts_scan_digits s len dpos in
     if
       (ipos >= len) ||
         ((Parser_FastString.fs_byte_at s ipos) <> (Prims.of_int (0x2E)))
     then false
     else
       (let fpos = ipos + Prims.int_one in
        let fend = ts_scan_digits s len fpos in (fend > fpos) && (fend = len)))
let is_turtle_double_lexical (s : Prims.string) : Prims.bool=
  let len = Parser_FastString.fs_byte_length s in
  let dpos = ts_optional_sign_end s len in
  if (len = Prims.int_zero) || (dpos >= len)
  then false
  else
    (let c = Parser_FastString.fs_byte_at s dpos in
     if c = (Prims.of_int (0x2E))
     then
       let fpos = dpos + Prims.int_one in
       (if fpos >= len
        then false
        else
          (let fend = ts_scan_digits s len fpos in
           (fend > fpos) && (ts_exponent_suffix s len fend)))
     else
       if ts_digit_byte c
       then
         (let iend = ts_scan_digits s len dpos in
          if
            (iend < len) &&
              ((Parser_FastString.fs_byte_at s iend) = (Prims.of_int (0x2E)))
          then
            let fpos = iend + Prims.int_one in
            let fend = ts_scan_digits s len fpos in
            ts_exponent_suffix s len fend
          else ts_exponent_suffix s len iend)
       else false)
let is_turtle_boolean_lexical (s : Prims.string) : Prims.bool=
  (s = "true") || (s = "false")
let literal_shorthand (l : RDF_Term.literal) :
  Prims.string FStar_Pervasives_Native.option=
  if
    (l.RDF_Term.datatype = RDF_Term.xsd_integer) &&
      (is_turtle_integer_lexical l.RDF_Term.lexical_form)
  then FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
  else
    if
      (l.RDF_Term.datatype = RDF_Term.xsd_decimal) &&
        (is_turtle_decimal_lexical l.RDF_Term.lexical_form)
    then FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
    else
      if
        (l.RDF_Term.datatype = RDF_Term.xsd_double) &&
          (is_turtle_double_lexical l.RDF_Term.lexical_form)
      then FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
      else
        if
          (l.RDF_Term.datatype = RDF_Term.xsd_boolean) &&
            (is_turtle_boolean_lexical l.RDF_Term.lexical_form)
        then FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
        else FStar_Pervasives_Native.None
let rec ts_term_to_turtle (table : prefix_table) (shorthand : Prims.bool)
  (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> ts_abbreviate_iri table i
  | RDF_Term.T_BNode b -> Prims.strcat "_:" b
  | RDF_Term.T_Literal l ->
      let esc =
        RDF_NQuads_Serialize.nq_escape_literal l.RDF_Term.lexical_form in
      (match l.RDF_Term.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           let ds =
             match l.RDF_Term.direction with
             | FStar_Pervasives_Native.Some (RDF_Term.Dir_LTR) -> "--ltr"
             | FStar_Pervasives_Native.Some (RDF_Term.Dir_RTL) -> "--rtl"
             | FStar_Pervasives_Native.None -> "" in
           Prims.strcat "\""
             (Prims.strcat esc (Prims.strcat "\"@" (Prims.strcat tag ds)))
       | FStar_Pervasives_Native.None ->
           if l.RDF_Term.datatype = RDF_Term.xsd_string
           then Prims.strcat "\"" (Prims.strcat esc "\"")
           else
             (match if shorthand
                    then literal_shorthand l
                    else FStar_Pervasives_Native.None
              with
              | FStar_Pervasives_Native.Some bare -> bare
              | FStar_Pervasives_Native.None ->
                  Prims.strcat "\""
                    (Prims.strcat esc
                       (Prims.strcat "\"^^"
                          (ts_abbreviate_iri table l.RDF_Term.datatype)))))
  | RDF_Term.T_TripleTerm (s, p, o) ->
      let subj_str =
        match s with
        | RDF_Term.S_IRI i -> ts_abbreviate_iri table i
        | RDF_Term.S_BNode b -> Prims.strcat "_:" b in
      let pred_str =
        if p = RDFS_Closure.rdf_type then "a" else ts_abbreviate_iri table p in
      Prims.strcat "<<( "
        (Prims.strcat subj_str
           (Prims.strcat " "
              (Prims.strcat pred_str
                 (Prims.strcat " "
                    (Prims.strcat (ts_term_to_turtle table shorthand o)
                       " )>>")))))
let ts_subject_to_turtle (table : prefix_table) (s : RDF_Term.subject) :
  Prims.string=
  match s with
  | RDF_Term.S_IRI i -> ts_abbreviate_iri table i
  | RDF_Term.S_BNode b -> Prims.strcat "_:" b
let ts_predicate_to_turtle (table : prefix_table) (p : RDF_Term.wf_iri) :
  Prims.string=
  if p = RDFS_Closure.rdf_type then "a" else ts_abbreviate_iri table p
type subj_state =
  {
  ss_subj: RDF_Term.subject ;
  ss_subj_text: Prims.string ;
  ss_cur_pred: RDF_Term.wf_iri ;
  ss_cur_pred_text: Prims.string ;
  ss_cur_objs: Prims.string Prims.list ;
  ss_pred_chunks: Prims.string Prims.list }
let __proj__Mksubj_state__item__ss_subj (projectee : subj_state) :
  RDF_Term.subject=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_subj
let __proj__Mksubj_state__item__ss_subj_text (projectee : subj_state) :
  Prims.string=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_subj_text
let __proj__Mksubj_state__item__ss_cur_pred (projectee : subj_state) :
  RDF_Term.wf_iri=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_cur_pred
let __proj__Mksubj_state__item__ss_cur_pred_text (projectee : subj_state) :
  Prims.string=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_cur_pred_text
let __proj__Mksubj_state__item__ss_cur_objs (projectee : subj_state) :
  Prims.string Prims.list=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_cur_objs
let __proj__Mksubj_state__item__ss_pred_chunks (projectee : subj_state) :
  Prims.string Prims.list=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_pred_chunks
let finish_pred (st : subj_state) : Prims.string Prims.list=
  let objs = FStar_List_Tot_Base.rev st.ss_cur_objs in
  let group =
    Prims.strcat st.ss_cur_pred_text
      (Prims.strcat " " (join_with " , " objs)) in
  group :: (st.ss_pred_chunks)
let finish_subj (st : subj_state) : Prims.string=
  let chunks = FStar_List_Tot_Base.rev (finish_pred st) in
  Prims.strcat st.ss_subj_text
    (Prims.strcat " " (Prims.strcat (join_with " ;\n    " chunks) " .\n\n"))
let rec walk_triples (table : prefix_table) (shorthand : Prims.bool)
  (sorted : RDF_Graph.rdf_graph)
  (st : subj_state FStar_Pervasives_Native.option)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match sorted with
  | [] ->
      (match st with
       | FStar_Pervasives_Native.None -> acc
       | FStar_Pervasives_Native.Some s -> (finish_subj s) :: acc)
  | t::rest ->
      let obj_text = ts_term_to_turtle table shorthand t.RDF_Triple.o in
      (match st with
       | FStar_Pervasives_Native.None ->
           let st' =
             {
               ss_subj = (t.RDF_Triple.s);
               ss_subj_text = (ts_subject_to_turtle table t.RDF_Triple.s);
               ss_cur_pred = (t.RDF_Triple.p);
               ss_cur_pred_text =
                 (ts_predicate_to_turtle table t.RDF_Triple.p);
               ss_cur_objs = [obj_text];
               ss_pred_chunks = []
             } in
           walk_triples table shorthand rest
             (FStar_Pervasives_Native.Some st') acc
       | FStar_Pervasives_Native.Some s ->
           if RDF_Term.subject_eq s.ss_subj t.RDF_Triple.s
           then
             (if s.ss_cur_pred = t.RDF_Triple.p
              then
                let s' =
                  {
                    ss_subj = (s.ss_subj);
                    ss_subj_text = (s.ss_subj_text);
                    ss_cur_pred = (s.ss_cur_pred);
                    ss_cur_pred_text = (s.ss_cur_pred_text);
                    ss_cur_objs = (obj_text :: (s.ss_cur_objs));
                    ss_pred_chunks = (s.ss_pred_chunks)
                  } in
                walk_triples table shorthand rest
                  (FStar_Pervasives_Native.Some s') acc
              else
                (let pred_chunks' = finish_pred s in
                 let s' =
                   {
                     ss_subj = (s.ss_subj);
                     ss_subj_text = (s.ss_subj_text);
                     ss_cur_pred = (t.RDF_Triple.p);
                     ss_cur_pred_text =
                       (ts_predicate_to_turtle table t.RDF_Triple.p);
                     ss_cur_objs = [obj_text];
                     ss_pred_chunks = pred_chunks'
                   } in
                 walk_triples table shorthand rest
                   (FStar_Pervasives_Native.Some s') acc))
           else
             (let block = finish_subj s in
              let st' =
                {
                  ss_subj = (t.RDF_Triple.s);
                  ss_subj_text = (ts_subject_to_turtle table t.RDF_Triple.s);
                  ss_cur_pred = (t.RDF_Triple.p);
                  ss_cur_pred_text =
                    (ts_predicate_to_turtle table t.RDF_Triple.p);
                  ss_cur_objs = [obj_text];
                  ss_pred_chunks = []
                } in
              walk_triples table shorthand rest
                (FStar_Pervasives_Native.Some st') (block :: acc)))
let render_triples (table : prefix_table) (shorthand : Prims.bool)
  (g : RDF_Graph.rdf_graph) : Prims.string=
  let sorted = FStar_List_Tot_Base.sortWith RDF_Graph.triple_cmp g in
  let blocks =
    walk_triples table shorthand sorted FStar_Pervasives_Native.None [] in
  FStar_String.concat "" (FStar_List_Tot_Base.rev blocks)
let rec render_prefix_header (table : prefix_table) :
  Prims.string Prims.list=
  match table with
  | [] -> []
  | (ns, abbr)::rest ->
      (Prims.strcat "@prefix "
         (Prims.strcat abbr (Prims.strcat " <" (Prims.strcat ns "> .\n"))))
      :: (render_prefix_header rest)
let turtle_of_graph (table : (Prims.string * Prims.string) Prims.list)
  (shorthand : Prims.bool) (g : RDF_Graph.rdf_graph) : Prims.string=
  let header_lines = render_prefix_header table in
  let header = FStar_String.concat "" header_lines in
  let sep = match header_lines with | [] -> "" | uu___ -> "\n" in
  let body = render_triples table shorthand g in
  Prims.strcat header (Prims.strcat sep body)
let rec last_ns_split_from (s : Prims.string) (len : Prims.nat)
  (pos : Prims.nat) (best : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  if pos >= len
  then best
  else
    (let b = Parser_FastString.fs_byte_at s pos in
     if (b = (Prims.of_int (0x23))) || (b = (Prims.of_int (0x2F)))
     then
       last_ns_split_from s len (pos + Prims.int_one)
         (FStar_Pervasives_Native.Some pos)
     else last_ns_split_from s len (pos + Prims.int_one) best)
let last_ns_split (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  last_ns_split_from s (Parser_FastString.fs_byte_length s) Prims.int_zero
    FStar_Pervasives_Native.None
let ns_split (iri : Prims.string) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  match last_ns_split iri with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some idx ->
      let len = Parser_FastString.fs_byte_length iri in
      if (idx + Prims.int_one) <= len
      then
        let ns =
          Parser_FastString.fs_byte_sub iri Prims.int_zero
            (idx + Prims.int_one) in
        let local =
          Parser_FastString.fs_byte_sub iri (idx + Prims.int_one)
            (len - (idx + Prims.int_one)) in
        FStar_Pervasives_Native.Some (ns, local)
      else FStar_Pervasives_Native.None
let rec collect_iris_acc (g : RDF_Graph.rdf_graph)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match g with
  | [] -> acc
  | t::rest ->
      let acc1 = (t.RDF_Triple.p) :: acc in
      let acc2 =
        match t.RDF_Triple.s with
        | RDF_Term.S_IRI i -> i :: acc1
        | RDF_Term.S_BNode uu___ -> acc1 in
      let acc3 =
        match t.RDF_Triple.o with
        | RDF_Term.T_IRI i -> i :: acc2
        | RDF_Term.T_BNode uu___ -> acc2
        | RDF_Term.T_Literal l ->
            (match l.RDF_Term.lang_tag with
             | FStar_Pervasives_Native.Some uu___ -> acc2
             | FStar_Pervasives_Native.None ->
                 if l.RDF_Term.datatype = RDF_Term.xsd_string
                 then acc2
                 else (l.RDF_Term.datatype) :: acc2)
        | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> acc2 in
      collect_iris_acc rest acc3
let rec candidate_namespaces_acc (iris : Prims.string Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match iris with
  | [] -> acc
  | i::rest ->
      (match ns_split i with
       | FStar_Pervasives_Native.None -> candidate_namespaces_acc rest acc
       | FStar_Pervasives_Native.Some (ns, local) ->
           if
             ((Parser_FastString.fs_byte_length local) > Prims.int_zero) &&
               (Parser_Turtle.validate_pn_local local)
           then candidate_namespaces_acc rest (ns :: acc)
           else candidate_namespaces_acc rest acc)
let rec count_runs (sorted : Prims.string Prims.list) :
  (Prims.string * Prims.nat) Prims.list=
  match sorted with
  | [] -> []
  | x::[] -> [(x, Prims.int_one)]
  | x::y::rest ->
      if x = y
      then
        (match count_runs (y :: rest) with
         | (y', n)::more -> (y', (n + Prims.int_one)) :: more
         | [] -> [(x, Prims.int_one)])
      else (x, Prims.int_one) :: (count_runs (y :: rest))
let count_desc_compare (a : (Prims.string * Prims.nat))
  (b : (Prims.string * Prims.nat)) : Prims.int=
  if (FStar_Pervasives_Native.snd a) = (FStar_Pervasives_Native.snd b)
  then Prims.int_zero
  else
    if (FStar_Pervasives_Native.snd a) > (FStar_Pervasives_Native.snd b)
    then (Prims.of_int (-1))
    else Prims.int_one
let digit_char (n : Prims.nat) : Prims.string=
  match n with
  | uu___ when uu___ = Prims.int_zero -> "0"
  | uu___ when uu___ = Prims.int_one -> "1"
  | uu___ when uu___ = (Prims.of_int (2)) -> "2"
  | uu___ when uu___ = (Prims.of_int (3)) -> "3"
  | uu___ when uu___ = (Prims.of_int (4)) -> "4"
  | uu___ when uu___ = (Prims.of_int (5)) -> "5"
  | uu___ when uu___ = (Prims.of_int (6)) -> "6"
  | uu___ when uu___ = (Prims.of_int (7)) -> "7"
  | uu___ when uu___ = (Prims.of_int (8)) -> "8"
  | uu___ -> "9"
let rec take_at_most (n : Prims.nat)
  (l : (Prims.string * Prims.nat) Prims.list) :
  (Prims.string * Prims.nat) Prims.list=
  if n = Prims.int_zero
  then []
  else
    (match l with
     | [] -> []
     | hd::tl -> hd :: (take_at_most (n - Prims.int_one) tl))
let rec assign_labels_avoiding (reserved : Prims.string Prims.list)
  (idx : Prims.nat) (namespaces : (Prims.string * Prims.nat) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match namespaces with
  | [] -> []
  | (ns, uu___)::rest ->
      if idx >= (Prims.of_int (9))
      then []
      else
        (let label = Prims.strcat "ns" (Prims.strcat (digit_char idx) ":") in
         if FStar_List_Tot_Base.mem label reserved
         then
           assign_labels_avoiding reserved (idx + Prims.int_one) namespaces
         else (ns, label) ::
           (assign_labels_avoiding reserved (idx + Prims.int_one) rest))
let rec ts_any_iri_uses_ns (iris : Prims.string Prims.list)
  (ns : Prims.string) : Prims.bool=
  match iris with
  | [] -> false
  | i::rest ->
      if ts_starts_with_strict i ns then true else ts_any_iri_uses_ns rest ns
let rec ts_user_used (iris : Prims.string Prims.list) (caller : prefix_table)
  (seen_ns : Prims.string Prims.list) : prefix_table=
  match caller with
  | [] -> []
  | (ns, label)::rest ->
      if FStar_List_Tot_Base.mem ns seen_ns
      then ts_user_used iris rest seen_ns
      else
        if ts_any_iri_uses_ns iris ns
        then (ns, label) :: (ts_user_used iris rest (ns :: seen_ns))
        else ts_user_used iris rest (ns :: seen_ns)
let well_known_prefixes : prefix_table=
  [("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#", "xsd:");
  ("http://www.w3.org/2002/07/owl#", "owl:");
  ("http://xmlns.com/foaf/0.1/", "foaf:");
  ("http://purl.org/dc/terms/", "dcterms:");
  ("http://purl.org/dc/elements/1.1/", "dc:");
  ("http://schema.org/", "schema:")]
let known_prefixes_used (present_namespaces : Prims.string Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  FStar_List_Tot_Base.filter
    (fun uu___ ->
       match uu___ with
       | (ns, uu___1) -> FStar_List_Tot_Base.mem ns present_namespaces)
    well_known_prefixes
let turtle_of_graph_opts (opts : turtle_render_options)
  (g : RDF_Graph.rdf_graph) : Prims.string=
  let iris = collect_iris_acc g [] in
  let candidates = candidate_namespaces_acc iris [] in
  let sorted_candidates =
    FStar_List_Tot_Base.sortWith FStar_String.compare candidates in
  let counted = count_runs sorted_candidates in
  let present_ns =
    FStar_List_Tot_Base.map FStar_Pervasives_Native.fst counted in
  let user_used = ts_user_used iris opts.tro_prefixes [] in
  let user_used_ns =
    FStar_List_Tot_Base.map FStar_Pervasives_Native.fst user_used in
  let user_used_labels =
    FStar_List_Tot_Base.map FStar_Pervasives_Native.snd user_used in
  let known0 = known_prefixes_used present_ns in
  let known =
    FStar_List_Tot_Base.filter
      (fun uu___ ->
         match uu___ with
         | (ns, label) ->
             (Prims.op_Negation (FStar_List_Tot_Base.mem ns user_used_ns)) &&
               (Prims.op_Negation
                  (FStar_List_Tot_Base.mem label user_used_labels))) known0 in
  let known_ns = FStar_List_Tot_Base.map FStar_Pervasives_Native.fst known in
  let known_labels =
    FStar_List_Tot_Base.map FStar_Pervasives_Native.snd known in
  let covered_ns = FStar_List_Tot_Base.op_At user_used_ns known_ns in
  let counted_by_freq =
    FStar_List_Tot_Base.sortWith count_desc_compare counted in
  let fresh =
    FStar_List_Tot_Base.filter
      (fun uu___ ->
         match uu___ with
         | (ns, uu___1) ->
             Prims.op_Negation (FStar_List_Tot_Base.mem ns covered_ns))
      counted_by_freq in
  let covered_len =
    (FStar_List_Tot_Base.length user_used) +
      (FStar_List_Tot_Base.length known) in
  let budget =
    if covered_len >= (Prims.of_int (8))
    then Prims.int_zero
    else (Prims.of_int (8)) - covered_len in
  let fresh_top = take_at_most budget fresh in
  let reserved_labels =
    FStar_List_Tot_Base.op_At user_used_labels known_labels in
  let auto = assign_labels_avoiding reserved_labels Prims.int_one fresh_top in
  let table =
    FStar_List_Tot_Base.op_At user_used
      (FStar_List_Tot_Base.op_At known auto) in
  turtle_of_graph table opts.tro_literal_shorthand g
let turtle_of_graph_auto (g : RDF_Graph.rdf_graph) : Prims.string=
  turtle_of_graph_opts turtle_render_defaults g
