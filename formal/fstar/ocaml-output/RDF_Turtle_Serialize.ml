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
let ts_term_to_turtle (table : prefix_table)
  (t : RDF_Graph_Executable.rdf_term) : Prims.string=
  match t with
  | RDF_Graph_Executable.T_IRI i -> ts_abbreviate_iri table i
  | RDF_Graph_Executable.T_BNode b -> Prims.strcat "_:" b
  | RDF_Graph_Executable.T_Literal l ->
      let esc =
        RDF_NQuads_Serialize.nq_escape_literal
          l.RDF_Graph_Executable.lexical_form in
      (match l.RDF_Graph_Executable.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           Prims.strcat "\"" (Prims.strcat esc (Prims.strcat "\"@" tag))
       | FStar_Pervasives_Native.None ->
           if
             l.RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.xsd_string
           then Prims.strcat "\"" (Prims.strcat esc "\"")
           else
             Prims.strcat "\""
               (Prims.strcat esc
                  (Prims.strcat "\"^^"
                     (ts_abbreviate_iri table l.RDF_Graph_Executable.datatype))))
let ts_subject_to_turtle (table : prefix_table)
  (s : RDF_Graph_Executable.subject) : Prims.string=
  match s with
  | RDF_Graph_Executable.S_IRI i -> ts_abbreviate_iri table i
  | RDF_Graph_Executable.S_BNode b -> Prims.strcat "_:" b
let ts_predicate_to_turtle (table : prefix_table)
  (p : RDF_Graph_Executable.wf_iri) : Prims.string=
  if p = RDF_Graph_Executable.rdf_type
  then "a"
  else ts_abbreviate_iri table p
type subj_state =
  {
  ss_subj: RDF_Graph_Executable.subject ;
  ss_subj_text: Prims.string ;
  ss_cur_pred: RDF_Graph_Executable.wf_iri ;
  ss_cur_pred_text: Prims.string ;
  ss_cur_objs: Prims.string Prims.list ;
  ss_pred_chunks: Prims.string Prims.list }
let __proj__Mksubj_state__item__ss_subj (projectee : subj_state) :
  RDF_Graph_Executable.subject=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_subj
let __proj__Mksubj_state__item__ss_subj_text (projectee : subj_state) :
  Prims.string=
  match projectee with
  | { ss_subj; ss_subj_text; ss_cur_pred; ss_cur_pred_text; ss_cur_objs;
      ss_pred_chunks;_} -> ss_subj_text
let __proj__Mksubj_state__item__ss_cur_pred (projectee : subj_state) :
  RDF_Graph_Executable.wf_iri=
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
let rec walk_triples (table : prefix_table)
  (sorted : RDF_Graph_Executable.rdf_graph)
  (st : subj_state FStar_Pervasives_Native.option)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match sorted with
  | [] ->
      (match st with
       | FStar_Pervasives_Native.None -> acc
       | FStar_Pervasives_Native.Some s -> (finish_subj s) :: acc)
  | t::rest ->
      let obj_text = ts_term_to_turtle table t.RDF_Graph_Executable.o in
      (match st with
       | FStar_Pervasives_Native.None ->
           let st' =
             {
               ss_subj = (t.RDF_Graph_Executable.s);
               ss_subj_text =
                 (ts_subject_to_turtle table t.RDF_Graph_Executable.s);
               ss_cur_pred = (t.RDF_Graph_Executable.p);
               ss_cur_pred_text =
                 (ts_predicate_to_turtle table t.RDF_Graph_Executable.p);
               ss_cur_objs = [obj_text];
               ss_pred_chunks = []
             } in
           walk_triples table rest (FStar_Pervasives_Native.Some st') acc
       | FStar_Pervasives_Native.Some s ->
           if
             RDF_Graph_Executable.subject_eq s.ss_subj
               t.RDF_Graph_Executable.s
           then
             (if s.ss_cur_pred = t.RDF_Graph_Executable.p
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
                walk_triples table rest (FStar_Pervasives_Native.Some s') acc
              else
                (let pred_chunks' = finish_pred s in
                 let s' =
                   {
                     ss_subj = (s.ss_subj);
                     ss_subj_text = (s.ss_subj_text);
                     ss_cur_pred = (t.RDF_Graph_Executable.p);
                     ss_cur_pred_text =
                       (ts_predicate_to_turtle table t.RDF_Graph_Executable.p);
                     ss_cur_objs = [obj_text];
                     ss_pred_chunks = pred_chunks'
                   } in
                 walk_triples table rest (FStar_Pervasives_Native.Some s')
                   acc))
           else
             (let block = finish_subj s in
              let st' =
                {
                  ss_subj = (t.RDF_Graph_Executable.s);
                  ss_subj_text =
                    (ts_subject_to_turtle table t.RDF_Graph_Executable.s);
                  ss_cur_pred = (t.RDF_Graph_Executable.p);
                  ss_cur_pred_text =
                    (ts_predicate_to_turtle table t.RDF_Graph_Executable.p);
                  ss_cur_objs = [obj_text];
                  ss_pred_chunks = []
                } in
              walk_triples table rest (FStar_Pervasives_Native.Some st')
                (block :: acc)))
let render_triples (table : prefix_table)
  (g : RDF_Graph_Executable.rdf_graph) : Prims.string=
  let sorted = FStar_List_Tot_Base.sortWith RDF_Graph_Executable.triple_cmp g in
  let blocks = walk_triples table sorted FStar_Pervasives_Native.None [] in
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
  (g : RDF_Graph_Executable.rdf_graph) : Prims.string=
  let header_lines = render_prefix_header table in
  let header = FStar_String.concat "" header_lines in
  let sep = match header_lines with | [] -> "" | uu___ -> "\n" in
  let body = render_triples table g in
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
let rec collect_iris_acc (g : RDF_Graph_Executable.rdf_graph)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match g with
  | [] -> acc
  | t::rest ->
      let acc1 = (t.RDF_Graph_Executable.p) :: acc in
      let acc2 =
        match t.RDF_Graph_Executable.s with
        | RDF_Graph_Executable.S_IRI i -> i :: acc1
        | RDF_Graph_Executable.S_BNode uu___ -> acc1 in
      let acc3 =
        match t.RDF_Graph_Executable.o with
        | RDF_Graph_Executable.T_IRI i -> i :: acc2
        | RDF_Graph_Executable.T_BNode uu___ -> acc2
        | RDF_Graph_Executable.T_Literal l ->
            (match l.RDF_Graph_Executable.lang_tag with
             | FStar_Pervasives_Native.Some uu___ -> acc2
             | FStar_Pervasives_Native.None ->
                 if
                   l.RDF_Graph_Executable.datatype =
                     RDF_Graph_Executable.xsd_string
                 then acc2
                 else (l.RDF_Graph_Executable.datatype) :: acc2) in
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
let rec assign_labels (idx : Prims.nat)
  (namespaces : (Prims.string * Prims.nat) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match namespaces with
  | [] -> []
  | (ns, uu___)::rest ->
      if idx < (Prims.of_int (9))
      then (ns, (Prims.strcat "ns" (Prims.strcat (digit_char idx) ":"))) ::
        (assign_labels (idx + Prims.int_one) rest)
      else []
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
let turtle_of_graph_auto (g : RDF_Graph_Executable.rdf_graph) : Prims.string=
  let iris = collect_iris_acc g [] in
  let candidates = candidate_namespaces_acc iris [] in
  let sorted_candidates =
    FStar_List_Tot_Base.sortWith FStar_String.compare candidates in
  let counted = count_runs sorted_candidates in
  let present_ns =
    FStar_List_Tot_Base.map FStar_Pervasives_Native.fst counted in
  let known = known_prefixes_used present_ns in
  let known_ns = FStar_List_Tot_Base.map FStar_Pervasives_Native.fst known in
  let counted_by_freq =
    FStar_List_Tot_Base.sortWith count_desc_compare counted in
  let fresh =
    FStar_List_Tot_Base.filter
      (fun uu___ ->
         match uu___ with
         | (ns, uu___1) ->
             Prims.op_Negation (FStar_List_Tot_Base.mem ns known_ns))
      counted_by_freq in
  let known_len = FStar_List_Tot_Base.length known in
  let budget =
    if known_len >= (Prims.of_int (8))
    then Prims.int_zero
    else (Prims.of_int (8)) - known_len in
  let rec take_at_most n l =
    if n = Prims.int_zero
    then []
    else
      (match l with
       | [] -> []
       | hd::tl -> hd :: (take_at_most (n - Prims.int_one) tl)) in
  let fresh_top = take_at_most budget fresh in
  let auto = assign_labels Prims.int_one fresh_top in
  let table = FStar_List_Tot_Base.op_At known auto in turtle_of_graph table g
