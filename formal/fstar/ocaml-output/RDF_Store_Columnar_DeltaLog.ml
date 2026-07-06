open Prims
let delta_entry_magic : Prims.nat= (Prims.parse_int "0x31454C44")
let delta_entry_version : Prims.nat= Prims.int_one
let term_tag_iri : Prims.nat= Prims.int_zero
let term_tag_bnode : Prims.nat= Prims.int_one
let term_tag_literal : Prims.nat= (Prims.of_int (2))
let subj_tag_iri : Prims.nat= Prims.int_zero
let subj_tag_bnode : Prims.nat= Prims.int_one
let de_tag_add : Prims.nat= Prims.int_zero
let de_tag_remove : Prims.nat= Prims.int_one
let de_tag_clear : Prims.nat= (Prims.of_int (2))
let de_tag_drop : Prims.nat= (Prims.of_int (3))
let de_tag_create : Prims.nat= (Prims.of_int (4))
type delta_entry =
  | DE_Add of RDF_Triple.triple * RDF_Term.iri FStar_Pervasives_Native.option
  
  | DE_Remove of RDF_Triple.triple * RDF_Term.iri
  FStar_Pervasives_Native.option 
  | DE_Clear of RDF_Term.iri FStar_Pervasives_Native.option 
  | DE_Drop of RDF_Term.iri 
  | DE_Create of RDF_Term.iri 
let uu___is_DE_Add (projectee : delta_entry) : Prims.bool=
  match projectee with | DE_Add (quad, graph) -> true | uu___ -> false
let __proj__DE_Add__item__quad (projectee : delta_entry) : RDF_Triple.triple=
  match projectee with | DE_Add (quad, graph) -> quad
let __proj__DE_Add__item__graph (projectee : delta_entry) :
  RDF_Term.iri FStar_Pervasives_Native.option=
  match projectee with | DE_Add (quad, graph) -> graph
let uu___is_DE_Remove (projectee : delta_entry) : Prims.bool=
  match projectee with | DE_Remove (quad, graph) -> true | uu___ -> false
let __proj__DE_Remove__item__quad (projectee : delta_entry) :
  RDF_Triple.triple= match projectee with | DE_Remove (quad, graph) -> quad
let __proj__DE_Remove__item__graph (projectee : delta_entry) :
  RDF_Term.iri FStar_Pervasives_Native.option=
  match projectee with | DE_Remove (quad, graph) -> graph
let uu___is_DE_Clear (projectee : delta_entry) : Prims.bool=
  match projectee with | DE_Clear graph -> true | uu___ -> false
let __proj__DE_Clear__item__graph (projectee : delta_entry) :
  RDF_Term.iri FStar_Pervasives_Native.option=
  match projectee with | DE_Clear graph -> graph
let uu___is_DE_Drop (projectee : delta_entry) : Prims.bool=
  match projectee with | DE_Drop graph -> true | uu___ -> false
let __proj__DE_Drop__item__graph (projectee : delta_entry) : RDF_Term.iri=
  match projectee with | DE_Drop graph -> graph
let uu___is_DE_Create (projectee : delta_entry) : Prims.bool=
  match projectee with | DE_Create graph -> true | uu___ -> false
let __proj__DE_Create__item__graph (projectee : delta_entry) : RDF_Term.iri=
  match projectee with | DE_Create graph -> graph
let write_u8 (n : Prims.nat) : RDF_Bytes.bytes= [RDF_Bytes.byte_of_int n]
let parse_u8 (bs : RDF_Bytes.bytes) :
  (Prims.nat * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match bs with
  | b::rest -> FStar_Pervasives_Native.Some ((RDF_Bytes.int_of_byte b), rest)
  | [] -> FStar_Pervasives_Native.None
let serialize_lstring (s : Prims.string) : RDF_Bytes.bytes=
  let n = FStar_String.strlen s in
  if n >= (Prims.parse_int "4294967296")
  then []
  else
    FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le n)
      (RDF_Bytes.bytes_of_string s)
let parse_lstring (bs : RDF_Bytes.bytes) :
  (Prims.string * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (n, rest) ->
      RDF_Bytes.parse_string_of_length n rest
let serialize_term (t : RDF_Term.rdf_term) : RDF_Bytes.bytes=
  match t with
  | RDF_Term.T_IRI i ->
      FStar_List_Tot_Base.append (write_u8 term_tag_iri)
        (serialize_lstring i)
  | RDF_Term.T_BNode b ->
      FStar_List_Tot_Base.append (write_u8 term_tag_bnode)
        (serialize_lstring b)
  | RDF_Term.T_Literal l ->
      FStar_List_Tot_Base.append (write_u8 term_tag_literal)
        (FStar_List_Tot_Base.append
           (serialize_lstring l.RDF_Term.lexical_form)
           (FStar_List_Tot_Base.append
              (serialize_lstring l.RDF_Term.datatype)
              (match l.RDF_Term.lang_tag with
               | FStar_Pervasives_Native.None -> write_u8 Prims.int_zero
               | FStar_Pervasives_Native.Some tag ->
                   FStar_List_Tot_Base.append (write_u8 Prims.int_one)
                     (serialize_lstring tag))))
let parse_term (bs : RDF_Bytes.bytes) :
  (RDF_Term.rdf_term * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match parse_u8 bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (tag, after_tag) ->
      if tag = term_tag_iri
      then
        (match parse_lstring after_tag with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (i, rest) ->
             if RDF_Term.is_iri i
             then FStar_Pervasives_Native.Some ((RDF_Term.T_IRI i), rest)
             else FStar_Pervasives_Native.None)
      else
        if tag = term_tag_bnode
        then
          (match parse_lstring after_tag with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (b, rest) ->
               FStar_Pervasives_Native.Some ((RDF_Term.T_BNode b), rest))
        else
          if tag = term_tag_literal
          then
            (match parse_lstring after_tag with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (lex, after_lex) ->
                 (match parse_lstring after_lex with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (dt, after_dt) ->
                      if Prims.op_Negation (RDF_Term.is_iri dt)
                      then FStar_Pervasives_Native.None
                      else
                        (match parse_u8 after_dt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some (flag, after_flag) ->
                             if flag = Prims.int_zero
                             then
                               let l =
                                 {
                                   RDF_Term.lexical_form = lex;
                                   RDF_Term.datatype = dt;
                                   RDF_Term.lang_tag =
                                     FStar_Pervasives_Native.None
                                 } in
                               (if RDF_Term.literal_wf l
                                then
                                  FStar_Pervasives_Native.Some
                                    ((RDF_Term.T_Literal l), after_flag)
                                else FStar_Pervasives_Native.None)
                             else
                               if flag = Prims.int_one
                               then
                                 (match parse_lstring after_flag with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some
                                      (tag_str, rest) ->
                                      let l =
                                        {
                                          RDF_Term.lexical_form = lex;
                                          RDF_Term.datatype = dt;
                                          RDF_Term.lang_tag =
                                            (FStar_Pervasives_Native.Some
                                               tag_str)
                                        } in
                                      if RDF_Term.literal_wf l
                                      then
                                        FStar_Pervasives_Native.Some
                                          ((RDF_Term.T_Literal l), rest)
                                      else FStar_Pervasives_Native.None)
                               else FStar_Pervasives_Native.None)))
          else FStar_Pervasives_Native.None
let serialize_subject (s : RDF_Term.subject) : RDF_Bytes.bytes=
  match s with
  | RDF_Term.S_IRI i ->
      FStar_List_Tot_Base.append (write_u8 subj_tag_iri)
        (serialize_lstring i)
  | RDF_Term.S_BNode b ->
      FStar_List_Tot_Base.append (write_u8 subj_tag_bnode)
        (serialize_lstring b)
let parse_subject (bs : RDF_Bytes.bytes) :
  (RDF_Term.subject * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match parse_u8 bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (tag, after_tag) ->
      if tag = subj_tag_iri
      then
        (match parse_lstring after_tag with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (i, rest) ->
             if RDF_Term.is_iri i
             then FStar_Pervasives_Native.Some ((RDF_Term.S_IRI i), rest)
             else FStar_Pervasives_Native.None)
      else
        if tag = subj_tag_bnode
        then
          (match parse_lstring after_tag with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (b, rest) ->
               FStar_Pervasives_Native.Some ((RDF_Term.S_BNode b), rest))
        else FStar_Pervasives_Native.None
let serialize_triple (tr : RDF_Triple.triple) : RDF_Bytes.bytes=
  FStar_List_Tot_Base.append (serialize_subject tr.RDF_Triple.s)
    (FStar_List_Tot_Base.append (serialize_lstring tr.RDF_Triple.p)
       (serialize_term tr.RDF_Triple.o))
let parse_triple (bs : RDF_Bytes.bytes) :
  (RDF_Triple.triple * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match parse_subject bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (s, after_s) ->
      (match parse_lstring after_s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (p, after_p) ->
           if Prims.op_Negation (RDF_Term.is_iri p)
           then FStar_Pervasives_Native.None
           else
             (match parse_term after_p with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (o, rest) ->
                  FStar_Pervasives_Native.Some
                    ({ RDF_Triple.s = s; RDF_Triple.p = p; RDF_Triple.o = o },
                      rest)))
let serialize_graph_opt (g : RDF_Term.iri FStar_Pervasives_Native.option) :
  RDF_Bytes.bytes=
  match g with
  | FStar_Pervasives_Native.None -> write_u8 Prims.int_zero
  | FStar_Pervasives_Native.Some i ->
      FStar_List_Tot_Base.append (write_u8 Prims.int_one)
        (serialize_lstring i)
let parse_graph_opt (bs : RDF_Bytes.bytes) :
  (RDF_Term.iri FStar_Pervasives_Native.option * RDF_Bytes.bytes)
    FStar_Pervasives_Native.option=
  match parse_u8 bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (uu___, rest) when uu___ = Prims.int_zero ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None, rest)
  | FStar_Pervasives_Native.Some (uu___, after) when uu___ = Prims.int_one ->
      (match parse_lstring after with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (i, rest) ->
           FStar_Pervasives_Native.Some
             ((FStar_Pervasives_Native.Some i), rest))
  | FStar_Pervasives_Native.Some (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let serialize_delta_entry_payload (e : delta_entry) : RDF_Bytes.bytes=
  match e with
  | DE_Add (q, g) ->
      FStar_List_Tot_Base.append (write_u8 de_tag_add)
        (FStar_List_Tot_Base.append (serialize_triple q)
           (serialize_graph_opt g))
  | DE_Remove (q, g) ->
      FStar_List_Tot_Base.append (write_u8 de_tag_remove)
        (FStar_List_Tot_Base.append (serialize_triple q)
           (serialize_graph_opt g))
  | DE_Clear g ->
      FStar_List_Tot_Base.append (write_u8 de_tag_clear)
        (serialize_graph_opt g)
  | DE_Drop g ->
      FStar_List_Tot_Base.append (write_u8 de_tag_drop) (serialize_lstring g)
  | DE_Create g ->
      FStar_List_Tot_Base.append (write_u8 de_tag_create)
        (serialize_lstring g)
let parse_delta_entry_payload (bs : RDF_Bytes.bytes) :
  (delta_entry * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match parse_u8 bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (tag, after_tag) ->
      if tag = de_tag_add
      then
        (match parse_triple after_tag with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (q, after_q) ->
             (match parse_graph_opt after_q with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (g, rest) ->
                  FStar_Pervasives_Native.Some ((DE_Add (q, g)), rest)))
      else
        if tag = de_tag_remove
        then
          (match parse_triple after_tag with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (q, after_q) ->
               (match parse_graph_opt after_q with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (g, rest) ->
                    FStar_Pervasives_Native.Some ((DE_Remove (q, g)), rest)))
        else
          if tag = de_tag_clear
          then
            (match parse_graph_opt after_tag with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (g, rest) ->
                 FStar_Pervasives_Native.Some ((DE_Clear g), rest))
          else
            if tag = de_tag_drop
            then
              (match parse_lstring after_tag with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (g, rest) ->
                   FStar_Pervasives_Native.Some ((DE_Drop g), rest))
            else
              if tag = de_tag_create
              then
                (match parse_lstring after_tag with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (g, rest) ->
                     FStar_Pervasives_Native.Some ((DE_Create g), rest))
              else FStar_Pervasives_Native.None
let rec simple_checksum_acc (acc : Prims.nat) (bs : RDF_Bytes.bytes) :
  Prims.nat=
  match bs with
  | [] -> (mod) acc (Prims.parse_int "4294967296")
  | b::rest ->
      simple_checksum_acc
        ((mod) (acc + (RDF_Bytes.int_of_byte b))
           (Prims.parse_int "4294967296")) rest
let simple_checksum (bs : RDF_Bytes.bytes) : Prims.nat=
  simple_checksum_acc Prims.int_zero bs
let serialize_delta_entry (e : delta_entry) : RDF_Bytes.bytes=
  let payload = serialize_delta_entry_payload e in
  let len = FStar_List_Tot_Base.length payload in
  if len >= (Prims.parse_int "4294967296")
  then []
  else
    FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le delta_entry_magic)
      (FStar_List_Tot_Base.append
         (RDF_Bytes.write_u32_le delta_entry_version)
         (FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le len)
            (FStar_List_Tot_Base.append payload
               (RDF_Bytes.write_u32_le (simple_checksum payload)))))
let parse_delta_entry (bs : RDF_Bytes.bytes) :
  (delta_entry * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (magic, after_magic) ->
      if magic <> delta_entry_magic
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (ver, after_ver) ->
             if ver <> delta_entry_version
             then FStar_Pervasives_Native.None
             else
               (match RDF_Bytes.parse_u32_le after_ver with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (len, after_len) ->
                    (match RDF_Bytes.parse_n_bytes len after_len with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (payload, after_payload)
                         ->
                         (match RDF_Bytes.parse_u32_le after_payload with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (chk, rest) ->
                              if chk <> (simple_checksum payload)
                              then FStar_Pervasives_Native.None
                              else
                                (match parse_delta_entry_payload payload with
                                 | FStar_Pervasives_Native.Some (e, []) ->
                                     FStar_Pervasives_Native.Some (e, rest)
                                 | uu___3 -> FStar_Pervasives_Native.None)))))
let max_field_chars : Prims.nat= (Prims.parse_int "268435456")
let term_ok (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_IRI i -> (FStar_String.strlen i) < max_field_chars
  | RDF_Term.T_BNode b -> (FStar_String.strlen b) < max_field_chars
  | RDF_Term.T_Literal l ->
      (((FStar_String.strlen l.RDF_Term.lexical_form) < max_field_chars) &&
         ((FStar_String.strlen l.RDF_Term.datatype) < max_field_chars))
        &&
        ((match l.RDF_Term.lang_tag with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some tg ->
              (FStar_String.strlen tg) < max_field_chars))
let subject_ok (s : RDF_Term.subject) : Prims.bool=
  match s with
  | RDF_Term.S_IRI i -> (FStar_String.strlen i) < max_field_chars
  | RDF_Term.S_BNode b -> (FStar_String.strlen b) < max_field_chars
let triple_ok (tr : RDF_Triple.triple) : Prims.bool=
  ((subject_ok tr.RDF_Triple.s) &&
     ((FStar_String.strlen tr.RDF_Triple.p) < max_field_chars))
    && (term_ok tr.RDF_Triple.o)
let graph_opt_ok (g : RDF_Term.iri FStar_Pervasives_Native.option) :
  Prims.bool=
  match g with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some i ->
      (FStar_String.strlen i) < max_field_chars
let delta_entry_ok (e : delta_entry) : Prims.bool=
  match e with
  | DE_Add (q, g) -> (triple_ok q) && (graph_opt_ok g)
  | DE_Remove (q, g) -> (triple_ok q) && (graph_opt_ok g)
  | DE_Clear g -> graph_opt_ok g
  | DE_Drop g -> (FStar_String.strlen g) < max_field_chars
  | DE_Create g -> (FStar_String.strlen g) < max_field_chars
let delta_entry_frame_ok (e : delta_entry) : Prims.bool=
  (FStar_List_Tot_Base.length (serialize_delta_entry_payload e)) <
    (Prims.parse_int "4294967296")
type delta_batch =
  {
  db_seq: Prims.nat ;
  db_epoch: Prims.nat ;
  db_ops: delta_entry Prims.list }
let __proj__Mkdelta_batch__item__db_seq (projectee : delta_batch) :
  Prims.nat= match projectee with | { db_seq; db_epoch; db_ops;_} -> db_seq
let __proj__Mkdelta_batch__item__db_epoch (projectee : delta_batch) :
  Prims.nat= match projectee with | { db_seq; db_epoch; db_ops;_} -> db_epoch
let __proj__Mkdelta_batch__item__db_ops (projectee : delta_batch) :
  delta_entry Prims.list=
  match projectee with | { db_seq; db_epoch; db_ops;_} -> db_ops
let delta_batch_magic : Prims.nat= (Prims.parse_int "0x31424C44")
let delta_batch_version : Prims.nat= Prims.int_one
let rec serialize_ops (ops : delta_entry Prims.list) : RDF_Bytes.bytes=
  match ops with
  | [] -> []
  | e::rest ->
      FStar_List_Tot_Base.append (serialize_delta_entry e)
        (serialize_ops rest)
let rec parse_n_delta_entries (n : Prims.nat) (bs : RDF_Bytes.bytes) :
  (delta_entry Prims.list * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  if n = Prims.int_zero
  then FStar_Pervasives_Native.Some ([], bs)
  else
    (match parse_delta_entry bs with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (e, rest) ->
         (match parse_n_delta_entries (n - Prims.int_one) rest with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (es, rest2) ->
              FStar_Pervasives_Native.Some ((e :: es), rest2)))
let rec delta_batch_ops_ok (ops : delta_entry Prims.list) : Prims.bool=
  match ops with
  | [] -> true
  | e::rest -> (delta_entry_ok e) && (delta_batch_ops_ok rest)
let u64_max_nat : Prims.nat= (Prims.parse_int "18446744073709551615")
let delta_batch_ok (b : delta_batch) : Prims.bool=
  ((((b.db_seq <= u64_max_nat) && (b.db_epoch <= u64_max_nat)) &&
      ((FStar_List_Tot_Base.length b.db_ops) < (Prims.parse_int "4294967296")))
     && (delta_batch_ops_ok b.db_ops))
    &&
    ((FStar_List_Tot_Base.length (serialize_ops b.db_ops)) <
       (Prims.parse_int "4294967276"))
let serialize_delta_batch_body (b : delta_batch) : RDF_Bytes.bytes=
  if
    ((b.db_seq > u64_max_nat) || (b.db_epoch > u64_max_nat)) ||
      ((FStar_List_Tot_Base.length b.db_ops) >=
         (Prims.parse_int "4294967296"))
  then []
  else
    FStar_List_Tot_Base.append (RDF_Bytes.write_u64_le b.db_seq)
      (FStar_List_Tot_Base.append (RDF_Bytes.write_u64_le b.db_epoch)
         (FStar_List_Tot_Base.append
            (RDF_Bytes.write_u32_le (FStar_List_Tot_Base.length b.db_ops))
            (serialize_ops b.db_ops)))
let parse_delta_batch_body (bs : RDF_Bytes.bytes) :
  (delta_batch * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u64_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (sq, after_seq) ->
      (match RDF_Bytes.parse_u64_le after_seq with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (ep, after_epoch) ->
           (match RDF_Bytes.parse_u32_le after_epoch with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (n, after_n) ->
                (match parse_n_delta_entries n after_n with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (ops, rest) ->
                     FStar_Pervasives_Native.Some
                       ({ db_seq = sq; db_epoch = ep; db_ops = ops }, rest))))
let serialize_delta_batch (b : delta_batch) : RDF_Bytes.bytes=
  let body = serialize_delta_batch_body b in
  let len = FStar_List_Tot_Base.length body in
  if len >= (Prims.parse_int "4294967296")
  then []
  else
    FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le delta_batch_magic)
      (FStar_List_Tot_Base.append
         (RDF_Bytes.write_u32_le delta_batch_version)
         (FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le len)
            (FStar_List_Tot_Base.append body
               (RDF_Bytes.write_u32_le (simple_checksum body)))))
let parse_delta_batch (bs : RDF_Bytes.bytes) :
  (delta_batch * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (magic, after_magic) ->
      if magic <> delta_batch_magic
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (ver, after_ver) ->
             if ver <> delta_batch_version
             then FStar_Pervasives_Native.None
             else
               (match RDF_Bytes.parse_u32_le after_ver with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (len, after_len) ->
                    (match RDF_Bytes.parse_n_bytes len after_len with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (body, after_body) ->
                         (match RDF_Bytes.parse_u32_le after_body with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (chk, rest) ->
                              if chk <> (simple_checksum body)
                              then FStar_Pervasives_Native.None
                              else
                                (match parse_delta_batch_body body with
                                 | FStar_Pervasives_Native.Some (b, []) ->
                                     FStar_Pervasives_Native.Some (b, rest)
                                 | uu___3 -> FStar_Pervasives_Native.None)))))
let delta_log_magic : Prims.nat= (Prims.parse_int "0x474F4C44")
let delta_log_version : Prims.nat= Prims.int_one
let serialize_log_header : RDF_Bytes.bytes=
  FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le delta_log_magic)
    (RDF_Bytes.write_u32_le delta_log_version)
let parse_log_header (bs : RDF_Bytes.bytes) :
  RDF_Bytes.bytes FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (magic, after_magic) ->
      if magic <> delta_log_magic
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (ver, rest) ->
             if ver <> delta_log_version
             then FStar_Pervasives_Native.None
             else FStar_Pervasives_Native.Some rest)
let rec parse_log_batches (bs : RDF_Bytes.bytes) :
  (delta_batch Prims.list * RDF_Bytes.bytes)=
  match parse_delta_batch bs with
  | FStar_Pervasives_Native.None -> ([], bs)
  | FStar_Pervasives_Native.Some (b, rest) ->
      let uu___ = parse_log_batches rest in
      (match uu___ with | (more, tail) -> ((b :: more), tail))
let rec serialize_delta_batches (bs : delta_batch Prims.list) :
  RDF_Bytes.bytes=
  match bs with
  | [] -> []
  | b::rest ->
      FStar_List_Tot_Base.append (serialize_delta_batch b)
        (serialize_delta_batches rest)
let rec delta_batches_ok (bs : delta_batch Prims.list) : Prims.bool=
  match bs with
  | [] -> true
  | b::rest -> (delta_batch_ok b) && (delta_batches_ok rest)
let serialize_log (bs : delta_batch Prims.list) : RDF_Bytes.bytes=
  FStar_List_Tot_Base.append serialize_log_header
    (serialize_delta_batches bs)
let parse_log (bs : RDF_Bytes.bytes) :
  (delta_batch Prims.list * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match parse_log_header bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rest ->
      FStar_Pervasives_Native.Some (parse_log_batches rest)
let expected_digest_bytes (b : delta_batch) : RDF_Bytes.bytes=
  serialize_delta_batch b
(* __delta_log_io_realised (issue #NNN) *)
(* rule #11(a) pure-I/O realisation. O_APPEND writes below the
   filesystem block size are atomic per POSIX -- a crash mid-append
   leaves a torn TAIL entry, never corrupts already-committed bytes
   earlier in the file (design doc §3.3 step 2). The caller (the
   commit sequence, or the crash-harness driver deliberately
   slicing one batch into several small appends to widen a kill
   window) decides how many times to call this per batch; each
   call is independently a plain append. *)
let delta_log_append (path : Prims.string) (bytes : RDF_Bytes.bytes) :
  unit=
  let s = RDF_Bytes.bytes_to_string bytes in
  let fd =
    Unix.openfile path [Unix.O_APPEND; Unix.O_CREAT; Unix.O_WRONLY] 0o644 in
  Fun.protect ~finally:(fun () -> Unix.close fd)
    (fun () ->
       (* this file has a top-level `open Prims` (F* extraction
          convention) that shadows `(<)`/`(+)`/`(-)` to operate over
          Prims.int = Z.t; qualify with plain OCaml Stdlib for the
          native-int write-loop bookkeeping, same pattern as
          experimental_ocaml_glue/parquet_footer_runtime.sh. *)
       let module S = Stdlib in
       let n = String.length s in
       let written = ref 0 in
       while S.(!written < n) do
         let k = Unix.write_substring fd s !written S.(n - !written) in
         written := S.(!written + k)
       done)
(* rule #11(a): the commit point (design doc §3.3 step 3) -- before
   this returns, nothing appended since the last fsync is durable.
   Reopen read-write (not O_APPEND -- fsync just needs a valid fd on
   the path, it does not write) since delta_log_append already
   closed its own fd. *)
let delta_log_fsync (path : Prims.string) : unit=
  let fd = Unix.openfile path [Unix.O_WRONLY] 0o644 in
  Fun.protect ~finally:(fun () -> Unix.close fd) (fun () -> Unix.fsync fd)
(* rule #11(a): whole-file read, no interpretation -- parse_log
   (F*, Tot) decides what the bytes mean, including tolerating a
   torn tail batch (design doc §3.3's crash-recovery replay). *)
let delta_log_read_all (path : Prims.string) : RDF_Bytes.bytes=
  let fd = Unix.openfile path [Unix.O_RDONLY] 0o644 in
  Fun.protect ~finally:(fun () -> Unix.close fd)
    (fun () ->
       (* see delta_log_append -- same open-Prims arithmetic-shadow
          trap, same Stdlib qualification fix. *)
       let module S = Stdlib in
       let len = (Unix.fstat fd).Unix.st_size in
       let buf = Bytes.create len in
       let read_total = ref 0 in
       while S.(!read_total < len) do
         let k = Unix.read fd buf !read_total S.(len - !read_total) in
         if k = 0 then read_total := len (* EOF: file shrank under us *)
         else read_total := S.(!read_total + k)
       done;
       RDF_Bytes.bytes_of_string (Bytes.sub_string buf 0 !read_total))
(* rule #11(a): POSIX rename(2) within one directory is atomic --
   design doc §3.3 step 5's base-file swap relies on exactly this
   property. Callers still owe a subsequent fsync_dir for the
   rename itself to be durable across a crash. *)
let atomic_rename (from_path : Prims.string) (to_path : Prims.string) :
  unit=
  Unix.rename from_path to_path
(* rule #11(a): a directory can be opened read-only and fsynced on
   POSIX (Linux, most *BSDs) to force its entry-table changes
   (a rename's new/removed name) to durable storage -- design doc
   §3.3 step 5's "every WAL implementation gets bitten by if
   skipped" detail. *)
let fsync_dir (path : Prims.string) : unit=
  let fd = Unix.openfile path [Unix.O_RDONLY] 0o644 in
  Fun.protect ~finally:(fun () -> Unix.close fd) (fun () -> Unix.fsync fd)
let compacted_epoch_magic : Prims.nat= (Prims.parse_int "0x31504543")
let compacted_epoch_version : Prims.nat= Prims.int_one
let serialize_compacted_epoch (n : Prims.nat) : RDF_Bytes.bytes=
  let body = RDF_Bytes.write_u64_le n in
  let len = FStar_List_Tot_Base.length body in
  FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le compacted_epoch_magic)
    (FStar_List_Tot_Base.append
       (RDF_Bytes.write_u32_le compacted_epoch_version)
       (FStar_List_Tot_Base.append (RDF_Bytes.write_u32_le len)
          (FStar_List_Tot_Base.append body
             (RDF_Bytes.write_u32_le (simple_checksum body)))))
let parse_compacted_epoch (bs : RDF_Bytes.bytes) :
  Prims.nat FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (magic, after_magic) ->
      if magic <> compacted_epoch_magic
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (ver, after_ver) ->
             if ver <> compacted_epoch_version
             then FStar_Pervasives_Native.None
             else
               (match RDF_Bytes.parse_u32_le after_ver with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (len, after_len) ->
                    (match RDF_Bytes.parse_n_bytes len after_len with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (body, after_body) ->
                         (match RDF_Bytes.parse_u32_le after_body with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (chk, _rest) ->
                              if chk <> (simple_checksum body)
                              then FStar_Pervasives_Native.None
                              else
                                (match RDF_Bytes.parse_u64_le body with
                                 | FStar_Pervasives_Native.Some (n, []) ->
                                     FStar_Pervasives_Native.Some n
                                 | uu___3 -> FStar_Pervasives_Native.None)))))
let rec filter_batches_since_epoch
  (threshold : Prims.nat FStar_Pervasives_Native.option)
  (batches : delta_batch Prims.list) : delta_batch Prims.list=
  match batches with
  | [] -> []
  | b::rest ->
      let keep =
        match threshold with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some ce -> b.db_epoch > ce in
      if keep
      then b :: (filter_batches_since_epoch threshold rest)
      else filter_batches_since_epoch threshold rest
