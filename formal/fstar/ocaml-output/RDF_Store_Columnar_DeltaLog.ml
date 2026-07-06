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
let payload_len_bound : Prims.nat=
  (Prims.of_int (10)) * (max_field_chars + (Prims.of_int (10)))
let delta_entry_frame_ok (e : delta_entry) : Prims.bool=
  (FStar_List_Tot_Base.length (serialize_delta_entry_payload e)) <
    (Prims.parse_int "4294967296")
