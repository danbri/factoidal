open Prims
let rdf_type_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_first_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let jld_fresh_bnode (ctr : Prims.nat) :
  (RDF_Graph_Executable.bnode_id * Prims.nat)=
  ((FStar_String.concat "" ["_jld_anon"; Prims.string_of_int ctr]),
    (ctr + Prims.int_one))
let jld_is_bnode_label (s : Prims.string) : Prims.bool=
  ((Parser_JSON.jbyte_at s Prims.int_zero) = (Prims.of_int (0x5F))) &&
    ((Parser_JSON.jbyte_at s Prims.int_one) = (Prims.of_int (0x3A)))
let jld_strip_bnode_prefix (s : Prims.string) : Prims.string=
  let n = Parser_FastString.fs_byte_length s in
  if n >= (Prims.of_int (2))
  then
    Parser_FastString.fs_byte_sub s (Prims.of_int (2))
      (n - (Prims.of_int (2)))
  else s
let jld_id_to_subject (s : Prims.string) :
  RDF_Graph_Executable.subject FStar_Pervasives_Native.option=
  if jld_is_bnode_label s
  then
    FStar_Pervasives_Native.Some
      (RDF_Graph_Executable.S_BNode (jld_strip_bnode_prefix s))
  else
    if RDF_Graph_Executable.is_iri s
    then FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_IRI s)
    else FStar_Pervasives_Native.None
let jld_is_keyword (k : Prims.string) : Prims.bool=
  (Parser_JSON.jbyte_at k Prims.int_zero) = (Prims.of_int (0x40))
let jld_as_array (v : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list=
  match v with | Parser_JSON.JArray items -> items | uu___ -> [v]
let rec jld_scan_double_marker (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let b = Parser_JSON.jbyte_at s pos in
     if b < Prims.int_zero
     then false
     else
       if
         ((b = (Prims.of_int (0x2E))) || (b = (Prims.of_int (0x65)))) ||
           (b = (Prims.of_int (0x45)))
       then true
       else
         jld_scan_double_marker s (pos + Prims.int_one)
           (fuel - Prims.int_one))
let jld_number_is_double (s : Prims.string) : Prims.bool=
  jld_scan_double_marker s Prims.int_zero
    ((Parser_FastString.fs_byte_length s) + Prims.int_one)
let jld_make_literal (lexical : Prims.string) (dt : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri dt
  then
    let lit =
      {
        RDF_Graph_Executable.lexical_form = lexical;
        RDF_Graph_Executable.datatype = dt;
        RDF_Graph_Executable.lang_tag = lang
      } in
    (if RDF_Graph_Executable.literal_wf lit
     then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal lit)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let jld_scalar_to_term (v : Parser_JSON.json_val) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString str ->
      jld_make_literal str RDF_Graph_Executable.xsd_string
        FStar_Pervasives_Native.None
  | Parser_JSON.JBool b ->
      jld_make_literal (if b then "true" else "false")
        RDF_Graph_Executable.xsd_boolean FStar_Pervasives_Native.None
  | Parser_JSON.JNumber n ->
      if jld_number_is_double n
      then
        jld_make_literal n RDF_Graph_Executable.xsd_double
          FStar_Pervasives_Native.None
      else
        jld_make_literal n RDF_Graph_Executable.xsd_integer
          FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let jld_value_object_to_term (obj : Parser_JSON.json_val) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field "@value" obj with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v ->
      let lang = Parser_JSON.json_get_string "@language" obj in
      let dt = Parser_JSON.json_get_string "@type" obj in
      (match (lang, dt) with
       | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
          uu___1) -> FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.Some lg, FStar_Pervasives_Native.None) ->
           (match v with
            | Parser_JSON.JString s ->
                jld_make_literal s RDF_Graph_Executable.rdf_lang_string
                  (FStar_Pervasives_Native.Some lg)
            | uu___ -> FStar_Pervasives_Native.None)
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some d) ->
           (match v with
            | Parser_JSON.JString s ->
                jld_make_literal s d FStar_Pervasives_Native.None
            | Parser_JSON.JBool b ->
                jld_make_literal (if b then "true" else "false") d
                  FStar_Pervasives_Native.None
            | Parser_JSON.JNumber n ->
                jld_make_literal n d FStar_Pervasives_Native.None
            | uu___ -> FStar_Pervasives_Native.None)
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
           jld_scalar_to_term v)
let jld_type_term (t : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if jld_is_bnode_label t
  then
    FStar_Pervasives_Native.Some
      (RDF_Graph_Executable.T_BNode (jld_strip_bnode_prefix t))
  else
    if RDF_Graph_Executable.is_iri t
    then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI t)
    else FStar_Pervasives_Native.None
let rec jld_type_prepend_items (subj : RDF_Graph_Executable.subject)
  (items : Parser_JSON.json_val Prims.list)
  (acc : RDF_Graph_Executable.triple Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match items with
  | [] -> acc
  | (Parser_JSON.JString t)::rest ->
      (match jld_type_term t with
       | FStar_Pervasives_Native.Some tm ->
           jld_type_prepend_items subj rest
             ({
                RDF_Graph_Executable.s = subj;
                RDF_Graph_Executable.p = rdf_type_iri;
                RDF_Graph_Executable.o = tm
              } :: acc)
       | FStar_Pervasives_Native.None -> jld_type_prepend_items subj rest acc)
  | uu___::rest -> jld_type_prepend_items subj rest acc
let jld_type_prepend (subj : RDF_Graph_Executable.subject)
  (v : Parser_JSON.json_val) (acc : RDF_Graph_Executable.triple Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  jld_type_prepend_items subj (jld_as_array v) acc
let rec jld_expand_value (v : Parser_JSON.json_val) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option *
    RDF_Graph_Executable.triple Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (FStar_Pervasives_Native.None, acc, ctr)
  else
    (match v with
     | Parser_JSON.JObject uu___1 ->
         (match Parser_JSON.json_get_field "@value" v with
          | FStar_Pervasives_Native.Some uu___2 ->
              ((jld_value_object_to_term v), acc, ctr)
          | FStar_Pervasives_Native.None ->
              (match Parser_JSON.json_get_field "@list" v with
               | FStar_Pervasives_Native.Some lst ->
                   let uu___2 =
                     jld_expand_list (jld_as_array lst) ctr acc
                       (fuel - Prims.int_one) in
                   (match uu___2 with
                    | (t, acc1, ctr1) ->
                        ((FStar_Pervasives_Native.Some t), acc1, ctr1))
               | FStar_Pervasives_Native.None ->
                   let uu___2 =
                     jld_expand_node v ctr acc (fuel - Prims.int_one) in
                   (match uu___2 with
                    | (osubj, acc1, ctr1) ->
                        (match osubj with
                         | FStar_Pervasives_Native.Some subj ->
                             ((FStar_Pervasives_Native.Some
                                 (RDF_Graph_Executable.subject_to_term subj)),
                               acc1, ctr1)
                         | FStar_Pervasives_Native.None ->
                             (FStar_Pervasives_Native.None, acc1, ctr1)))))
     | uu___1 -> ((jld_scalar_to_term v), acc, ctr))
and jld_expand_list (items : Parser_JSON.json_val Prims.list)
  (ctr : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (fuel : Prims.nat) :
  (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.triple Prims.list *
    Prims.nat)=
  if fuel = Prims.int_zero
  then ((RDF_Graph_Executable.T_IRI rdf_nil_iri), acc, ctr)
  else
    (match items with
     | [] -> ((RDF_Graph_Executable.T_IRI rdf_nil_iri), acc, ctr)
     | item::rest ->
         let uu___1 = jld_expand_value item ctr acc (fuel - Prims.int_one) in
         (match uu___1 with
          | (oterm, acc1, ctr1) ->
              (match oterm with
               | FStar_Pervasives_Native.None ->
                   jld_expand_list rest ctr1 acc1 (fuel - Prims.int_one)
               | FStar_Pervasives_Native.Some t ->
                   let uu___2 = jld_fresh_bnode ctr1 in
                   (match uu___2 with
                    | (cell, ctr2) ->
                        let uu___3 =
                          jld_expand_list rest ctr2 acc1
                            (fuel - Prims.int_one) in
                        (match uu___3 with
                         | (rest_term, acc2, ctr3) ->
                             let cell_subj =
                               RDF_Graph_Executable.S_BNode cell in
                             ((RDF_Graph_Executable.T_BNode cell),
                               ({
                                  RDF_Graph_Executable.s = cell_subj;
                                  RDF_Graph_Executable.p = rdf_rest_iri;
                                  RDF_Graph_Executable.o = rest_term
                                } ::
                               {
                                 RDF_Graph_Executable.s = cell_subj;
                                 RDF_Graph_Executable.p = rdf_first_iri;
                                 RDF_Graph_Executable.o = t
                               } :: acc2), ctr3))))))
and jld_expand_node (v : Parser_JSON.json_val) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.subject FStar_Pervasives_Native.option *
    RDF_Graph_Executable.triple Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (FStar_Pervasives_Native.None, acc, ctr)
  else
    (match v with
     | Parser_JSON.JObject fields ->
         let uu___1 =
           match Parser_JSON.json_get_field "@id" v with
           | FStar_Pervasives_Native.Some (Parser_JSON.JString id_str) ->
               ((jld_id_to_subject id_str), ctr)
           | FStar_Pervasives_Native.Some uu___2 ->
               (FStar_Pervasives_Native.None, ctr)
           | FStar_Pervasives_Native.None ->
               let uu___2 = jld_fresh_bnode ctr in
               (match uu___2 with
                | (b, ctr') ->
                    ((FStar_Pervasives_Native.Some
                        (RDF_Graph_Executable.S_BNode b)), ctr')) in
         (match uu___1 with
          | (subj_opt, ctr1) ->
              (match subj_opt with
               | FStar_Pervasives_Native.None ->
                   (FStar_Pervasives_Native.None, acc, ctr1)
               | FStar_Pervasives_Native.Some subj ->
                   let uu___2 =
                     jld_expand_fields subj fields ctr1 acc
                       (fuel - Prims.int_one) in
                   (match uu___2 with
                    | (acc1, ctr2) ->
                        ((FStar_Pervasives_Native.Some subj), acc1, ctr2))))
     | uu___1 -> (FStar_Pervasives_Native.None, acc, ctr))
and jld_expand_fields (subj : RDF_Graph_Executable.subject)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (ctr : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (fuel : Prims.nat) : (RDF_Graph_Executable.triple Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, ctr)
  else
    (match fields with
     | [] -> (acc, ctr)
     | (key, value)::rest ->
         let uu___1 =
           if key = "@type"
           then ((jld_type_prepend subj value acc), ctr)
           else
             if jld_is_keyword key
             then (acc, ctr)
             else
               if RDF_Graph_Executable.is_iri key
               then
                 jld_expand_property subj key (jld_as_array value) ctr acc
                   (fuel - Prims.int_one)
               else (acc, ctr) in
         (match uu___1 with
          | (acc1, ctr1) ->
              jld_expand_fields subj rest ctr1 acc1 (fuel - Prims.int_one)))
and jld_expand_property (subj : RDF_Graph_Executable.subject)
  (prop : RDF_Graph_Executable.wf_iri)
  (vals : Parser_JSON.json_val Prims.list) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, ctr)
  else
    (match vals with
     | [] -> (acc, ctr)
     | v::rest ->
         let uu___1 = jld_expand_value v ctr acc (fuel - Prims.int_one) in
         (match uu___1 with
          | (oterm, acc1, ctr1) ->
              let acc2 =
                match oterm with
                | FStar_Pervasives_Native.Some t ->
                    {
                      RDF_Graph_Executable.s = subj;
                      RDF_Graph_Executable.p = prop;
                      RDF_Graph_Executable.o = t
                    } :: acc1
                | FStar_Pervasives_Native.None -> acc1 in
              jld_expand_property subj prop rest ctr1 acc2
                (fuel - Prims.int_one)))
let jld_graph_name_of_subject (s : RDF_Graph_Executable.subject) :
  RDF_Graph_Executable.iri=
  match s with
  | RDF_Graph_Executable.S_IRI i -> i
  | RDF_Graph_Executable.S_BNode b -> FStar_String.concat "" ["_:"; b]
let rec jld_expand_graph_nodes (nodes : Parser_JSON.json_val Prims.list)
  (ctr : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (fuel : Prims.nat) : (RDF_Graph_Executable.triple Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, ctr)
  else
    (match nodes with
     | [] -> (acc, ctr)
     | n::rest ->
         let uu___1 = jld_expand_node n ctr acc (fuel - Prims.int_one) in
         (match uu___1 with
          | (uu___2, acc1, ctr1) ->
              jld_expand_graph_nodes rest ctr1 acc1 (fuel - Prims.int_one)))
let jld_expand_top (v : Parser_JSON.json_val)
  (dflt : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (ctr : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  match v with
  | Parser_JSON.JObject fields ->
      (match Parser_JSON.json_get_field "@graph" v with
       | FStar_Pervasives_Native.Some g ->
           let uu___ =
             match Parser_JSON.json_get_field "@id" v with
             | FStar_Pervasives_Native.Some (Parser_JSON.JString id_str) ->
                 ((jld_id_to_subject id_str), ctr)
             | FStar_Pervasives_Native.Some uu___1 ->
                 (FStar_Pervasives_Native.None, ctr)
             | FStar_Pervasives_Native.None ->
                 let uu___1 = jld_fresh_bnode ctr in
                 (match uu___1 with
                  | (b, ctr') ->
                      ((FStar_Pervasives_Native.Some
                          (RDF_Graph_Executable.S_BNode b)), ctr')) in
           (match uu___ with
            | (subj_opt, ctr1) ->
                (match subj_opt with
                 | FStar_Pervasives_Native.None -> (dflt, named, ctr1)
                 | FStar_Pervasives_Native.Some gsubj ->
                     let uu___1 =
                       jld_expand_graph_nodes (jld_as_array g) ctr1 [] fuel in
                     (match uu___1 with
                      | (gtris, ctr2) ->
                          let uu___2 =
                            jld_expand_fields gsubj fields ctr2 dflt fuel in
                          (match uu___2 with
                           | (dflt1, ctr3) ->
                               let ng =
                                 {
                                   RDF_Graph_Executable.ng_name =
                                     (jld_graph_name_of_subject gsubj);
                                   RDF_Graph_Executable.ng_graph = gtris
                                 } in
                               (dflt1, (ng :: named), ctr3)))))
       | FStar_Pervasives_Native.None ->
           let uu___ = jld_expand_node v ctr dflt fuel in
           (match uu___ with | (uu___1, dflt1, ctr1) -> (dflt1, named, ctr1)))
  | uu___ -> (dflt, named, ctr)
let rec jld_expand_tops (vs : Parser_JSON.json_val Prims.list)
  (dflt : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (ctr : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (dflt, named, ctr)
  else
    (match vs with
     | [] -> (dflt, named, ctr)
     | v::rest ->
         let uu___1 = jld_expand_top v dflt named ctr fuel in
         (match uu___1 with
          | (d1, n1, c1) ->
              jld_expand_tops rest d1 n1 c1 (fuel - Prims.int_one)))
let rec jld_only_graph_keys
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::rest -> (k = "@graph") && (jld_only_graph_keys rest)
let jld_dataset_of_json (root : Parser_JSON.json_val) :
  RDF_Graph_Executable.rdf_dataset FStar_Pervasives_Native.option=
  let fuel = (Parser_JSON.json_size root) + Prims.int_one in
  match root with
  | Parser_JSON.JArray tops ->
      let uu___ = jld_expand_tops tops [] [] Prims.int_zero fuel in
      (match uu___ with
       | (d, n, uu___1) ->
           FStar_Pervasives_Native.Some
             (RDF_Graph_Executable.dataset_finalise
                {
                  RDF_Graph_Executable.ds_default = d;
                  RDF_Graph_Executable.ds_named = (FStar_List_Tot_Base.rev n)
                }))
  | Parser_JSON.JObject fields ->
      let tops =
        if jld_only_graph_keys fields
        then
          match Parser_JSON.json_get_field "@graph" root with
          | FStar_Pervasives_Native.Some g -> jld_as_array g
          | FStar_Pervasives_Native.None -> [root]
        else [root] in
      let uu___ = jld_expand_tops tops [] [] Prims.int_zero fuel in
      (match uu___ with
       | (d, n, uu___1) ->
           FStar_Pervasives_Native.Some
             (RDF_Graph_Executable.dataset_finalise
                {
                  RDF_Graph_Executable.ds_default = d;
                  RDF_Graph_Executable.ds_named = (FStar_List_Tot_Base.rev n)
                }))
  | uu___ -> FStar_Pervasives_Native.None
let jld_has_inline_context (root : Parser_JSON.json_val) : Prims.bool=
  match root with
  | Parser_JSON.JObject fields ->
      FStar_List_Tot_Base.existsb
        (fun kv -> (FStar_Pervasives_Native.fst kv) = "@context") fields
  | uu___ -> false
let parse_jsonld (input : Prims.string) :
  RDF_Graph_Executable.rdf_dataset FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      if jld_has_inline_context root
      then
        (match JSONLD_Expand.expand JSONLD_Context.empty_active_context root
         with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some expanded ->
             jld_dataset_of_json expanded)
      else jld_dataset_of_json root
