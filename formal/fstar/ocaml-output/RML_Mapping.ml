open Prims
let rml_TriplesMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/TriplesMap"
let rml_baseIRI : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/baseIRI"
let rml_logicalSource : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/logicalSource"
let rml_iterator : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/iterator"
let rml_referenceFormulation : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/referenceFormulation"
let rml_JSONPath : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/JSONPath"
let rml_XPath : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/XPath"
let rml_CSV : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/CSV"
let rml_source : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/source"
let rml_path : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/path"
let rml_root : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/root"
let rml_null : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/null"
let rml_MappingDirectory : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/MappingDirectory"
let rml_CurrentWorkingDirectory : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/CurrentWorkingDirectory"
let rml_subjectMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/subjectMap"
let rml_subject : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/subject"
let rml_class : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/class"
let rml_graph : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/graph"
let rml_graphMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/graphMap"
let rml_defaultGraph : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/defaultGraph"
let rml_predicateObjectMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/predicateObjectMap"
let rml_predicate : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/predicate"
let rml_predicateMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/predicateMap"
let rml_object : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/object"
let rml_objectMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/objectMap"
let rml_parentTriplesMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/parentTriplesMap"
let rml_joinCondition : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/joinCondition"
let rml_child : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/child"
let rml_parent : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/parent"
let rml_childMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/childMap"
let rml_parentMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/parentMap"
let rml_constant : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/constant"
let rml_reference : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/reference"
let rml_template : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/template"
let rml_termType : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/termType"
let rml_IRI : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/IRI"
let rml_URI : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/URI"
let rml_UnsafeIRI : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/UnsafeIRI"
let rml_BlankNode : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/BlankNode"
let rml_Literal : RDF_Graph_Executable.wf_iri= "http://w3id.org/rml/Literal"
let rml_datatype : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/datatype"
let rml_datatypeMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/datatypeMap"
let rml_language : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/language"
let rml_languageMap : RDF_Graph_Executable.wf_iri=
  "http://w3id.org/rml/languageMap"
type template_segment =
  | TSeg_Literal of Prims.string 
  | TSeg_Reference of Prims.string 
let uu___is_TSeg_Literal (projectee : template_segment) : Prims.bool=
  match projectee with | TSeg_Literal _0 -> true | uu___ -> false
let __proj__TSeg_Literal__item___0 (projectee : template_segment) :
  Prims.string= match projectee with | TSeg_Literal _0 -> _0
let uu___is_TSeg_Reference (projectee : template_segment) : Prims.bool=
  match projectee with | TSeg_Reference _0 -> true | uu___ -> false
let __proj__TSeg_Reference__item___0 (projectee : template_segment) :
  Prims.string= match projectee with | TSeg_Reference _0 -> _0
let flush_template_buf (mode : Prims.bool) (buf : Prims.string)
  (acc : template_segment Prims.list) : template_segment Prims.list=
  if buf = ""
  then acc
  else
    if mode then (TSeg_Reference buf) :: acc else (TSeg_Literal buf) :: acc
let rec scan_template_acc (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (mode : Prims.bool) (buf : Prims.string)
  (acc : template_segment Prims.list) : template_segment Prims.list=
  if fuel = Prims.int_zero
  then flush_template_buf mode buf acc
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then flush_template_buf mode buf acc
     else
       (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
        if (c = (Prims.of_int (0x5C))) && ((pos + Prims.int_one) < len)
        then
          scan_template_acc s (pos + (Prims.of_int (2)))
            (fuel - Prims.int_one) mode
            (Prims.strcat buf
               (FStar_String.sub s (pos + Prims.int_one) Prims.int_one)) acc
        else
          if (Prims.op_Negation mode) && (c = (Prims.of_int (0x7B)))
          then
            (let acc' = if buf = "" then acc else (TSeg_Literal buf) :: acc in
             scan_template_acc s (pos + Prims.int_one) (fuel - Prims.int_one)
               true "" acc')
          else
            if mode && (c = (Prims.of_int (0x7D)))
            then
              scan_template_acc s (pos + Prims.int_one)
                (fuel - Prims.int_one) false "" ((TSeg_Reference buf) :: acc)
            else
              scan_template_acc s (pos + Prims.int_one)
                (fuel - Prims.int_one) mode
                (Prims.strcat buf (FStar_String.sub s pos Prims.int_one)) acc))
let parse_template (s : Prims.string) : template_segment Prims.list=
  FStar_List_Tot_Base.rev
    (scan_template_acc s Prims.int_zero
       ((FStar_String.strlen s) + Prims.int_one) false "" [])
type term_type =
  | TT_IRI 
  | TT_URI 
  | TT_UnsafeIRI 
  | TT_BlankNode 
  | TT_Literal 
let uu___is_TT_IRI (projectee : term_type) : Prims.bool=
  match projectee with | TT_IRI -> true | uu___ -> false
let uu___is_TT_URI (projectee : term_type) : Prims.bool=
  match projectee with | TT_URI -> true | uu___ -> false
let uu___is_TT_UnsafeIRI (projectee : term_type) : Prims.bool=
  match projectee with | TT_UnsafeIRI -> true | uu___ -> false
let uu___is_TT_BlankNode (projectee : term_type) : Prims.bool=
  match projectee with | TT_BlankNode -> true | uu___ -> false
let uu___is_TT_Literal (projectee : term_type) : Prims.bool=
  match projectee with | TT_Literal -> true | uu___ -> false
type reference_formulation =
  | RF_JSONPath 
  | RF_XPath 
  | RF_CSV 
  | RF_Other of Prims.string 
let uu___is_RF_JSONPath (projectee : reference_formulation) : Prims.bool=
  match projectee with | RF_JSONPath -> true | uu___ -> false
let uu___is_RF_XPath (projectee : reference_formulation) : Prims.bool=
  match projectee with | RF_XPath -> true | uu___ -> false
let uu___is_RF_CSV (projectee : reference_formulation) : Prims.bool=
  match projectee with | RF_CSV -> true | uu___ -> false
let uu___is_RF_Other (projectee : reference_formulation) : Prims.bool=
  match projectee with | RF_Other _0 -> true | uu___ -> false
let __proj__RF_Other__item___0 (projectee : reference_formulation) :
  Prims.string= match projectee with | RF_Other _0 -> _0
type source_root =
  | Root_MappingDirectory 
  | Root_CurrentWorkingDirectory 
  | Root_Other of Prims.string 
let uu___is_Root_MappingDirectory (projectee : source_root) : Prims.bool=
  match projectee with | Root_MappingDirectory -> true | uu___ -> false
let uu___is_Root_CurrentWorkingDirectory (projectee : source_root) :
  Prims.bool=
  match projectee with
  | Root_CurrentWorkingDirectory -> true
  | uu___ -> false
let uu___is_Root_Other (projectee : source_root) : Prims.bool=
  match projectee with | Root_Other _0 -> true | uu___ -> false
let __proj__Root_Other__item___0 (projectee : source_root) : Prims.string=
  match projectee with | Root_Other _0 -> _0
let decode_term_type (t : RDF_Graph_Executable.rdf_term) :
  term_type FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_IRI i ->
      if i = rml_IRI
      then FStar_Pervasives_Native.Some TT_IRI
      else
        if i = rml_URI
        then FStar_Pervasives_Native.Some TT_URI
        else
          if i = rml_UnsafeIRI
          then FStar_Pervasives_Native.Some TT_UnsafeIRI
          else
            if i = rml_BlankNode
            then FStar_Pervasives_Native.Some TT_BlankNode
            else
              if i = rml_Literal
              then FStar_Pervasives_Native.Some TT_Literal
              else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let decode_reference_formulation (t : RDF_Graph_Executable.rdf_term) :
  reference_formulation=
  match t with
  | RDF_Graph_Executable.T_IRI i ->
      if i = rml_JSONPath
      then RF_JSONPath
      else
        if i = rml_XPath
        then RF_XPath
        else if i = rml_CSV then RF_CSV else RF_Other i
  | uu___ -> RF_Other ""
let decode_source_root (t : RDF_Graph_Executable.rdf_term) : source_root=
  match t with
  | RDF_Graph_Executable.T_IRI i ->
      if i = rml_MappingDirectory
      then Root_MappingDirectory
      else
        if i = rml_CurrentWorkingDirectory
        then Root_CurrentWorkingDirectory
        else Root_Other i
  | uu___ -> Root_Other ""
type node_ref = Prims.string
let term_to_node_ref (t : RDF_Graph_Executable.rdf_term) :
  node_ref FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_IRI i -> FStar_Pervasives_Native.Some i
  | RDF_Graph_Executable.T_BNode b ->
      FStar_Pervasives_Native.Some (Prims.strcat "_:" b)
  | RDF_Graph_Executable.T_Literal uu___ -> FStar_Pervasives_Native.None
let subject_to_node_ref (s : RDF_Graph_Executable.subject) : node_ref=
  match s with
  | RDF_Graph_Executable.S_IRI i -> i
  | RDF_Graph_Executable.S_BNode b -> Prims.strcat "_:" b
let rec distinct_subjects_acc (g : RDF_Graph_Executable.rdf_graph)
  (acc : RDF_Graph_Executable.subject Prims.list) :
  RDF_Graph_Executable.subject Prims.list=
  match g with
  | [] -> acc
  | t::rest ->
      if
        FStar_List_Tot_Base.existsb
          (RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s) acc
      then distinct_subjects_acc rest acc
      else distinct_subjects_acc rest ((t.RDF_Graph_Executable.s) :: acc)
let distinct_subjects (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.subject Prims.list= distinct_subjects_acc g []
type logical_source =
  {
  ls_iterator: Prims.string FStar_Pervasives_Native.option ;
  ls_reference_formulation:
    reference_formulation FStar_Pervasives_Native.option ;
  ls_source_path: Prims.string FStar_Pervasives_Native.option ;
  ls_source_root: source_root FStar_Pervasives_Native.option ;
  ls_null_values: Prims.string Prims.list }
let __proj__Mklogical_source__item__ls_iterator (projectee : logical_source)
  : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ls_iterator; ls_reference_formulation; ls_source_path; ls_source_root;
      ls_null_values;_} -> ls_iterator
let __proj__Mklogical_source__item__ls_reference_formulation
  (projectee : logical_source) :
  reference_formulation FStar_Pervasives_Native.option=
  match projectee with
  | { ls_iterator; ls_reference_formulation; ls_source_path; ls_source_root;
      ls_null_values;_} -> ls_reference_formulation
let __proj__Mklogical_source__item__ls_source_path
  (projectee : logical_source) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ls_iterator; ls_reference_formulation; ls_source_path; ls_source_root;
      ls_null_values;_} -> ls_source_path
let __proj__Mklogical_source__item__ls_source_root
  (projectee : logical_source) : source_root FStar_Pervasives_Native.option=
  match projectee with
  | { ls_iterator; ls_reference_formulation; ls_source_path; ls_source_root;
      ls_null_values;_} -> ls_source_root
let __proj__Mklogical_source__item__ls_null_values
  (projectee : logical_source) : Prims.string Prims.list=
  match projectee with
  | { ls_iterator; ls_reference_formulation; ls_source_path; ls_source_root;
      ls_null_values;_} -> ls_null_values
let empty_logical_source : logical_source=
  {
    ls_iterator = FStar_Pervasives_Native.None;
    ls_reference_formulation = FStar_Pervasives_Native.None;
    ls_source_path = FStar_Pervasives_Native.None;
    ls_source_root = FStar_Pervasives_Native.None;
    ls_null_values = []
  }
let first_literal (l : RDF_Graph_Executable.rdf_term Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match l with
  | (RDF_Graph_Executable.T_Literal lit)::uu___ ->
      FStar_Pervasives_Native.Some (lit.RDF_Graph_Executable.lexical_form)
  | uu___ -> FStar_Pervasives_Native.None
let literal_strings (l : RDF_Graph_Executable.rdf_term Prims.list) :
  Prims.string Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match t with
       | RDF_Graph_Executable.T_Literal lit ->
           [lit.RDF_Graph_Executable.lexical_form]
       | uu___ -> []) l
let decode_logical_source (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) :
  logical_source FStar_Pervasives_Native.option=
  match RDF_Graph_Executable.find_objects g s rml_logicalSource with
  | [] -> FStar_Pervasives_Native.None
  | ls_term::uu___ ->
      (match RDF_Graph_Executable.term_to_subject ls_term with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ls_subj ->
           let iterator =
             first_literal
               (RDF_Graph_Executable.find_objects g ls_subj rml_iterator) in
           let refform =
             match RDF_Graph_Executable.find_objects g ls_subj
                     rml_referenceFormulation
             with
             | t::uu___1 ->
                 FStar_Pervasives_Native.Some
                   (decode_reference_formulation t)
             | [] -> FStar_Pervasives_Native.None in
           let uu___1 =
             match RDF_Graph_Executable.find_objects g ls_subj rml_source
             with
             | src_term::uu___2 ->
                 (match RDF_Graph_Executable.term_to_subject src_term with
                  | FStar_Pervasives_Native.Some src_subj ->
                      ((first_literal
                          (RDF_Graph_Executable.find_objects g src_subj
                             rml_path)),
                        ((match RDF_Graph_Executable.find_objects g src_subj
                                  rml_root
                          with
                          | t::uu___3 ->
                              FStar_Pervasives_Native.Some
                                (decode_source_root t)
                          | [] -> FStar_Pervasives_Native.None)),
                        (literal_strings
                           (RDF_Graph_Executable.find_objects g src_subj
                              rml_null)))
                  | FStar_Pervasives_Native.None ->
                      (FStar_Pervasives_Native.None,
                        FStar_Pervasives_Native.None, []))
             | [] ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   []) in
           (match uu___1 with
            | (path, root, null_values) ->
                FStar_Pervasives_Native.Some
                  {
                    ls_iterator = iterator;
                    ls_reference_formulation = refform;
                    ls_source_path = path;
                    ls_source_root = root;
                    ls_null_values = null_values
                  }))
type term_map_form =
  | TMF_Constant of RDF_Graph_Executable.rdf_term 
  | TMF_Reference of Prims.string 
  | TMF_Template of Prims.string 
  | TMF_Unknown 
let uu___is_TMF_Constant (projectee : term_map_form) : Prims.bool=
  match projectee with | TMF_Constant _0 -> true | uu___ -> false
let __proj__TMF_Constant__item___0 (projectee : term_map_form) :
  RDF_Graph_Executable.rdf_term= match projectee with | TMF_Constant _0 -> _0
let uu___is_TMF_Reference (projectee : term_map_form) : Prims.bool=
  match projectee with | TMF_Reference _0 -> true | uu___ -> false
let __proj__TMF_Reference__item___0 (projectee : term_map_form) :
  Prims.string= match projectee with | TMF_Reference _0 -> _0
let uu___is_TMF_Template (projectee : term_map_form) : Prims.bool=
  match projectee with | TMF_Template _0 -> true | uu___ -> false
let __proj__TMF_Template__item___0 (projectee : term_map_form) :
  Prims.string= match projectee with | TMF_Template _0 -> _0
let uu___is_TMF_Unknown (projectee : term_map_form) : Prims.bool=
  match projectee with | TMF_Unknown -> true | uu___ -> false
type term_map =
  {
  tmap_form: term_map_form ;
  tmap_termtype: term_type FStar_Pervasives_Native.option ;
  tmap_datatype: term_map FStar_Pervasives_Native.option ;
  tmap_language: term_map FStar_Pervasives_Native.option }
let __proj__Mkterm_map__item__tmap_form (projectee : term_map) :
  term_map_form=
  match projectee with
  | { tmap_form; tmap_termtype; tmap_datatype; tmap_language;_} -> tmap_form
let __proj__Mkterm_map__item__tmap_termtype (projectee : term_map) :
  term_type FStar_Pervasives_Native.option=
  match projectee with
  | { tmap_form; tmap_termtype; tmap_datatype; tmap_language;_} ->
      tmap_termtype
let __proj__Mkterm_map__item__tmap_datatype (projectee : term_map) :
  term_map FStar_Pervasives_Native.option=
  match projectee with
  | { tmap_form; tmap_termtype; tmap_datatype; tmap_language;_} ->
      tmap_datatype
let __proj__Mkterm_map__item__tmap_language (projectee : term_map) :
  term_map FStar_Pervasives_Native.option=
  match projectee with
  | { tmap_form; tmap_termtype; tmap_datatype; tmap_language;_} ->
      tmap_language
let unknown_term_map : term_map=
  {
    tmap_form = TMF_Unknown;
    tmap_termtype = FStar_Pervasives_Native.None;
    tmap_datatype = FStar_Pervasives_Native.None;
    tmap_language = FStar_Pervasives_Native.None
  }
let const_term_map (t : RDF_Graph_Executable.rdf_term) : term_map=
  {
    tmap_form = (TMF_Constant t);
    tmap_termtype = FStar_Pervasives_Native.None;
    tmap_datatype = FStar_Pervasives_Native.None;
    tmap_language = FStar_Pervasives_Native.None
  }
let ref_term_map (r : Prims.string) : term_map=
  {
    tmap_form = (TMF_Reference r);
    tmap_termtype = FStar_Pervasives_Native.None;
    tmap_datatype = FStar_Pervasives_Native.None;
    tmap_language = FStar_Pervasives_Native.None
  }
let rec decode_term_map_from_subject (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) : term_map=
  if fuel = Prims.int_zero
  then unknown_term_map
  else
    (let fuel' = fuel - Prims.int_one in
     let form =
       match RDF_Graph_Executable.find_objects g s rml_constant with
       | t::uu___1 -> TMF_Constant t
       | [] ->
           (match RDF_Graph_Executable.find_objects g s rml_reference with
            | (RDF_Graph_Executable.T_Literal l)::uu___1 ->
                TMF_Reference (l.RDF_Graph_Executable.lexical_form)
            | uu___1 ->
                (match RDF_Graph_Executable.find_objects g s rml_template
                 with
                 | (RDF_Graph_Executable.T_Literal l)::uu___2 ->
                     TMF_Template (l.RDF_Graph_Executable.lexical_form)
                 | uu___2 -> TMF_Unknown)) in
     let termtype =
       match RDF_Graph_Executable.find_objects g s rml_termType with
       | t::uu___1 -> decode_term_type t
       | [] -> FStar_Pervasives_Native.None in
     let datatype =
       match RDF_Graph_Executable.find_objects g s rml_datatypeMap with
       | t::uu___1 ->
           (match RDF_Graph_Executable.term_to_subject t with
            | FStar_Pervasives_Native.Some ds ->
                FStar_Pervasives_Native.Some
                  (decode_term_map_from_subject g ds fuel')
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | [] ->
           (match RDF_Graph_Executable.find_objects g s rml_datatype with
            | t::uu___1 -> FStar_Pervasives_Native.Some (const_term_map t)
            | [] -> FStar_Pervasives_Native.None) in
     let language =
       match RDF_Graph_Executable.find_objects g s rml_languageMap with
       | t::uu___1 ->
           (match RDF_Graph_Executable.term_to_subject t with
            | FStar_Pervasives_Native.Some ls ->
                FStar_Pervasives_Native.Some
                  (decode_term_map_from_subject g ls fuel')
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | [] ->
           (match RDF_Graph_Executable.find_objects g s rml_language with
            | t::uu___1 -> FStar_Pervasives_Native.Some (const_term_map t)
            | [] -> FStar_Pervasives_Native.None) in
     {
       tmap_form = form;
       tmap_termtype = termtype;
       tmap_datatype = datatype;
       tmap_language = language
     })
type join_condition = {
  jc_child: term_map ;
  jc_parent: term_map }
let __proj__Mkjoin_condition__item__jc_child (projectee : join_condition) :
  term_map= match projectee with | { jc_child; jc_parent;_} -> jc_child
let __proj__Mkjoin_condition__item__jc_parent (projectee : join_condition) :
  term_map= match projectee with | { jc_child; jc_parent;_} -> jc_parent
type ref_object_map =
  {
  rom_parent_triples_map: node_ref ;
  rom_joins: join_condition Prims.list }
let __proj__Mkref_object_map__item__rom_parent_triples_map
  (projectee : ref_object_map) : node_ref=
  match projectee with
  | { rom_parent_triples_map; rom_joins;_} -> rom_parent_triples_map
let __proj__Mkref_object_map__item__rom_joins (projectee : ref_object_map) :
  join_condition Prims.list=
  match projectee with | { rom_parent_triples_map; rom_joins;_} -> rom_joins
let decode_child_or_parent (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (map_pred : RDF_Graph_Executable.wf_iri)
  (shortcut_pred : RDF_Graph_Executable.wf_iri) (fuel : Prims.nat) :
  term_map=
  match RDF_Graph_Executable.find_objects g s map_pred with
  | t::uu___ ->
      (match RDF_Graph_Executable.term_to_subject t with
       | FStar_Pervasives_Native.Some ms ->
           decode_term_map_from_subject g ms fuel
       | FStar_Pervasives_Native.None -> unknown_term_map)
  | [] ->
      (match RDF_Graph_Executable.find_objects g s shortcut_pred with
       | (RDF_Graph_Executable.T_Literal l)::uu___ ->
           ref_term_map l.RDF_Graph_Executable.lexical_form
       | uu___ -> unknown_term_map)
let decode_join_conditions (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) :
  join_condition Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match RDF_Graph_Executable.term_to_subject t with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some jc_subj ->
           [{
              jc_child =
                (decode_child_or_parent g jc_subj rml_childMap rml_child fuel);
              jc_parent =
                (decode_child_or_parent g jc_subj rml_parentMap rml_parent
                   fuel)
            }]) (RDF_Graph_Executable.find_objects g s rml_joinCondition)
type object_binding =
  | OB_TermMap of term_map 
  | OB_Join of ref_object_map 
let uu___is_OB_TermMap (projectee : object_binding) : Prims.bool=
  match projectee with | OB_TermMap _0 -> true | uu___ -> false
let __proj__OB_TermMap__item___0 (projectee : object_binding) : term_map=
  match projectee with | OB_TermMap _0 -> _0
let uu___is_OB_Join (projectee : object_binding) : Prims.bool=
  match projectee with | OB_Join _0 -> true | uu___ -> false
let __proj__OB_Join__item___0 (projectee : object_binding) : ref_object_map=
  match projectee with | OB_Join _0 -> _0
type predicate_object_map =
  {
  pom_predicates: term_map Prims.list ;
  pom_objects: object_binding Prims.list ;
  pom_graphs: term_map Prims.list }
let __proj__Mkpredicate_object_map__item__pom_predicates
  (projectee : predicate_object_map) : term_map Prims.list=
  match projectee with
  | { pom_predicates; pom_objects; pom_graphs;_} -> pom_predicates
let __proj__Mkpredicate_object_map__item__pom_objects
  (projectee : predicate_object_map) : object_binding Prims.list=
  match projectee with
  | { pom_predicates; pom_objects; pom_graphs;_} -> pom_objects
let __proj__Mkpredicate_object_map__item__pom_graphs
  (projectee : predicate_object_map) : term_map Prims.list=
  match projectee with
  | { pom_predicates; pom_objects; pom_graphs;_} -> pom_graphs
let decode_graphs (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) :
  term_map Prims.list=
  let via_map =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match RDF_Graph_Executable.term_to_subject t with
         | FStar_Pervasives_Native.Some gs ->
             [decode_term_map_from_subject g gs fuel]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s rml_graphMap) in
  let via_shortcut =
    FStar_List_Tot_Base.map const_term_map
      (RDF_Graph_Executable.find_objects g s rml_graph) in
  FStar_List_Tot_Base.op_At via_map via_shortcut
let decode_predicates (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) :
  term_map Prims.list=
  let via_map =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match RDF_Graph_Executable.term_to_subject t with
         | FStar_Pervasives_Native.Some ps ->
             [decode_term_map_from_subject g ps fuel]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s rml_predicateMap) in
  let via_shortcut =
    FStar_List_Tot_Base.map const_term_map
      (RDF_Graph_Executable.find_objects g s rml_predicate) in
  FStar_List_Tot_Base.op_At via_map via_shortcut
let decode_object_bindings (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) :
  object_binding Prims.list=
  let via_object_map =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match RDF_Graph_Executable.term_to_subject t with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some om_subj ->
             (match RDF_Graph_Executable.find_objects g om_subj
                      rml_parentTriplesMap
              with
              | ptm::uu___ ->
                  let parent_ref =
                    match term_to_node_ref ptm with
                    | FStar_Pervasives_Native.Some r -> r
                    | FStar_Pervasives_Native.None -> "" in
                  [OB_Join
                     {
                       rom_parent_triples_map = parent_ref;
                       rom_joins = (decode_join_conditions g om_subj fuel)
                     }]
              | [] ->
                  [OB_TermMap (decode_term_map_from_subject g om_subj fuel)]))
      (RDF_Graph_Executable.find_objects g s rml_objectMap) in
  let via_object_shortcut =
    FStar_List_Tot_Base.map (fun t -> OB_TermMap (const_term_map t))
      (RDF_Graph_Executable.find_objects g s rml_object) in
  FStar_List_Tot_Base.op_At via_object_map via_object_shortcut
let decode_predicate_object_map (g : RDF_Graph_Executable.rdf_graph)
  (pom_subj : RDF_Graph_Executable.subject) (fuel : Prims.nat) :
  predicate_object_map=
  {
    pom_predicates = (decode_predicates g pom_subj fuel);
    pom_objects = (decode_object_bindings g pom_subj fuel);
    pom_graphs = (decode_graphs g pom_subj fuel)
  }
let decode_predicate_object_maps (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) :
  predicate_object_map Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match RDF_Graph_Executable.term_to_subject t with
       | FStar_Pervasives_Native.Some pom_subj ->
           [decode_predicate_object_map g pom_subj fuel]
       | FStar_Pervasives_Native.None -> [])
    (RDF_Graph_Executable.find_objects g s rml_predicateObjectMap)
type subject_map_t =
  {
  sm_term: term_map ;
  sm_classes: RDF_Graph_Executable.wf_iri Prims.list ;
  sm_graphs: term_map Prims.list }
let __proj__Mksubject_map_t__item__sm_term (projectee : subject_map_t) :
  term_map=
  match projectee with | { sm_term; sm_classes; sm_graphs;_} -> sm_term
let __proj__Mksubject_map_t__item__sm_classes (projectee : subject_map_t) :
  RDF_Graph_Executable.wf_iri Prims.list=
  match projectee with | { sm_term; sm_classes; sm_graphs;_} -> sm_classes
let __proj__Mksubject_map_t__item__sm_graphs (projectee : subject_map_t) :
  term_map Prims.list=
  match projectee with | { sm_term; sm_classes; sm_graphs;_} -> sm_graphs
let decode_subject_map (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) :
  subject_map_t FStar_Pervasives_Native.option=
  match RDF_Graph_Executable.find_objects g s rml_subjectMap with
  | [] ->
      (match RDF_Graph_Executable.find_objects g s rml_subject with
       | t::uu___ ->
           FStar_Pervasives_Native.Some
             { sm_term = (const_term_map t); sm_classes = []; sm_graphs = []
             }
       | [] -> FStar_Pervasives_Native.None)
  | sm_term::[] ->
      (match RDF_Graph_Executable.term_to_subject sm_term with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sm_subj ->
           let term = decode_term_map_from_subject g sm_subj fuel in
           let classes =
             FStar_List_Tot_Base.concatMap
               (fun t ->
                  match t with
                  | RDF_Graph_Executable.T_IRI i -> [i]
                  | uu___ -> [])
               (RDF_Graph_Executable.find_objects g sm_subj rml_class) in
           let graphs = decode_graphs g sm_subj fuel in
           FStar_Pervasives_Native.Some
             { sm_term = term; sm_classes = classes; sm_graphs = graphs })
  | uu___::uu___1::uu___2 -> FStar_Pervasives_Native.None
type triples_map =
  {
  tm_id: node_ref ;
  tm_base_iri: Prims.string FStar_Pervasives_Native.option ;
  tm_logical_source: logical_source FStar_Pervasives_Native.option ;
  tm_subject_map: subject_map_t FStar_Pervasives_Native.option ;
  tm_predicate_object_maps: predicate_object_map Prims.list }
let __proj__Mktriples_map__item__tm_id (projectee : triples_map) : node_ref=
  match projectee with
  | { tm_id; tm_base_iri; tm_logical_source; tm_subject_map;
      tm_predicate_object_maps;_} -> tm_id
let __proj__Mktriples_map__item__tm_base_iri (projectee : triples_map) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { tm_id; tm_base_iri; tm_logical_source; tm_subject_map;
      tm_predicate_object_maps;_} -> tm_base_iri
let __proj__Mktriples_map__item__tm_logical_source (projectee : triples_map)
  : logical_source FStar_Pervasives_Native.option=
  match projectee with
  | { tm_id; tm_base_iri; tm_logical_source; tm_subject_map;
      tm_predicate_object_maps;_} -> tm_logical_source
let __proj__Mktriples_map__item__tm_subject_map (projectee : triples_map) :
  subject_map_t FStar_Pervasives_Native.option=
  match projectee with
  | { tm_id; tm_base_iri; tm_logical_source; tm_subject_map;
      tm_predicate_object_maps;_} -> tm_subject_map
let __proj__Mktriples_map__item__tm_predicate_object_maps
  (projectee : triples_map) : predicate_object_map Prims.list=
  match projectee with
  | { tm_id; tm_base_iri; tm_logical_source; tm_subject_map;
      tm_predicate_object_maps;_} -> tm_predicate_object_maps
type mapping_document = {
  md_triples_maps: triples_map Prims.list }
let __proj__Mkmapping_document__item__md_triples_maps
  (projectee : mapping_document) : triples_map Prims.list=
  match projectee with | { md_triples_maps;_} -> md_triples_maps
let decode_triples_map (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) (fuel : Prims.nat) : triples_map=
  {
    tm_id = (subject_to_node_ref s);
    tm_base_iri =
      (match RDF_Graph_Executable.find_objects g s rml_baseIRI with
       | (RDF_Graph_Executable.T_IRI i)::uu___ ->
           FStar_Pervasives_Native.Some i
       | uu___ -> FStar_Pervasives_Native.None);
    tm_logical_source = (decode_logical_source g s);
    tm_subject_map = (decode_subject_map g s fuel);
    tm_predicate_object_maps = (decode_predicate_object_maps g s fuel)
  }
let is_triples_map_subject (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s s) &&
          (t.RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type))
         &&
         (RDF_Graph_Executable.rdf_term_eq t.RDF_Graph_Executable.o
            (RDF_Graph_Executable.T_IRI rml_TriplesMap))) g
let decode_mapping_document (g : RDF_Graph_Executable.rdf_graph) :
  mapping_document=
  let subs = distinct_subjects g in
  let tm_subs = FStar_List_Tot_Base.filter (is_triples_map_subject g) subs in
  {
    md_triples_maps =
      (FStar_List_Tot_Base.map
         (fun s ->
            decode_triples_map g s
              ((RDF_Graph_Executable.graph_len g) + Prims.int_one)) tm_subs)
  }
