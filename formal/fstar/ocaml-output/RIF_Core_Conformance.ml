open Prims
let conformance_fuel : Prims.nat= (Prims.of_int (1000))
let rec collect_vars_excl_declare (n : Parser_XML.xml_node)
  (fuel : Prims.nat) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if Parser_RIFXML.tag_is "declare" tag
         then []
         else
           if Parser_RIFXML.tag_is "Var" tag
           then
             (let raw =
                Parser_RIFXML.trim_ws
                  (Parser_RIFXML.collect_leaf_text children) in
              if (FStar_String.strlen raw) = Prims.int_zero
              then []
              else [raw])
           else
             collect_vars_excl_declare_list children (fuel - Prims.int_one)
     | uu___1 -> [])
and collect_vars_excl_declare_list
  (children : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match children with
     | [] -> []
     | c::rest ->
         FStar_List_Tot_Base.append
           (collect_vars_excl_declare c (fuel - Prims.int_one))
           (collect_vars_excl_declare_list rest (fuel - Prims.int_one)))
let rec collect_declared_vars (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if Parser_RIFXML.tag_is "declare" tag
         then
           FStar_List_Tot_Base.append
             (collect_vars_excl_declare_list children (fuel - Prims.int_one))
             (collect_declared_vars_list children (fuel - Prims.int_one))
         else collect_declared_vars_list children (fuel - Prims.int_one)
     | uu___1 -> [])
and collect_declared_vars_list (children : Parser_XML.xml_node Prims.list)
  (fuel : Prims.nat) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match children with
     | [] -> []
     | c::rest ->
         FStar_List_Tot_Base.append
           (collect_declared_vars c (fuel - Prims.int_one))
           (collect_declared_vars_list rest (fuel - Prims.int_one)))
let list_subset (a : Prims.string Prims.list) (b : Prims.string Prims.list) :
  Prims.bool=
  FStar_List_Tot_Base.for_all (fun x -> FStar_List_Tot_Base.mem x b) a
let no_free_variables (root : Parser_XML.xml_node) : Prims.bool=
  list_subset (collect_vars_excl_declare root conformance_fuel)
    (collect_declared_vars root conformance_fuel)
type bpat =
  | BP_B 
  | BP_U 
let uu___is_BP_B (projectee : bpat) : Prims.bool=
  match projectee with | BP_B -> true | uu___ -> false
let uu___is_BP_U (projectee : bpat) : Prims.bool=
  match projectee with | BP_U -> true | uu___ -> false
let iri_string_local : Prims.string= "iri-string"
let list_contains_local : Prims.string= "list-contains"
let rec find_last_hash_aux (cs : FStar_Char.char Prims.list)
  (idx : Prims.nat) (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x23))
      then
        find_last_hash_aux rest (idx + Prims.int_one)
          (FStar_Pervasives_Native.Some idx)
      else find_last_hash_aux rest (idx + Prims.int_one) last
let local_name_of_iri (iri : Prims.string) : Prims.string=
  match find_last_hash_aux (FStar_String.list_of_string iri) Prims.int_zero
          FStar_Pervasives_Native.None
  with
  | FStar_Pervasives_Native.None -> iri
  | FStar_Pervasives_Native.Some pos ->
      let len = FStar_String.strlen iri in
      if (pos + Prims.int_one) >= len
      then ""
      else
        FStar_String.sub iri (pos + Prims.int_one)
          ((len - pos) - Prims.int_one)
let builtin_binding_patterns (local : Prims.string) :
  bpat Prims.list Prims.list=
  if local = iri_string_local
  then [[BP_B; BP_U]; [BP_U; BP_B]]
  else if local = list_contains_local then [[BP_B; BP_U]] else []
let var_name_of (n : Parser_XML.xml_node) :
  Prims.string FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (tag, uu___, children) ->
      if Parser_RIFXML.tag_is "Var" tag
      then
        let raw =
          Parser_RIFXML.trim_ws (Parser_RIFXML.collect_leaf_text children) in
        (if (FStar_String.strlen raw) = Prims.int_zero
         then FStar_Pervasives_Native.None
         else FStar_Pervasives_Native.Some raw)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let rec collect_all_vars (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if Parser_RIFXML.tag_is "Var" tag
         then
           let raw =
             Parser_RIFXML.trim_ws (Parser_RIFXML.collect_leaf_text children) in
           (if (FStar_String.strlen raw) = Prims.int_zero then [] else [raw])
         else collect_all_vars_list children (fuel - Prims.int_one)
     | uu___1 -> [])
and collect_all_vars_list (children : Parser_XML.xml_node Prims.list)
  (fuel : Prims.nat) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match children with
     | [] -> []
     | c::rest ->
         FStar_List_Tot_Base.append
           (collect_all_vars c (fuel - Prims.int_one))
           (collect_all_vars_list rest (fuel - Prims.int_one)))
let dedup_strings (xs : Prims.string Prims.list) : Prims.string Prims.list=
  let rec go xs1 acc =
    match xs1 with
    | [] -> acc
    | x::rest ->
        if FStar_List_Tot_Base.mem x acc
        then go rest acc
        else go rest (FStar_List_Tot_Base.op_At acc [x]) in
  go xs []
let arg_availability (bound : Prims.string Prims.list)
  (arg : Parser_XML.xml_node) : bpat=
  match var_name_of arg with
  | FStar_Pervasives_Native.Some name ->
      if FStar_List_Tot_Base.mem name bound then BP_B else BP_U
  | FStar_Pervasives_Native.None -> BP_B
let rec args_availability (bound : Prims.string Prims.list)
  (args : Parser_XML.xml_node Prims.list) : bpat Prims.list=
  match args with
  | [] -> []
  | a::rest -> (arg_availability bound a) :: (args_availability bound rest)
let rec pattern_applicable (allowed : bpat Prims.list)
  (actual : bpat Prims.list) : Prims.bool=
  match (allowed, actual) with
  | ([], []) -> true
  | ((BP_B)::arest, (BP_B)::brest) -> pattern_applicable arest brest
  | ((BP_B)::uu___, (BP_U)::uu___1) -> false
  | ((BP_U)::arest, uu___::brest) -> pattern_applicable arest brest
  | (uu___, uu___1) -> false
let rec newly_bound_from_pattern (allowed : bpat Prims.list)
  (args : Parser_XML.xml_node Prims.list) (actual : bpat Prims.list) :
  Prims.string Prims.list=
  match (allowed, args, actual) with
  | ((BP_U)::arest, a::args_rest, (BP_U)::brest) ->
      (match var_name_of a with
       | FStar_Pervasives_Native.Some name -> name ::
           (newly_bound_from_pattern arest args_rest brest)
       | FStar_Pervasives_Native.None ->
           newly_bound_from_pattern arest args_rest brest)
  | (uu___::arest, uu___1::args_rest, uu___2::brest) ->
      newly_bound_from_pattern arest args_rest brest
  | (uu___, uu___1, uu___2) -> []
let rec try_patterns (patterns : bpat Prims.list Prims.list)
  (args : Parser_XML.xml_node Prims.list) (actual : bpat Prims.list) :
  Prims.string Prims.list=
  match patterns with
  | [] -> []
  | p::rest ->
      if
        ((FStar_List_Tot_Base.length p) = (FStar_List_Tot_Base.length actual))
          && (pattern_applicable p actual)
      then newly_bound_from_pattern p args actual
      else try_patterns rest args actual
let external_op_and_args (external_node : Parser_XML.xml_node) :
  (Prims.string * Parser_XML.xml_node Prims.list)
    FStar_Pervasives_Native.option=
  match external_node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      (match Parser_RIFXML.first_child_with_local_name "content" children
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some content_node ->
           (match content_node with
            | Parser_XML.XElement (uu___2, uu___3, cchildren) ->
                (match Parser_RIFXML.child_elements_only cchildren with
                 | inner::[] ->
                     (match inner with
                      | Parser_XML.XElement (uu___4, uu___5, ichildren) ->
                          (match Parser_RIFXML.first_child_with_local_name
                                   "op" ichildren
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some op_node ->
                               (match Parser_RIFXML.parse_term_host op_node
                                with
                                | FStar_Pervasives_Native.Some
                                    (RIF_Core_Syntax.RIF_Const
                                    (RDF_Graph_Executable.T_IRI pi)) ->
                                    let args_n =
                                      Parser_RIFXML.first_child_with_local_name
                                        "args" ichildren in
                                    let args =
                                      match args_n with
                                      | FStar_Pervasives_Native.None -> []
                                      | FStar_Pervasives_Native.Some an ->
                                          Parser_RIFXML.child_elements_only
                                            (Parser_XML.element_children an) in
                                    FStar_Pervasives_Native.Some
                                      ((local_name_of_iri pi), args)
                                | uu___6 -> FStar_Pervasives_Native.None))
                      | uu___4 -> FStar_Pervasives_Native.None)
                 | uu___4 -> FStar_Pervasives_Native.None)
            | uu___2 -> FStar_Pervasives_Native.None))
  | uu___ -> FStar_Pervasives_Native.None
let bound_after_external (bound : Prims.string Prims.list)
  (external_node : Parser_XML.xml_node) : Prims.string Prims.list=
  match external_op_and_args external_node with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some (local, args) ->
      let allowed = builtin_binding_patterns local in
      let actual = args_availability bound args in
      try_patterns allowed args actual
let bound_after_equal (bound : Prims.string Prims.list)
  (equal_node : Parser_XML.xml_node) : Prims.string Prims.list=
  match equal_node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      (match ((Parser_RIFXML.first_child_with_local_name "left" children),
               (Parser_RIFXML.first_child_with_local_name "right" children))
       with
       | (FStar_Pervasives_Native.Some l_host, FStar_Pervasives_Native.Some
          r_host) ->
           (match ((Parser_RIFXML.child_elements_only
                      (Parser_XML.element_children l_host)),
                    (Parser_RIFXML.child_elements_only
                       (Parser_XML.element_children r_host)))
            with
            | (l::[], r::[]) ->
                let lb = arg_availability bound l in
                let rb = arg_availability bound r in
                (match (lb, rb) with
                 | (BP_B, BP_U) ->
                     (match var_name_of r with
                      | FStar_Pervasives_Native.Some n -> [n]
                      | FStar_Pervasives_Native.None -> [])
                 | (BP_U, BP_B) ->
                     (match var_name_of l with
                      | FStar_Pervasives_Native.Some n -> [n]
                      | FStar_Pervasives_Native.None -> [])
                 | (uu___2, uu___3) -> [])
            | (uu___2, uu___3) -> [])
       | (uu___2, uu___3) -> [])
  | uu___ -> []
let rec bound_closure (n : Parser_XML.xml_node)
  (bound : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then bound
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if Parser_RIFXML.is_body_wrapper_tag tag
         then
           (match Parser_RIFXML.child_elements_only children with
            | [] -> bound
            | first::uu___2 ->
                bound_closure first bound (fuel - Prims.int_one))
         else
           if Parser_RIFXML.is_atom_tag tag
           then
             dedup_strings
               (FStar_List_Tot_Base.append bound
                  (collect_all_vars n conformance_fuel))
           else
             if Parser_RIFXML.tag_is "And" tag
             then
               and_fixpoint (Parser_RIFXML.child_elements_only children)
                 bound (fuel - Prims.int_one)
             else
               if Parser_RIFXML.tag_is "Or" tag
               then
                 or_intersection (Parser_RIFXML.child_elements_only children)
                   bound (fuel - Prims.int_one)
               else
                 if Parser_RIFXML.tag_is "Exists" tag
                 then
                   (match Parser_RIFXML.first_child_with_local_name "formula"
                            children
                    with
                    | FStar_Pervasives_Native.Some f ->
                        bound_closure f bound (fuel - Prims.int_one)
                    | FStar_Pervasives_Native.None ->
                        (match Parser_RIFXML.child_elements_only children
                         with
                         | [] -> bound
                         | cs ->
                             (match FStar_List_Tot_Base.filter
                                      (fun c ->
                                         match c with
                                         | Parser_XML.XElement
                                             (t, uu___6, uu___7) ->
                                             Prims.op_Negation
                                               (Parser_RIFXML.tag_is
                                                  "declare" t)
                                         | uu___6 -> false) cs
                              with
                              | f::uu___6 ->
                                  bound_closure f bound
                                    (fuel - Prims.int_one)
                              | [] -> bound)))
                 else
                   if Parser_RIFXML.tag_is "External" tag
                   then
                     dedup_strings
                       (FStar_List_Tot_Base.append bound
                          (bound_after_external bound n))
                   else
                     if Parser_RIFXML.tag_is "Equal" tag
                     then
                       dedup_strings
                         (FStar_List_Tot_Base.append bound
                            (bound_after_equal bound n))
                     else bound
     | uu___1 -> bound)
and and_fixpoint (conjuncts : Parser_XML.xml_node Prims.list)
  (bound : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then bound
  else
    (let bound' = one_and_round conjuncts bound (fuel - Prims.int_one) in
     if
       (FStar_List_Tot_Base.length bound') =
         (FStar_List_Tot_Base.length bound)
     then bound
     else and_fixpoint conjuncts bound' (fuel - Prims.int_one))
and one_and_round (conjuncts : Parser_XML.xml_node Prims.list)
  (bound : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then bound
  else
    (match conjuncts with
     | [] -> bound
     | c::rest ->
         let bound' = bound_closure c bound (fuel - Prims.int_one) in
         one_and_round rest bound' (fuel - Prims.int_one))
and or_intersection (branches : Parser_XML.xml_node Prims.list)
  (bound : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then bound
  else
    (match branches with
     | [] -> bound
     | b0::rest ->
         let first_result = bound_closure b0 bound (fuel - Prims.int_one) in
         intersect_rest bound rest first_result (fuel - Prims.int_one))
and intersect_rest (bound : Prims.string Prims.list)
  (bs : Parser_XML.xml_node Prims.list) (acc : Prims.string Prims.list)
  (fuel : Prims.nat) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then acc
  else
    (match bs with
     | [] -> acc
     | b::more ->
         let br = bound_closure b bound (fuel - Prims.int_one) in
         intersect_rest bound more
           (FStar_List_Tot_Base.filter
              (fun x -> FStar_List_Tot_Base.mem x br) acc)
           (fuel - Prims.int_one))
let rec check_sentence (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if
           (Parser_RIFXML.tag_is "sentence" tag) ||
             (Parser_RIFXML.tag_is "formula" tag)
         then
           (match Parser_RIFXML.child_elements_only children with
            | [] -> true
            | first::uu___2 -> check_sentence first (fuel - Prims.int_one))
         else
           if Parser_RIFXML.tag_is "Forall" tag
           then
             (match Parser_RIFXML.first_child_with_local_name "formula"
                      children
              with
              | FStar_Pervasives_Native.Some f ->
                  check_sentence f (fuel - Prims.int_one)
              | FStar_Pervasives_Native.None ->
                  (match Parser_RIFXML.first_child_with_local_name "Implies"
                           children
                   with
                   | FStar_Pervasives_Native.Some imp ->
                       check_sentence imp (fuel - Prims.int_one)
                   | FStar_Pervasives_Native.None -> true))
           else
             if Parser_RIFXML.tag_is "Implies" tag
             then
               (match ((Parser_RIFXML.find_first_named ["if"; "body"]
                          children),
                        (Parser_RIFXML.find_first_named ["then"; "head"]
                           children))
                with
                | (FStar_Pervasives_Native.Some body_node,
                   FStar_Pervasives_Native.Some head_node) ->
                    let bound = bound_closure body_node [] conformance_fuel in
                    let head_vars =
                      dedup_strings
                        (collect_all_vars head_node conformance_fuel) in
                    let body_vars =
                      dedup_strings
                        (collect_all_vars body_node conformance_fuel) in
                    (list_subset head_vars bound) &&
                      (list_subset body_vars bound)
                | (uu___4, uu___5) -> false)
             else
               if Parser_RIFXML.is_atom_tag tag
               then Prims.uu___is_Nil (collect_all_vars n conformance_fuel)
               else true
     | uu___1 -> true)
let rec all_sentences_safe (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if Parser_RIFXML.tag_is "Group" tag
         then
           all_sentences_safe_list
             (Parser_RIFXML.child_elements_only children)
             (fuel - Prims.int_one)
         else
           if Parser_RIFXML.tag_is "payload" tag
           then
             all_sentences_safe_list
               (Parser_RIFXML.child_elements_only children)
               (fuel - Prims.int_one)
           else
             if Parser_RIFXML.tag_is "Document" tag
             then
               all_sentences_safe_list
                 (Parser_RIFXML.child_elements_only children)
                 (fuel - Prims.int_one)
             else
               if Parser_RIFXML.tag_is "sentence" tag
               then check_sentence n conformance_fuel
               else true
     | uu___1 -> true)
and all_sentences_safe_list (children : Parser_XML.xml_node Prims.list)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (match children with
     | [] -> true
     | c::rest ->
         (all_sentences_safe c (fuel - Prims.int_one)) &&
           (all_sentences_safe_list rest (fuel - Prims.int_one)))
let check_document_safe (root : Parser_XML.xml_node) : Prims.bool=
  (no_free_variables root) && (all_sentences_safe root conformance_fuel)
let rec has_variable_frame_property (n : Parser_XML.xml_node)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if Parser_RIFXML.tag_is "slot" tag
         then
           (match Parser_RIFXML.child_elements_only children with
            | key::uu___2 ->
                (match key with
                 | Parser_XML.XElement (kt, uu___3, uu___4) ->
                     Parser_RIFXML.tag_is "Var" kt
                 | uu___3 -> false)
            | [] -> false) ||
             (has_variable_frame_property_list children
                (fuel - Prims.int_one))
         else
           has_variable_frame_property_list children (fuel - Prims.int_one)
     | uu___1 -> false)
and has_variable_frame_property_list
  (children : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match children with
     | [] -> false
     | c::rest ->
         (has_variable_frame_property c (fuel - Prims.int_one)) ||
           (has_variable_frame_property_list rest (fuel - Prims.int_one)))
let rif_iri_datatype : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2007/rif#iri"
let rdf_plainliteral_datatype : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"
let triple_has_forbidden_datatype (t : RDF_Graph_Executable.triple) :
  Prims.bool=
  match t.RDF_Graph_Executable.o with
  | RDF_Graph_Executable.T_Literal l ->
      (l.RDF_Graph_Executable.datatype = rif_iri_datatype) ||
        (l.RDF_Graph_Executable.datatype = rdf_plainliteral_datatype)
  | uu___ -> false
let graph_has_forbidden_rif_datatype
  (g : RDF_Graph_Executable.triple Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb triple_has_forbidden_datatype g
let profile_rank (p : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  if p = "http://www.w3.org/ns/entailment/Simple"
  then FStar_Pervasives_Native.Some Prims.int_zero
  else
    if p = "http://www.w3.org/ns/entailment/RDF"
    then FStar_Pervasives_Native.Some Prims.int_one
    else
      if p = "http://www.w3.org/ns/entailment/RDFS"
      then FStar_Pervasives_Native.Some (Prims.of_int (2))
      else FStar_Pervasives_Native.None
let profiles_comparable (p1 : Prims.string) (p2 : Prims.string) : Prims.bool=
  if p1 = p2
  then true
  else
    (match ((profile_rank p1), (profile_rank p2)) with
     | (FStar_Pervasives_Native.Some uu___1, FStar_Pervasives_Native.Some
        uu___2) -> true
     | (uu___1, uu___2) -> false)
let rec has_incomparable_profile_pair (profiles : Prims.string Prims.list) :
  Prims.bool=
  match profiles with
  | [] -> false
  | p::rest ->
      (FStar_List_Tot_Base.existsb
         (fun q -> Prims.op_Negation (profiles_comparable p q)) rest)
        || (has_incomparable_profile_pair rest)
let imported_graph_is_empty (g : RDF_Graph_Executable.triple Prims.list) :
  Prims.bool= Prims.uu___is_Nil g
