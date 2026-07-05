open Prims
let shex_starts_with (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  let pl = FStar_String.strlen pfx in
  let sl = FStar_String.strlen s in
  (sl >= pl) && ((FStar_String.sub s Prims.int_zero pl) = pfx)
let lang_range_matches (tag : Prims.string) (range : Prims.string) :
  Prims.bool=
  if range = ""
  then true
  else
    (let tag_l = FStar_String.lowercase tag in
     let range_l = FStar_String.lowercase range in
     if tag_l = range_l
     then true
     else
       (let rl = FStar_String.strlen range_l in
        let tl = FStar_String.strlen tag_l in
        ((tl > rl) && ((FStar_String.sub tag_l Prims.int_zero rl) = range_l))
          && ((FStar_String.sub tag_l rl Prims.int_one) = "-")))
let shex_lex (t : RDF_Graph_Executable.rdf_term) : Prims.string=
  match t with
  | RDF_Graph_Executable.T_IRI i -> i
  | RDF_Graph_Executable.T_BNode b -> b
  | RDF_Graph_Executable.T_Literal l -> l.RDF_Graph_Executable.lexical_form
let is_ascii_digit_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let rec chars_before_dot (chars : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match chars with
  | [] -> []
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (46))
      then []
      else c :: (chars_before_dot rest)
let rec chars_after_dot (chars : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (46))
      then FStar_Pervasives_Native.Some rest
      else chars_after_dot rest
let rec strip_leading_zeros (chars : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match chars with
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (48))
      then strip_leading_zeros rest
      else chars
  | [] -> []
let rec strip_trailing_zeros_fuel (chars : FStar_Char.char Prims.list)
  (fuel : Prims.nat) : FStar_Char.char Prims.list=
  if fuel = Prims.int_zero
  then chars
  else
    (match FStar_List_Tot_Base.rev chars with
     | [] -> []
     | c::rest ->
         if (FStar_Char.int_of_char c) = (Prims.of_int (48))
         then
           strip_trailing_zeros_fuel (FStar_List_Tot_Base.rev rest)
             (fuel - Prims.int_one)
         else chars)
let total_digit_count (s : Prims.string) : Prims.nat=
  let chars = FStar_String.list_of_string s in
  let before = strip_leading_zeros (chars_before_dot chars) in
  let after =
    match chars_after_dot chars with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some frac ->
        strip_trailing_zeros_fuel frac (FStar_List_Tot_Base.length frac) in
  (FStar_List_Tot_Base.length
     (FStar_List_Tot_Base.filter is_ascii_digit_char before))
    +
    (FStar_List_Tot_Base.length
       (FStar_List_Tot_Base.filter is_ascii_digit_char after))
let fraction_digit_count (s : Prims.string) : Prims.nat=
  match chars_after_dot (FStar_String.list_of_string s) with
  | FStar_Pervasives_Native.None -> Prims.int_zero
  | FStar_Pervasives_Native.Some frac ->
      let trimmed =
        strip_trailing_zeros_fuel frac (FStar_List_Tot_Base.length frac) in
      FStar_List_Tot_Base.length
        (FStar_List_Tot_Base.filter is_ascii_digit_char trimmed)
let shex_numeric_le (a : Prims.string) (b : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option=
  match ((XSD_Datatypes.parse_double_to_scaled a),
          (XSD_Datatypes.parse_double_to_scaled b))
  with
  | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
      FStar_Pervasives_Native.Some
        ((XSD_Datatypes.scaled_cmp sa sb) <= Prims.int_zero)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let shex_numeric_lt (a : Prims.string) (b : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option=
  match ((XSD_Datatypes.parse_double_to_scaled a),
          (XSD_Datatypes.parse_double_to_scaled b))
  with
  | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
      FStar_Pervasives_Native.Some
        ((XSD_Datatypes.scaled_cmp sa sb) < Prims.int_zero)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let shex_node_kind_ok (nk : ShEx_Schema.shex_node_kind)
  (t : RDF_Graph_Executable.rdf_term) : Prims.bool=
  match (nk, t) with
  | (ShEx_Schema.ShexNK_Iri, RDF_Graph_Executable.T_IRI uu___) -> true
  | (ShEx_Schema.ShexNK_BNode, RDF_Graph_Executable.T_BNode uu___) -> true
  | (ShEx_Schema.ShexNK_NonLiteral, RDF_Graph_Executable.T_IRI uu___) -> true
  | (ShEx_Schema.ShexNK_NonLiteral, RDF_Graph_Executable.T_BNode uu___) ->
      true
  | (ShEx_Schema.ShexNK_Literal, RDF_Graph_Executable.T_Literal uu___) ->
      true
  | (uu___, uu___1) -> false
let shex_datatype_ok (dt : Prims.string) (t : RDF_Graph_Executable.rdf_term)
  : Prims.bool=
  match t with
  | RDF_Graph_Executable.T_Literal l ->
      (l.RDF_Graph_Executable.datatype = dt) &&
        (if RDF_Graph_Executable.is_iri dt
         then
           Prims.op_Negation
             (XSD_Datatypes.literal_ill_formed dt
                l.RDF_Graph_Executable.lexical_form)
         else true)
  | uu___ -> false
let stem_matches (st : ShEx_Schema.shex_stem) (s : Prims.string) :
  Prims.bool=
  match st with
  | ShEx_Schema.ShexStemWildcard -> true
  | ShEx_Schema.ShexStemPlain pfx -> shex_starts_with s pfx
let object_value_matches (ov : ShEx_Schema.shex_object_value)
  (t : RDF_Graph_Executable.rdf_term) : Prims.bool=
  match (ov, t) with
  | (ShEx_Schema.ShexOV_Iri i, RDF_Graph_Executable.T_IRI ti) -> i = ti
  | (ShEx_Schema.ShexOV_Literal (value, lang, dt),
     RDF_Graph_Executable.T_Literal l) ->
      (l.RDF_Graph_Executable.lexical_form = value) &&
        ((match lang with
          | FStar_Pervasives_Native.Some lg ->
              if lg = ""
              then
                FStar_Pervasives_Native.uu___is_None
                  l.RDF_Graph_Executable.lang_tag
              else
                (match l.RDF_Graph_Executable.lang_tag with
                 | FStar_Pervasives_Native.Some tlg ->
                     RDF_Graph_Executable.lang_tag_eq lg tlg
                 | FStar_Pervasives_Native.None -> false)
          | FStar_Pervasives_Native.None ->
              (match dt with
               | FStar_Pervasives_Native.Some d ->
                   (l.RDF_Graph_Executable.datatype = d) &&
                     (FStar_Pervasives_Native.uu___is_None
                        l.RDF_Graph_Executable.lang_tag)
               | FStar_Pervasives_Native.None ->
                   (l.RDF_Graph_Executable.datatype =
                      RDF_Graph_Executable.xsd_string)
                     &&
                     (FStar_Pervasives_Native.uu___is_None
                        l.RDF_Graph_Executable.lang_tag))))
  | (uu___, uu___1) -> false
let rec vsv_size (v : ShEx_Schema.shex_value_set_value) : Prims.nat=
  match v with
  | ShEx_Schema.VSV_IriStemRange (uu___, excl) ->
      Prims.int_one + (vsv_list_size excl)
  | ShEx_Schema.VSV_LiteralStemRange (uu___, excl) ->
      Prims.int_one + (vsv_list_size excl)
  | ShEx_Schema.VSV_LanguageStemRange (uu___, excl) ->
      Prims.int_one + (vsv_list_size excl)
  | uu___ -> Prims.int_one
and vsv_list_size (l : ShEx_Schema.shex_value_set_value Prims.list) :
  Prims.nat=
  match l with
  | [] -> Prims.int_zero
  | hd::tl -> (Prims.int_one + (vsv_size hd)) + (vsv_list_size tl)
let rec vsv_matches (vsv : ShEx_Schema.shex_value_set_value)
  (t : RDF_Graph_Executable.rdf_term) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let fuel' = fuel - Prims.int_one in
     match vsv with
     | ShEx_Schema.VSV_Value ov -> object_value_matches ov t
     | ShEx_Schema.VSV_IriStem st ->
         (match t with
          | RDF_Graph_Executable.T_IRI i -> stem_matches st i
          | uu___1 -> false)
     | ShEx_Schema.VSV_IriStemRange (st, excl) ->
         (match t with
          | RDF_Graph_Executable.T_IRI i ->
              (stem_matches st i) &&
                (Prims.op_Negation (vsv_list_exists excl t fuel'))
          | uu___1 -> false)
     | ShEx_Schema.VSV_LiteralStem st ->
         (match t with
          | RDF_Graph_Executable.T_Literal l ->
              stem_matches st l.RDF_Graph_Executable.lexical_form
          | uu___1 -> false)
     | ShEx_Schema.VSV_LiteralStemRange (st, excl) ->
         (match t with
          | RDF_Graph_Executable.T_Literal l ->
              (stem_matches st l.RDF_Graph_Executable.lexical_form) &&
                (Prims.op_Negation (vsv_list_exists excl t fuel'))
          | uu___1 -> false)
     | ShEx_Schema.VSV_Language lt ->
         (match t with
          | RDF_Graph_Executable.T_Literal l ->
              (match l.RDF_Graph_Executable.lang_tag with
               | FStar_Pervasives_Native.Some tag ->
                   RDF_Graph_Executable.lang_tag_eq lt tag
               | FStar_Pervasives_Native.None -> false)
          | uu___1 -> false)
     | ShEx_Schema.VSV_LanguageStem st ->
         (match t with
          | RDF_Graph_Executable.T_Literal l ->
              (match l.RDF_Graph_Executable.lang_tag with
               | FStar_Pervasives_Native.Some tag ->
                   (match st with
                    | ShEx_Schema.ShexStemWildcard -> true
                    | ShEx_Schema.ShexStemPlain s -> lang_range_matches tag s)
               | FStar_Pervasives_Native.None -> false)
          | uu___1 -> false)
     | ShEx_Schema.VSV_LanguageStemRange (st, excl) ->
         (match t with
          | RDF_Graph_Executable.T_Literal l ->
              (match l.RDF_Graph_Executable.lang_tag with
               | FStar_Pervasives_Native.Some tag ->
                   let base_ok =
                     match st with
                     | ShEx_Schema.ShexStemWildcard -> true
                     | ShEx_Schema.ShexStemPlain s ->
                         lang_range_matches tag s in
                   base_ok &&
                     (Prims.op_Negation (vsv_list_exists excl t fuel'))
               | FStar_Pervasives_Native.None -> false)
          | uu___1 -> false))
and vsv_list_exists (items : ShEx_Schema.shex_value_set_value Prims.list)
  (t : RDF_Graph_Executable.rdf_term) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match items with
     | [] -> false
     | hd::tl ->
         if vsv_matches hd t (fuel - Prims.int_one)
         then true
         else vsv_list_exists tl t (fuel - Prims.int_one))
let values_ok (values : ShEx_Schema.shex_value_set_value Prims.list)
  (t : RDF_Graph_Executable.rdf_term) : Prims.bool=
  if Prims.uu___is_Nil values
  then true
  else vsv_list_exists values t (Prims.int_one + (vsv_list_size values))
let node_constraint_matches (nc : ShEx_Schema.shex_node_constraint)
  (t : RDF_Graph_Executable.rdf_term) : Prims.bool=
  let nk_ok =
    match nc.ShEx_Schema.nc_node_kind with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some nk -> shex_node_kind_ok nk t in
  let dt_ok =
    match nc.ShEx_Schema.nc_datatype with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some dt -> shex_datatype_ok dt t in
  let vs_ok = values_ok nc.ShEx_Schema.nc_values t in
  let lex = shex_lex t in
  let length_ok =
    match nc.ShEx_Schema.nc_length with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some n -> (FStar_String.strlen lex) = n in
  let minlength_ok =
    match nc.ShEx_Schema.nc_minlength with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some n -> (FStar_String.strlen lex) >= n in
  let maxlength_ok =
    match nc.ShEx_Schema.nc_maxlength with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some n -> (FStar_String.strlen lex) <= n in
  let flags_opt =
    match nc.ShEx_Schema.nc_flags with
    | FStar_Pervasives_Native.Some "" -> FStar_Pervasives_Native.None
    | f -> f in
  let pattern_ok =
    match nc.ShEx_Schema.nc_pattern with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some re ->
        SPARQL11_Algebra.regex_match lex re flags_opt in
  let num_lex =
    match t with
    | RDF_Graph_Executable.T_Literal l ->
        FStar_Pervasives_Native.Some (l.RDF_Graph_Executable.lexical_form)
    | uu___ -> FStar_Pervasives_Native.None in
  let digits_lex =
    match t with
    | RDF_Graph_Executable.T_Literal l ->
        if
          (XSD_Datatypes.is_decimal_derived_datatype
             l.RDF_Graph_Executable.datatype)
            &&
            (Prims.op_Negation
               (XSD_Datatypes.literal_ill_formed
                  l.RDF_Graph_Executable.datatype
                  l.RDF_Graph_Executable.lexical_form))
        then
          FStar_Pervasives_Native.Some (l.RDF_Graph_Executable.lexical_form)
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None in
  let mininclusive_ok =
    match ((nc.ShEx_Schema.nc_mininclusive), num_lex) with
    | (FStar_Pervasives_Native.None, uu___) -> true
    | (FStar_Pervasives_Native.Some facet, FStar_Pervasives_Native.Some nlex)
        -> (shex_numeric_le facet nlex) = (FStar_Pervasives_Native.Some true)
    | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
        false in
  let maxinclusive_ok =
    match ((nc.ShEx_Schema.nc_maxinclusive), num_lex) with
    | (FStar_Pervasives_Native.None, uu___) -> true
    | (FStar_Pervasives_Native.Some facet, FStar_Pervasives_Native.Some nlex)
        -> (shex_numeric_le nlex facet) = (FStar_Pervasives_Native.Some true)
    | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
        false in
  let minexclusive_ok =
    match ((nc.ShEx_Schema.nc_minexclusive), num_lex) with
    | (FStar_Pervasives_Native.None, uu___) -> true
    | (FStar_Pervasives_Native.Some facet, FStar_Pervasives_Native.Some nlex)
        -> (shex_numeric_lt facet nlex) = (FStar_Pervasives_Native.Some true)
    | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
        false in
  let maxexclusive_ok =
    match ((nc.ShEx_Schema.nc_maxexclusive), num_lex) with
    | (FStar_Pervasives_Native.None, uu___) -> true
    | (FStar_Pervasives_Native.Some facet, FStar_Pervasives_Native.Some nlex)
        -> (shex_numeric_lt nlex facet) = (FStar_Pervasives_Native.Some true)
    | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
        false in
  let totaldigits_ok =
    match ((nc.ShEx_Schema.nc_totaldigits), digits_lex) with
    | (FStar_Pervasives_Native.None, uu___) -> true
    | (FStar_Pervasives_Native.Some n, FStar_Pervasives_Native.Some nlex) ->
        (total_digit_count nlex) <= n
    | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
        false in
  let fractiondigits_ok =
    match ((nc.ShEx_Schema.nc_fractiondigits), digits_lex) with
    | (FStar_Pervasives_Native.None, uu___) -> true
    | (FStar_Pervasives_Native.Some n, FStar_Pervasives_Native.Some nlex) ->
        (fraction_digit_count nlex) <= n
    | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
        false in
  (((((((((((nk_ok && dt_ok) && vs_ok) && length_ok) && minlength_ok) &&
           maxlength_ok)
          && pattern_ok)
         && mininclusive_ok)
        && maxinclusive_ok)
       && minexclusive_ok)
      && maxexclusive_ok)
     && totaldigits_ok)
    && fractiondigits_ok
let shex_test_extension_iri : Prims.string= "http://shex.io/extensions/Test/"
let rec shex_list_has_prefix (l : FStar_Char.char Prims.list)
  (pfx : FStar_Char.char Prims.list) : Prims.bool=
  match pfx with
  | [] -> true
  | pc::ptl ->
      (match l with
       | [] -> false
       | lc::ltl -> (pc = lc) && (shex_list_has_prefix ltl ptl))
let rec shex_list_contains_sub (l : FStar_Char.char Prims.list)
  (sub : FStar_Char.char Prims.list) : Prims.bool=
  if shex_list_has_prefix l sub
  then true
  else
    (match l with | [] -> false | uu___1::tl -> shex_list_contains_sub tl sub)
let shex_string_contains (s : Prims.string) (sub : Prims.string) :
  Prims.bool=
  shex_list_contains_sub (FStar_String.list_of_string s)
    (FStar_String.list_of_string sub)
let semact_says_fail (sa : ShEx_Schema.shex_sem_act) : Prims.bool=
  (sa.ShEx_Schema.sa_name = shex_test_extension_iri) &&
    (match sa.ShEx_Schema.sa_code with
     | FStar_Pervasives_Native.Some code -> shex_string_contains code "fail("
     | FStar_Pervasives_Native.None -> false)
let rec any_semact_fails (l : ShEx_Schema.shex_sem_act Prims.list) :
  Prims.bool=
  match l with
  | [] -> false
  | hd::tl -> (semact_says_fail hd) || (any_semact_fails tl)
type shex_visited = (Prims.string * RDF_Graph_Executable.rdf_term) Prims.list
let visited_mem (label : Prims.string) (t : RDF_Graph_Executable.rdf_term)
  (v : shex_visited) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun entry ->
       ((FStar_Pervasives_Native.fst entry) = label) &&
         (RDF_Graph_Executable.rdf_term_eq
            (FStar_Pervasives_Native.snd entry) t)) v
let rec lookup_shape_decl (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (label : Prims.string) :
  ShEx_Schema.shex_shape_decl FStar_Pervasives_Native.option=
  match decls with
  | [] -> FStar_Pervasives_Native.None
  | hd::tl ->
      if hd.ShEx_Schema.sd_id = label
      then FStar_Pervasives_Native.Some hd
      else lookup_shape_decl tl label
let rec se_collect_ids (se : ShEx_Schema.shex_shape_expr) :
  (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list=
  match se with
  | ShEx_Schema.SE_Ref uu___ -> []
  | ShEx_Schema.SE_ShapeAnd ses -> se_collect_ids_list ses
  | ShEx_Schema.SE_ShapeOr ses -> se_collect_ids_list ses
  | ShEx_Schema.SE_ShapeNot se' -> se_collect_ids se'
  | ShEx_Schema.SE_NodeConstraint uu___ -> []
  | ShEx_Schema.SE_ShapeExternal -> []
  | ShEx_Schema.SE_Shape sh ->
      (match sh.ShEx_Schema.sh_expression with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some te -> te_collect_ids te)
and se_collect_ids_list (ses : ShEx_Schema.shex_shape_expr Prims.list) :
  (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list=
  match ses with
  | [] -> []
  | hd::tl ->
      FStar_List_Tot_Base.op_At (se_collect_ids hd) (se_collect_ids_list tl)
and te_collect_ids (te : ShEx_Schema.shex_triple_expr) :
  (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list=
  match te with
  | ShEx_Schema.TE_Ref uu___ -> []
  | ShEx_Schema.TE_TripleConstraint tc ->
      let self =
        match tc.ShEx_Schema.tc_id with
        | FStar_Pervasives_Native.Some id -> [(id, te)]
        | FStar_Pervasives_Native.None -> [] in
      let inner =
        match tc.ShEx_Schema.tc_value_expr with
        | FStar_Pervasives_Native.Some se -> se_collect_ids se
        | FStar_Pervasives_Native.None -> [] in
      FStar_List_Tot_Base.op_At self inner
  | ShEx_Schema.TE_EachOf grp ->
      let self =
        match grp.ShEx_Schema.gr_id with
        | FStar_Pervasives_Native.Some id -> [(id, te)]
        | FStar_Pervasives_Native.None -> [] in
      FStar_List_Tot_Base.op_At self
        (te_collect_ids_list grp.ShEx_Schema.gr_expressions)
  | ShEx_Schema.TE_OneOf grp ->
      let self =
        match grp.ShEx_Schema.gr_id with
        | FStar_Pervasives_Native.Some id -> [(id, te)]
        | FStar_Pervasives_Native.None -> [] in
      FStar_List_Tot_Base.op_At self
        (te_collect_ids_list grp.ShEx_Schema.gr_expressions)
and te_collect_ids_list (tes : ShEx_Schema.shex_triple_expr Prims.list) :
  (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list=
  match tes with
  | [] -> []
  | hd::tl ->
      FStar_List_Tot_Base.op_At (te_collect_ids hd) (te_collect_ids_list tl)
let rec shape_decl_list_collect_ids
  (decls : ShEx_Schema.shex_shape_decl Prims.list) :
  (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list=
  match decls with
  | [] -> []
  | hd::tl ->
      FStar_List_Tot_Base.op_At (se_collect_ids hd.ShEx_Schema.sd_expr)
        (shape_decl_list_collect_ids tl)
let rec lookup_te_id
  (tab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (id : Prims.string) :
  ShEx_Schema.shex_triple_expr FStar_Pervasives_Native.option=
  match tab with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::tl ->
      if k = id then FStar_Pervasives_Native.Some v else lookup_te_id tl id
type extends_flat =
  {
  ef_tes: ShEx_Schema.shex_triple_expr Prims.list ;
  ef_extra: Prims.string Prims.list ;
  ef_closed: Prims.bool ;
  ef_checks: ShEx_Schema.shex_shape_expr Prims.list }
let __proj__Mkextends_flat__item__ef_tes (projectee : extends_flat) :
  ShEx_Schema.shex_triple_expr Prims.list=
  match projectee with
  | { ef_tes; ef_extra; ef_closed; ef_checks;_} -> ef_tes
let __proj__Mkextends_flat__item__ef_extra (projectee : extends_flat) :
  Prims.string Prims.list=
  match projectee with
  | { ef_tes; ef_extra; ef_closed; ef_checks;_} -> ef_extra
let __proj__Mkextends_flat__item__ef_closed (projectee : extends_flat) :
  Prims.bool=
  match projectee with
  | { ef_tes; ef_extra; ef_closed; ef_checks;_} -> ef_closed
let __proj__Mkextends_flat__item__ef_checks (projectee : extends_flat) :
  ShEx_Schema.shex_shape_expr Prims.list=
  match projectee with
  | { ef_tes; ef_extra; ef_closed; ef_checks;_} -> ef_checks
let ef_empty : extends_flat=
  { ef_tes = []; ef_extra = []; ef_closed = false; ef_checks = [] }
let ef_combine (a : extends_flat) (b : extends_flat) : extends_flat=
  {
    ef_tes = (FStar_List_Tot_Base.op_At a.ef_tes b.ef_tes);
    ef_extra = (FStar_List_Tot_Base.op_At a.ef_extra b.ef_extra);
    ef_closed = (a.ef_closed || b.ef_closed);
    ef_checks = (FStar_List_Tot_Base.op_At a.ef_checks b.ef_checks)
  }
let rec flatten_se_for_extends
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (se : ShEx_Schema.shex_shape_expr) (visited : Prims.string Prims.list)
  (fuel : Prims.nat) :
  (extends_flat * Prims.string Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match se with
     | ShEx_Schema.SE_Shape sh ->
         let own_tes =
           match sh.ShEx_Schema.sh_expression with
           | FStar_Pervasives_Native.Some te -> [te]
           | FStar_Pervasives_Native.None -> [] in
         if Prims.uu___is_Nil sh.ShEx_Schema.sh_extends
         then
           FStar_Pervasives_Native.Some
             ({
                ef_tes = own_tes;
                ef_extra = (sh.ShEx_Schema.sh_extra);
                ef_closed = (sh.ShEx_Schema.sh_closed);
                ef_checks = []
              }, visited)
         else
           (match resolve_extends decls sh.ShEx_Schema.sh_extends visited
                    fuel'
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (parent, visited1) ->
                FStar_Pervasives_Native.Some
                  ((ef_combine
                      {
                        ef_tes = own_tes;
                        ef_extra = (sh.ShEx_Schema.sh_extra);
                        ef_closed = (sh.ShEx_Schema.sh_closed);
                        ef_checks = []
                      } parent), visited1))
     | ShEx_Schema.SE_ShapeAnd ses ->
         flatten_se_list_for_extends decls ses visited fuel'
     | ShEx_Schema.SE_Ref label ->
         if FStar_List_Tot_Base.mem label visited
         then FStar_Pervasives_Native.Some (ef_empty, visited)
         else
           (match lookup_shape_decl decls label with
            | FStar_Pervasives_Native.Some sd ->
                flatten_se_for_extends decls sd.ShEx_Schema.sd_expr (label ::
                  visited) fuel'
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ShEx_Schema.SE_NodeConstraint uu___1 ->
         FStar_Pervasives_Native.Some
           ({
              ef_tes = (ef_empty.ef_tes);
              ef_extra = (ef_empty.ef_extra);
              ef_closed = (ef_empty.ef_closed);
              ef_checks = [se]
            }, visited)
     | ShEx_Schema.SE_ShapeOr uu___1 ->
         FStar_Pervasives_Native.Some
           ({
              ef_tes = (ef_empty.ef_tes);
              ef_extra = (ef_empty.ef_extra);
              ef_closed = (ef_empty.ef_closed);
              ef_checks = [se]
            }, visited)
     | ShEx_Schema.SE_ShapeNot uu___1 ->
         FStar_Pervasives_Native.Some
           ({
              ef_tes = (ef_empty.ef_tes);
              ef_extra = (ef_empty.ef_extra);
              ef_closed = (ef_empty.ef_closed);
              ef_checks = [se]
            }, visited)
     | ShEx_Schema.SE_ShapeExternal ->
         FStar_Pervasives_Native.Some
           ({
              ef_tes = (ef_empty.ef_tes);
              ef_extra = (ef_empty.ef_extra);
              ef_closed = (ef_empty.ef_closed);
              ef_checks = [se]
            }, visited))
and flatten_se_list_for_extends
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (ses : ShEx_Schema.shex_shape_expr Prims.list)
  (visited : Prims.string Prims.list) (fuel : Prims.nat) :
  (extends_flat * Prims.string Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match ses with
     | [] -> FStar_Pervasives_Native.Some (ef_empty, visited)
     | hd::tl ->
         (match flatten_se_for_extends decls hd visited fuel' with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (a, visited1) ->
              (match flatten_se_list_for_extends decls tl visited1 fuel' with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (b, visited2) ->
                   FStar_Pervasives_Native.Some ((ef_combine a b), visited2))))
and resolve_extends (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (labels : Prims.string Prims.list) (visited : Prims.string Prims.list)
  (fuel : Prims.nat) :
  (extends_flat * Prims.string Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match labels with
     | [] -> FStar_Pervasives_Native.Some (ef_empty, visited)
     | hd::tl ->
         if FStar_List_Tot_Base.mem hd visited
         then resolve_extends decls tl visited fuel'
         else
           (match lookup_shape_decl decls hd with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some sd ->
                (match flatten_se_for_extends decls sd.ShEx_Schema.sd_expr
                         (hd :: visited) fuel'
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (a, visited1) ->
                     (match resolve_extends decls tl visited1 fuel' with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (b, visited2) ->
                          FStar_Pervasives_Native.Some
                            ((ef_combine a b), visited2)))))
let shex_gather_candidates (g : RDF_Graph_Executable.rdf_graph)
  (focus : RDF_Graph_Executable.rdf_term) (inverse : Prims.bool)
  (pred : Prims.string) : RDF_Graph_Executable.rdf_term Prims.list=
  if Prims.op_Negation (RDF_Graph_Executable.is_iri pred)
  then []
  else
    if inverse
    then
      FStar_List_Tot_Base.map RDF_Graph_Executable.subject_to_term
        (RDF_Graph_Executable.find_subjects g pred focus)
    else
      (match RDF_Graph_Executable.term_to_subject focus with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some s ->
           RDF_Graph_Executable.find_objects g s pred)
let triples_with_subject (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) :
  RDF_Graph_Executable.triple Prims.list=
  FStar_List_Tot_Base.filter
    (fun tr -> RDF_Graph_Executable.subject_eq tr.RDF_Graph_Executable.s s) g
type pool_elem = (Prims.bool * Prims.string * RDF_Graph_Executable.rdf_term)
type pool_t = pool_elem Prims.list
let pool_elem_eq (a : pool_elem) (b : pool_elem) : Prims.bool=
  let uu___ = a in
  match uu___ with
  | (ai, ap, at) ->
      let uu___1 = b in
      (match uu___1 with
       | (bi, bp, bt) ->
           ((ai = bi) && (ap = bp)) &&
             (RDF_Graph_Executable.rdf_term_eq at bt))
let rec pool_intersect (running : pool_t) (other : pool_t) : pool_t=
  match running with
  | [] -> []
  | hd::tl ->
      if FStar_List_Tot_Base.existsb (fun e -> pool_elem_eq hd e) other
      then hd :: (pool_intersect tl other)
      else pool_intersect tl other
let rec pool_diff (a : pool_t) (b : pool_t) : pool_t=
  match a with
  | [] -> []
  | hd::tl ->
      if FStar_List_Tot_Base.existsb (fun e -> pool_elem_eq hd e) b
      then pool_diff tl b
      else hd :: (pool_diff tl b)
let te_is_unbounded_tc (te : ShEx_Schema.shex_triple_expr) : Prims.bool=
  match te with
  | ShEx_Schema.TE_TripleConstraint tc ->
      tc.ShEx_Schema.tc_max = (Prims.of_int (-1))
  | uu___ -> false
let pair_mem (x : (Prims.bool * Prims.string))
  (l : (Prims.bool * Prims.string) Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun y ->
       ((FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)) &&
         ((FStar_Pervasives_Native.snd x) = (FStar_Pervasives_Native.snd y)))
    l
let rec dedup_pairs (l : (Prims.bool * Prims.string) Prims.list) :
  (Prims.bool * Prims.string) Prims.list=
  match l with
  | [] -> []
  | hd::tl ->
      if pair_mem hd tl then dedup_pairs tl else hd :: (dedup_pairs tl)
let rec gather_pool (g : RDF_Graph_Executable.rdf_graph)
  (focus : RDF_Graph_Executable.rdf_term)
  (pairs : (Prims.bool * Prims.string) Prims.list) : pool_t=
  match pairs with
  | [] -> []
  | (inv, pred)::tl ->
      let cands = shex_gather_candidates g focus inv pred in
      FStar_List_Tot_Base.op_At
        (FStar_List_Tot_Base.map (fun tm -> (inv, pred, tm)) cands)
        (gather_pool g focus tl)
let rec has_any_none
  (l : pool_t Prims.list FStar_Pervasives_Native.option Prims.list) :
  Prims.bool=
  match l with
  | [] -> false
  | (FStar_Pervasives_Native.None)::uu___ -> true
  | (FStar_Pervasives_Native.Some uu___)::tl -> has_any_none tl
let rec has_any_nonempty_some
  (l : pool_t Prims.list FStar_Pervasives_Native.option Prims.list) :
  Prims.bool=
  match l with
  | [] -> false
  | (FStar_Pervasives_Native.Some (uu___::uu___1))::uu___2 -> true
  | uu___::tl -> has_any_nonempty_some tl
let rec collect_nonempty_some
  (l : pool_t Prims.list FStar_Pervasives_Native.option Prims.list) :
  pool_t Prims.list=
  match l with
  | [] -> []
  | (FStar_Pervasives_Native.Some xs)::tl ->
      FStar_List_Tot_Base.op_At xs (collect_nonempty_some tl)
  | (FStar_Pervasives_Native.None)::tl -> collect_nonempty_some tl
let combine_oneof
  (l : pool_t Prims.list FStar_Pervasives_Native.option Prims.list) :
  pool_t Prims.list FStar_Pervasives_Native.option=
  if has_any_nonempty_some l
  then FStar_Pervasives_Native.Some (collect_nonempty_some l)
  else
    if has_any_none l
    then FStar_Pervasives_Native.None
    else FStar_Pervasives_Native.Some []
let rec pair_count (x : (Prims.bool * Prims.string))
  (l : (Prims.bool * Prims.string) Prims.list) : Prims.nat=
  match l with
  | [] -> Prims.int_zero
  | hd::tl ->
      (if
         ((FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst hd))
           &&
           ((FStar_Pervasives_Native.snd x) =
              (FStar_Pervasives_Native.snd hd))
       then Prims.int_one
       else Prims.int_zero) + (pair_count x tl)
let rec ambiguous_pairs_of (l : (Prims.bool * Prims.string) Prims.list) :
  (Prims.bool * Prims.string) Prims.list=
  match l with
  | [] -> []
  | hd::tl ->
      if (pair_count hd tl) > Prims.int_zero
      then hd :: (ambiguous_pairs_of tl)
      else ambiguous_pairs_of tl
let rec tc_pairs_of (tes : ShEx_Schema.shex_triple_expr Prims.list) :
  (Prims.bool * Prims.string) Prims.list=
  match tes with
  | [] -> []
  | (ShEx_Schema.TE_TripleConstraint tc)::tl ->
      ((tc.ShEx_Schema.tc_inverse), (tc.ShEx_Schema.tc_predicate)) ::
      (tc_pairs_of tl)
  | uu___::tl -> tc_pairs_of tl
let rec all_tc (tes : ShEx_Schema.shex_triple_expr Prims.list) : Prims.bool=
  match tes with
  | [] -> true
  | (ShEx_Schema.TE_TripleConstraint uu___)::tl -> all_tc tl
  | uu___ -> false
let rec pairs_distinct (l : (Prims.bool * Prims.string) Prims.list) :
  Prims.bool=
  match l with
  | [] -> true
  | hd::tl -> (Prims.op_Negation (pair_mem hd tl)) && (pairs_distinct tl)
let distinct_child_pairs (tes : ShEx_Schema.shex_triple_expr Prims.list) :
  Prims.bool= (all_tc tes) && (pairs_distinct (tc_pairs_of tes))
let rec all_equal_nat (l : Prims.nat Prims.list) : Prims.bool=
  match l with
  | [] -> true
  | x::tl ->
      (match tl with | [] -> true | y::uu___ -> (x = y) && (all_equal_nat tl))
let rec sum_nat (l : Prims.nat Prims.list) : Prims.nat=
  match l with | [] -> Prims.int_zero | hd::tl -> hd + (sum_nat tl)
let rec matches_shape_expr (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (se : ShEx_Schema.shex_shape_expr)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match se with
     | ShEx_Schema.SE_NodeConstraint nc ->
         FStar_Pervasives_Native.Some (node_constraint_matches nc t)
     | ShEx_Schema.SE_ShapeAnd ses ->
         matches_all decls idtab visited ses t g fuel'
     | ShEx_Schema.SE_ShapeOr ses ->
         matches_any decls idtab visited ses t g fuel'
     | ShEx_Schema.SE_ShapeNot se' ->
         (match matches_shape_expr decls idtab visited se' t g fuel' with
          | FStar_Pervasives_Native.Some b ->
              FStar_Pervasives_Native.Some (Prims.op_Negation b)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ShEx_Schema.SE_Ref label ->
         if visited_mem label t visited
         then FStar_Pervasives_Native.Some true
         else
           (match lookup_shape_decl decls label with
            | FStar_Pervasives_Native.Some sd ->
                (match matches_shape_expr decls idtab ((label, t) :: visited)
                         sd.ShEx_Schema.sd_expr t g fuel'
                 with
                 | FStar_Pervasives_Native.Some true ->
                     if sd.ShEx_Schema.sd_is_abstract
                     then
                       exists_nonabstract_descendant_satisfying decls idtab
                         visited label t g fuel'
                     else FStar_Pervasives_Native.Some true
                 | other -> other)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ShEx_Schema.SE_Shape sh ->
         matches_shape decls idtab visited sh t g fuel'
     | ShEx_Schema.SE_ShapeExternal -> FStar_Pervasives_Native.None)
and exists_nonabstract_descendant_satisfying
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (label : Prims.string)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     check_descendant_candidates decls idtab visited label decls t g fuel')
and check_descendant_candidates
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (label : Prims.string)
  (candidates : ShEx_Schema.shex_shape_decl Prims.list)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match candidates with
     | [] -> FStar_Pervasives_Native.Some false
     | cd::tl ->
         if
           cd.ShEx_Schema.sd_is_abstract ||
             (Prims.op_Negation
                (shape_decl_extends_label decls cd label [] fuel'))
         then
           check_descendant_candidates decls idtab visited label tl t g fuel'
         else
           (match ((matches_shape_expr decls idtab visited
                      cd.ShEx_Schema.sd_expr t g fuel'),
                    (check_descendant_candidates decls idtab visited label tl
                       t g fuel'))
            with
            | (FStar_Pervasives_Native.Some true, uu___2) ->
                FStar_Pervasives_Native.Some true
            | (uu___2, FStar_Pervasives_Native.Some true) ->
                FStar_Pervasives_Native.Some true
            | (FStar_Pervasives_Native.Some false,
               FStar_Pervasives_Native.Some false) ->
                FStar_Pervasives_Native.Some false
            | (uu___2, uu___3) -> FStar_Pervasives_Native.None))
and shape_decl_extends_label (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (cd : ShEx_Schema.shex_shape_decl) (label : Prims.string)
  (seen : Prims.string Prims.list) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    se_extends_label decls cd.ShEx_Schema.sd_expr label seen
      (fuel - Prims.int_one)
and se_extends_label (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (se : ShEx_Schema.shex_shape_expr) (label : Prims.string)
  (seen : Prims.string Prims.list) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let fuel' = fuel - Prims.int_one in
     match se with
     | ShEx_Schema.SE_Shape sh ->
         (FStar_List_Tot_Base.mem label sh.ShEx_Schema.sh_extends) ||
           (labels_extend_label decls sh.ShEx_Schema.sh_extends label seen
              fuel')
     | ShEx_Schema.SE_ShapeAnd ses ->
         se_list_extends_label decls ses label seen fuel'
     | uu___1 -> false)
and se_list_extends_label (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (ses : ShEx_Schema.shex_shape_expr Prims.list) (label : Prims.string)
  (seen : Prims.string Prims.list) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let fuel' = fuel - Prims.int_one in
     match ses with
     | [] -> false
     | hd::tl ->
         (se_extends_label decls hd label seen fuel') ||
           (se_list_extends_label decls tl label seen fuel'))
and labels_extend_label (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (labels : Prims.string Prims.list) (target : Prims.string)
  (seen : Prims.string Prims.list) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let fuel' = fuel - Prims.int_one in
     match labels with
     | [] -> false
     | hd::tl ->
         if hd = target
         then true
         else
           if FStar_List_Tot_Base.mem hd seen
           then labels_extend_label decls tl target seen fuel'
           else
             (match lookup_shape_decl decls hd with
              | FStar_Pervasives_Native.Some sd ->
                  (se_extends_label decls sd.ShEx_Schema.sd_expr target (hd
                     :: seen) fuel')
                    || (labels_extend_label decls tl target seen fuel')
              | FStar_Pervasives_Native.None ->
                  labels_extend_label decls tl target seen fuel'))
and matches_all (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (ses : ShEx_Schema.shex_shape_expr Prims.list)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match ses with
     | [] -> FStar_Pervasives_Native.Some true
     | hd::tl ->
         (match ((matches_shape_expr decls idtab visited hd t g fuel'),
                  (matches_all decls idtab visited tl t g fuel'))
          with
          | (FStar_Pervasives_Native.Some false, uu___1) ->
              FStar_Pervasives_Native.Some false
          | (uu___1, FStar_Pervasives_Native.Some false) ->
              FStar_Pervasives_Native.Some false
          | (FStar_Pervasives_Native.Some true, FStar_Pervasives_Native.Some
             true) -> FStar_Pervasives_Native.Some true
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and matches_any (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (ses : ShEx_Schema.shex_shape_expr Prims.list)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match ses with
     | [] -> FStar_Pervasives_Native.Some false
     | hd::tl ->
         (match ((matches_shape_expr decls idtab visited hd t g fuel'),
                  (matches_any decls idtab visited tl t g fuel'))
          with
          | (FStar_Pervasives_Native.Some true, uu___1) ->
              FStar_Pervasives_Native.Some true
          | (uu___1, FStar_Pervasives_Native.Some true) ->
              FStar_Pervasives_Native.Some true
          | (FStar_Pervasives_Native.Some false, FStar_Pervasives_Native.Some
             false) -> FStar_Pervasives_Native.Some false
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and matches_shape (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (sh : ShEx_Schema.shex_shape)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     if Prims.uu___is_Nil sh.ShEx_Schema.sh_extends
     then
       let own_te_list =
         match sh.ShEx_Schema.sh_expression with
         | FStar_Pervasives_Native.Some te -> [te]
         | FStar_Pervasives_Native.None -> [] in
       matches_shape_flat decls idtab visited own_te_list
         sh.ShEx_Schema.sh_extra sh.ShEx_Schema.sh_closed [] sh
         sh.ShEx_Schema.sh_semacts t g fuel'
     else
       (match resolve_extends decls sh.ShEx_Schema.sh_extends [] fuel' with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (chain, uu___2) ->
            let all_extra =
              FStar_List_Tot_Base.op_At sh.ShEx_Schema.sh_extra
                chain.ef_extra in
            let all_closed = sh.ShEx_Schema.sh_closed || chain.ef_closed in
            let node_checks_result =
              if Prims.uu___is_Nil chain.ef_checks
              then FStar_Pervasives_Native.Some true
              else matches_all decls idtab visited chain.ef_checks t g fuel' in
            let arcs_out =
              match RDF_Graph_Executable.term_to_subject t with
              | FStar_Pervasives_Native.None -> []
              | FStar_Pervasives_Native.Some s -> triples_with_subject g s in
            let own_pairs_opt =
              match sh.ShEx_Schema.sh_expression with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some []
              | FStar_Pervasives_Native.Some te ->
                  te_mentioned_pairs idtab te fuel' in
            let chain_pairs_opt =
              te_mentioned_pairs_list idtab chain.ef_tes fuel' in
            (match (own_pairs_opt, chain_pairs_opt) with
             | (FStar_Pervasives_Native.None, uu___3) ->
                 FStar_Pervasives_Native.None
             | (uu___3, FStar_Pervasives_Native.None) ->
                 FStar_Pervasives_Native.None
             | (FStar_Pervasives_Native.Some own_pairs,
                FStar_Pervasives_Native.Some chain_pairs) ->
                 let all_pairs =
                   FStar_List_Tot_Base.op_At own_pairs chain_pairs in
                 let closed_result =
                   if Prims.op_Negation all_closed
                   then FStar_Pervasives_Native.Some true
                   else
                     (let mentioned_preds =
                        FStar_List_Tot_Base.map FStar_Pervasives_Native.snd
                          (FStar_List_Tot_Base.filter
                             (fun p ->
                                Prims.op_Negation
                                  (FStar_Pervasives_Native.fst p)) all_pairs) in
                      FStar_Pervasives_Native.Some
                        (FStar_List_Tot_Base.for_all
                           (fun tr ->
                              (FStar_List_Tot_Base.mem
                                 tr.RDF_Graph_Executable.p mentioned_preds)
                                ||
                                (FStar_List_Tot_Base.mem
                                   tr.RDF_Graph_Executable.p all_extra))
                           arcs_out)) in
                 let pool0 = gather_pool g t (dedup_pairs all_pairs) in
                 let own_chain_ambiguous = ambiguous_pairs_of all_pairs in
                 let expr_result =
                   eval_own_vs_chain decls idtab visited own_chain_ambiguous
                     sh.ShEx_Schema.sh_expression chain.ef_tes all_extra
                     pool0 g fuel' in
                 let combined =
                   match (node_checks_result, closed_result, expr_result)
                   with
                   | (FStar_Pervasives_Native.Some false, uu___3, uu___4) ->
                       FStar_Pervasives_Native.Some false
                   | (uu___3, FStar_Pervasives_Native.Some false, uu___4) ->
                       FStar_Pervasives_Native.Some false
                   | (uu___3, uu___4, FStar_Pervasives_Native.Some false) ->
                       FStar_Pervasives_Native.Some false
                   | (FStar_Pervasives_Native.Some true,
                      FStar_Pervasives_Native.Some true,
                      FStar_Pervasives_Native.Some true) ->
                       FStar_Pervasives_Native.Some true
                   | (uu___3, uu___4, uu___5) -> FStar_Pervasives_Native.None in
                 (match combined with
                  | FStar_Pervasives_Native.Some true ->
                      FStar_Pervasives_Native.Some
                        (Prims.op_Negation
                           (any_semact_fails sh.ShEx_Schema.sh_semacts))
                  | other -> other))))
and matches_shape_flat (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (own_te_list : ShEx_Schema.shex_triple_expr Prims.list)
  (extra : Prims.string Prims.list) (closed : Prims.bool)
  (node_checks : ShEx_Schema.shex_shape_expr Prims.list)
  (sh : ShEx_Schema.shex_shape)
  (semacts : ShEx_Schema.shex_sem_act Prims.list)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     let node_checks_result =
       if Prims.uu___is_Nil node_checks
       then FStar_Pervasives_Native.Some true
       else matches_all decls idtab visited node_checks t g fuel' in
     let arcs_out =
       match RDF_Graph_Executable.term_to_subject t with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some s -> triples_with_subject g s in
     let mentioned_opt = te_mentioned_pairs_list idtab own_te_list fuel' in
     let closed_result =
       if Prims.op_Negation closed
       then FStar_Pervasives_Native.Some true
       else
         (match mentioned_opt with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some pairs ->
              let mentioned_preds =
                FStar_List_Tot_Base.map FStar_Pervasives_Native.snd
                  (FStar_List_Tot_Base.filter
                     (fun p ->
                        Prims.op_Negation (FStar_Pervasives_Native.fst p))
                     pairs) in
              FStar_Pervasives_Native.Some
                (FStar_List_Tot_Base.for_all
                   (fun tr ->
                      (FStar_List_Tot_Base.mem tr.RDF_Graph_Executable.p
                         mentioned_preds)
                        ||
                        (FStar_List_Tot_Base.mem tr.RDF_Graph_Executable.p
                           extra)) arcs_out)) in
     let expr_result =
       eval_expr_list_over_pool decls idtab visited own_te_list extra t g
         fuel' in
     let combined =
       match (node_checks_result, closed_result, expr_result) with
       | (FStar_Pervasives_Native.Some false, uu___1, uu___2) ->
           FStar_Pervasives_Native.Some false
       | (uu___1, FStar_Pervasives_Native.Some false, uu___2) ->
           FStar_Pervasives_Native.Some false
       | (uu___1, uu___2, FStar_Pervasives_Native.Some false) ->
           FStar_Pervasives_Native.Some false
       | (FStar_Pervasives_Native.Some true, FStar_Pervasives_Native.Some
          true, FStar_Pervasives_Native.Some true) ->
           FStar_Pervasives_Native.Some true
       | (uu___1, uu___2, uu___3) -> FStar_Pervasives_Native.None in
     match combined with
     | FStar_Pervasives_Native.Some true ->
         FStar_Pervasives_Native.Some
           (Prims.op_Negation (any_semact_fails semacts))
     | other -> other)
and eval_own_vs_chain (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (own_te_opt : ShEx_Schema.shex_triple_expr FStar_Pervasives_Native.option)
  (chain_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (extra : Prims.string Prims.list) (pool : pool_t)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     let unbounded_tes =
       FStar_List_Tot_Base.filter te_is_unbounded_tc chain_tes in
     match own_te_opt with
     | FStar_Pervasives_Native.None ->
         matches_chain_shared decls idtab visited ambiguous chain_tes
           unbounded_tes extra pool pool g fuel'
     | FStar_Pervasives_Native.Some own_te ->
         (match search_te decls idtab visited ambiguous own_te pool g fuel'
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some leftovers ->
              combine_own_vs_chain_results decls idtab visited ambiguous
                chain_tes unbounded_tes extra leftovers g fuel'))
and combine_own_vs_chain_results
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (chain_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (unbounded_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (extra : Prims.string Prims.list) (leftovers : pool_t Prims.list)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match leftovers with
     | [] -> FStar_Pervasives_Native.Some false
     | lo::tl ->
         (match ((matches_chain_shared decls idtab visited ambiguous
                    chain_tes unbounded_tes extra lo lo g fuel'),
                  (combine_own_vs_chain_results decls idtab visited ambiguous
                     chain_tes unbounded_tes extra tl g fuel'))
          with
          | (FStar_Pervasives_Native.Some true, uu___1) ->
              FStar_Pervasives_Native.Some true
          | (uu___1, FStar_Pervasives_Native.Some true) ->
              FStar_Pervasives_Native.Some true
          | (FStar_Pervasives_Native.Some false, FStar_Pervasives_Native.Some
             false) -> FStar_Pervasives_Native.Some false
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and matches_chain_shared (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (chain_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (unbounded_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (extra : Prims.string Prims.list) (pool : pool_t) (running : pool_t)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match chain_tes with
     | [] ->
         FStar_Pervasives_Native.Some
           (FStar_List_Tot_Base.for_all
              (fun e ->
                 let uu___1 = e in
                 match uu___1 with
                 | (inv, pred, uu___2) ->
                     inv || (FStar_List_Tot_Base.mem pred extra)) running)
     | hd::tl ->
         (match search_te decls idtab visited ambiguous hd pool g fuel' with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some raw_completions ->
              (match restrict_unbounded_completions decls idtab visited hd
                       unbounded_tes pool raw_completions g fuel'
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some completions ->
                   matches_chain_shared_try decls idtab visited ambiguous tl
                     unbounded_tes extra pool running completions g fuel')))
and matches_chain_shared_try (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (rest_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (unbounded_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (extra : Prims.string Prims.list) (pool : pool_t) (running : pool_t)
  (completions : pool_t Prims.list) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match completions with
     | [] -> FStar_Pervasives_Native.Some false
     | c::crest ->
         (match ((matches_chain_shared decls idtab visited ambiguous rest_tes
                    unbounded_tes extra pool (pool_intersect running c) g
                    fuel'),
                  (matches_chain_shared_try decls idtab visited ambiguous
                     rest_tes unbounded_tes extra pool running crest g fuel'))
          with
          | (FStar_Pervasives_Native.Some true, uu___1) ->
              FStar_Pervasives_Native.Some true
          | (uu___1, FStar_Pervasives_Native.Some true) ->
              FStar_Pervasives_Native.Some true
          | (FStar_Pervasives_Native.Some false, FStar_Pervasives_Native.Some
             false) -> FStar_Pervasives_Native.Some false
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and restrict_unbounded_completions
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (hd : ShEx_Schema.shex_triple_expr)
  (unbounded_tes : ShEx_Schema.shex_triple_expr Prims.list) (pool : pool_t)
  (raw_completions : pool_t Prims.list) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : pool_t Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     if Prims.op_Negation (te_is_unbounded_tc hd)
     then FStar_Pervasives_Native.Some raw_completions
     else
       (match raw_completions with
        | [] -> FStar_Pervasives_Native.Some []
        | c::crest ->
            let claimed = pool_diff pool c in
            (match restrict_claimed decls idtab visited unbounded_tes claimed
                     g fuel'
             with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some given_back ->
                 (match restrict_unbounded_completions decls idtab visited hd
                          unbounded_tes pool crest g fuel'
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some rest ->
                      FStar_Pervasives_Native.Some
                        ((FStar_List_Tot_Base.op_At c given_back) :: rest)))))
and restrict_claimed (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (unbounded_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (claimed : pool_t) (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat)
  : pool_t FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match claimed with
     | [] -> FStar_Pervasives_Native.Some []
     | e::tl ->
         (match ((background_safe decls idtab visited unbounded_tes e g fuel'),
                  (restrict_claimed decls idtab visited unbounded_tes tl g
                     fuel'))
          with
          | (FStar_Pervasives_Native.Some true, FStar_Pervasives_Native.Some
             rest) -> FStar_Pervasives_Native.Some rest
          | (FStar_Pervasives_Native.Some false, FStar_Pervasives_Native.Some
             rest) -> FStar_Pervasives_Native.Some (e :: rest)
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and background_safe (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (unbounded_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (item : pool_elem) (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat)
  : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     if Prims.uu___is_Nil unbounded_tes
     then FStar_Pervasives_Native.Some false
     else background_safe_all decls idtab visited unbounded_tes item g fuel')
and background_safe_all (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (unbounded_tes : ShEx_Schema.shex_triple_expr Prims.list)
  (item : pool_elem) (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat)
  : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match unbounded_tes with
     | [] -> FStar_Pervasives_Native.Some true
     | hd::tl ->
         (match ((item_good_for_unbounded_te decls idtab visited hd item g
                    fuel'),
                  (background_safe_all decls idtab visited tl item g fuel'))
          with
          | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b)
              -> FStar_Pervasives_Native.Some (a && b)
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and item_good_for_unbounded_te
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (te : ShEx_Schema.shex_triple_expr)
  (item : pool_elem) (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat)
  : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match te with
     | ShEx_Schema.TE_TripleConstraint tc ->
         let uu___1 = item in
         (match uu___1 with
          | (inv, pred, tm) ->
              if
                Prims.op_Negation
                  ((inv = tc.ShEx_Schema.tc_inverse) &&
                     (pred = tc.ShEx_Schema.tc_predicate))
              then FStar_Pervasives_Native.Some true
              else
                (match tc.ShEx_Schema.tc_value_expr with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some true
                 | FStar_Pervasives_Native.Some se ->
                     matches_shape_expr decls idtab visited se tm g fuel'))
     | uu___1 -> FStar_Pervasives_Native.Some true)
and eval_expr_list_over_pool (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (tes : ShEx_Schema.shex_triple_expr Prims.list)
  (extra : Prims.string Prims.list) (t : RDF_Graph_Executable.rdf_term)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     if Prims.uu___is_Nil tes
     then FStar_Pervasives_Native.Some true
     else
       (match te_mentioned_pairs_list idtab tes fuel' with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some pairs ->
            let pool0 = gather_pool g t (dedup_pairs pairs) in
            let ambiguous = ambiguous_pairs_of pairs in
            (match search_eachof_list decls idtab visited ambiguous tes pool0
                     g fuel'
             with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some leftovers ->
                 FStar_Pervasives_Native.Some
                   (FStar_List_Tot_Base.existsb
                      (fun lo ->
                         FStar_List_Tot_Base.for_all
                           (fun e ->
                              let uu___2 = e in
                              match uu___2 with
                              | (inv, pred, uu___3) ->
                                  inv || (FStar_List_Tot_Base.mem pred extra))
                           lo) leftovers))))
and te_mentioned_pairs
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (te : ShEx_Schema.shex_triple_expr) (fuel : Prims.nat) :
  (Prims.bool * Prims.string) Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match te with
     | ShEx_Schema.TE_TripleConstraint tc ->
         FStar_Pervasives_Native.Some
           [((tc.ShEx_Schema.tc_inverse), (tc.ShEx_Schema.tc_predicate))]
     | ShEx_Schema.TE_Ref id ->
         (match lookup_te_id idtab id with
          | FStar_Pervasives_Native.Some resolved ->
              te_mentioned_pairs idtab resolved fuel'
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ShEx_Schema.TE_EachOf grp ->
         te_mentioned_pairs_list idtab grp.ShEx_Schema.gr_expressions fuel'
     | ShEx_Schema.TE_OneOf grp ->
         te_mentioned_pairs_list idtab grp.ShEx_Schema.gr_expressions fuel')
and te_mentioned_pairs_list
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (tes : ShEx_Schema.shex_triple_expr Prims.list) (fuel : Prims.nat) :
  (Prims.bool * Prims.string) Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match tes with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::tl ->
         (match ((te_mentioned_pairs idtab hd fuel'),
                  (te_mentioned_pairs_list idtab tl fuel'))
          with
          | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b)
              -> FStar_Pervasives_Native.Some (FStar_List_Tot_Base.op_At a b)
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and tc_choose_acc (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (tc : ShEx_Schema.shex_triple_constraint) (pool : pool_t)
  (chosen : Prims.nat) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : pool_t Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match pool with
     | [] ->
         if
           (chosen >= tc.ShEx_Schema.tc_min) &&
             ((tc.ShEx_Schema.tc_max = (Prims.of_int (-1))) ||
                (chosen <= tc.ShEx_Schema.tc_max))
         then FStar_Pervasives_Native.Some [[]]
         else FStar_Pervasives_Native.Some []
     | (inv, pred, tm)::tl ->
         if
           Prims.op_Negation
             ((inv = tc.ShEx_Schema.tc_inverse) &&
                (pred = tc.ShEx_Schema.tc_predicate))
         then
           (match tc_choose_acc decls idtab visited ambiguous tc tl chosen g
                    fuel'
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some rests ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.map (fun r -> (inv, pred, tm) :: r)
                     rests))
         else
           (let good_opt =
              match tc.ShEx_Schema.tc_value_expr with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some true
              | FStar_Pervasives_Native.Some se ->
                  matches_shape_expr decls idtab visited se tm g fuel' in
            match good_opt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some is_good ->
                let offer_leave =
                  (Prims.op_Negation is_good) ||
                    (pair_mem (inv, pred) ambiguous) in
                let leave_opt =
                  if offer_leave
                  then
                    match tc_choose_acc decls idtab visited ambiguous tc tl
                            chosen g fuel'
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some leave_rests ->
                        FStar_Pervasives_Native.Some
                          (FStar_List_Tot_Base.map
                             (fun r -> (inv, pred, tm) :: r) leave_rests)
                  else FStar_Pervasives_Native.Some [] in
                (match leave_opt with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some leave_opts ->
                     if is_good
                     then
                       (match tc_choose_acc decls idtab visited ambiguous tc
                                tl (chosen + Prims.int_one) g fuel'
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some take_rests ->
                            FStar_Pervasives_Native.Some
                              (FStar_List_Tot_Base.op_At leave_opts
                                 take_rests))
                     else FStar_Pervasives_Native.Some leave_opts)))
and classify_candidates (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ve : ShEx_Schema.shex_shape_expr FStar_Pervasives_Native.option)
  (items : pool_t) (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  (Prims.nat * pool_t) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match items with
     | [] -> FStar_Pervasives_Native.Some (Prims.int_zero, [])
     | hd::tl ->
         let uu___1 = hd in
         (match uu___1 with
          | (inv, pred, tm) ->
              let good_opt =
                match ve with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.Some true
                | FStar_Pervasives_Native.Some se ->
                    matches_shape_expr decls idtab visited se tm g fuel' in
              (match good_opt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some is_good ->
                   (match classify_candidates decls idtab visited ve tl g
                            fuel'
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (cnt, badl) ->
                        if is_good
                        then
                          FStar_Pervasives_Native.Some
                            ((cnt + Prims.int_one), badl)
                        else FStar_Pervasives_Native.Some (cnt, (hd :: badl))))))
and count_children (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (tes : ShEx_Schema.shex_triple_expr Prims.list)
  (pool : pool_t) (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  (Prims.nat Prims.list * pool_t) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match tes with
     | [] -> FStar_Pervasives_Native.Some ([], pool)
     | (ShEx_Schema.TE_TripleConstraint tc)::tl ->
         let uu___1 =
           FStar_List_Tot_Base.partition
             (fun e ->
                let uu___2 = e in
                match uu___2 with
                | (inv, pred, uu___3) ->
                    (inv = tc.ShEx_Schema.tc_inverse) &&
                      (pred = tc.ShEx_Schema.tc_predicate)) pool in
         (match uu___1 with
          | (matching, rest) ->
              (match classify_candidates decls idtab visited
                       tc.ShEx_Schema.tc_value_expr matching g fuel'
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (good_count, bad_list) ->
                   (match count_children decls idtab visited tl rest g fuel'
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (counts, leftover) ->
                        FStar_Pervasives_Native.Some
                          ((good_count :: counts),
                            (FStar_List_Tot_Base.op_At bad_list leftover)))))
     | uu___1 -> FStar_Pervasives_Native.None)
and search_repeated_group (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited) (grp : ShEx_Schema.shex_group) (pool : pool_t)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat)
  (is_eachof : Prims.bool) :
  pool_t Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     if
       Prims.op_Negation
         (distinct_child_pairs grp.ShEx_Schema.gr_expressions)
     then FStar_Pervasives_Native.None
     else
       (match count_children decls idtab visited
                grp.ShEx_Schema.gr_expressions pool g fuel'
        with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (counts, leftover) ->
            let gmin =
              match grp.ShEx_Schema.gr_min with
              | FStar_Pervasives_Native.Some n -> n
              | FStar_Pervasives_Native.None -> Prims.int_one in
            let gmax =
              match grp.ShEx_Schema.gr_max with
              | FStar_Pervasives_Native.Some n -> n
              | FStar_Pervasives_Native.None -> Prims.int_one in
            let total_count = sum_nat counts in
            if is_eachof
            then
              (if Prims.op_Negation (all_equal_nat counts)
               then FStar_Pervasives_Native.Some []
               else
                 (match counts with
                  | hd::uu___3 ->
                      if
                        (hd >= gmin) &&
                          ((gmax = (Prims.of_int (-1))) || (hd <= gmax))
                      then FStar_Pervasives_Native.Some [leftover]
                      else FStar_Pervasives_Native.Some []
                  | [] ->
                      if
                        (Prims.int_zero >= gmin) &&
                          ((gmax = (Prims.of_int (-1))) ||
                             (Prims.int_zero <= gmax))
                      then FStar_Pervasives_Native.Some [leftover]
                      else FStar_Pervasives_Native.Some []))
            else
              if
                (total_count >= gmin) &&
                  ((gmax = (Prims.of_int (-1))) || (total_count <= gmax))
              then FStar_Pervasives_Native.Some [leftover]
              else FStar_Pervasives_Native.Some []))
and search_te (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (te : ShEx_Schema.shex_triple_expr) (pool : pool_t)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  pool_t Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match te with
     | ShEx_Schema.TE_TripleConstraint tc ->
         (match tc_choose_acc decls idtab visited ambiguous tc pool
                  Prims.int_zero g fuel'
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some results ->
              if any_semact_fails tc.ShEx_Schema.tc_semacts
              then FStar_Pervasives_Native.Some []
              else FStar_Pervasives_Native.Some results)
     | ShEx_Schema.TE_Ref id ->
         (match lookup_te_id idtab id with
          | FStar_Pervasives_Native.Some resolved ->
              search_te decls idtab visited ambiguous resolved pool g fuel'
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ShEx_Schema.TE_EachOf grp ->
         let raw =
           if
             (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_min) ||
               (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_max)
           then
             search_repeated_group decls idtab visited grp pool g fuel' true
           else
             search_eachof_list decls idtab visited ambiguous
               grp.ShEx_Schema.gr_expressions pool g fuel' in
         (match raw with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some results ->
              if any_semact_fails grp.ShEx_Schema.gr_semacts
              then FStar_Pervasives_Native.Some []
              else FStar_Pervasives_Native.Some results)
     | ShEx_Schema.TE_OneOf grp ->
         let raw =
           if
             (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_min) ||
               (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_max)
           then
             search_repeated_group decls idtab visited grp pool g fuel' false
           else
             search_oneof_list decls idtab visited ambiguous
               grp.ShEx_Schema.gr_expressions pool g fuel' in
         (match raw with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some results ->
              if any_semact_fails grp.ShEx_Schema.gr_semacts
              then FStar_Pervasives_Native.Some []
              else FStar_Pervasives_Native.Some results))
and search_eachof_list (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (tes : ShEx_Schema.shex_triple_expr Prims.list) (pool : pool_t)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  pool_t Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match tes with
     | [] -> FStar_Pervasives_Native.Some [pool]
     | hd::tl ->
         (match search_te decls idtab visited ambiguous hd pool g fuel' with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some states ->
              thread_states decls idtab visited ambiguous tl states g fuel'))
and thread_states (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (tl : ShEx_Schema.shex_triple_expr Prims.list) (states : pool_t Prims.list)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  pool_t Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match states with
     | [] -> FStar_Pervasives_Native.Some []
     | s::srest ->
         (match ((search_eachof_list decls idtab visited ambiguous tl s g
                    fuel'),
                  (thread_states decls idtab visited ambiguous tl srest g
                     fuel'))
          with
          | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b)
              -> FStar_Pervasives_Native.Some (FStar_List_Tot_Base.op_At a b)
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and search_oneof_list (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (tes : ShEx_Schema.shex_triple_expr Prims.list) (pool : pool_t)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  pool_t Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    combine_oneof
      (search_te_list_map decls idtab visited ambiguous tes pool g
         (fuel - Prims.int_one))
and search_te_list_map (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (idtab : (Prims.string * ShEx_Schema.shex_triple_expr) Prims.list)
  (visited : shex_visited)
  (ambiguous : (Prims.bool * Prims.string) Prims.list)
  (tes : ShEx_Schema.shex_triple_expr Prims.list) (pool : pool_t)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  pool_t Prims.list FStar_Pervasives_Native.option Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (let fuel' = fuel - Prims.int_one in
     match tes with
     | [] -> []
     | hd::tl -> (search_te decls idtab visited ambiguous hd pool g fuel') ::
         (search_te_list_map decls idtab visited ambiguous tl pool g fuel'))
let validate_focus (schema : ShEx_Schema.shex_schema)
  (shape_id : Prims.string FStar_Pervasives_Native.option)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph) :
  Prims.bool FStar_Pervasives_Native.option=
  if any_semact_fails schema.ShEx_Schema.sch_start_acts
  then FStar_Pervasives_Native.Some false
  else
    (let idtab = shape_decl_list_collect_ids schema.ShEx_Schema.sch_shapes in
     let n_shapes = FStar_List_Tot_Base.length schema.ShEx_Schema.sch_shapes in
     let n_graph = FStar_List_Tot_Base.length g in
     let fuel =
       (((Prims.of_int (300)) + ((Prims.of_int (50)) * n_shapes)) +
          ((Prims.of_int (30)) * n_graph))
         + ((Prims.of_int (5)) * (n_graph * n_graph)) in
     match shape_id with
     | FStar_Pervasives_Native.Some label ->
         (match lookup_shape_decl schema.ShEx_Schema.sch_shapes label with
          | FStar_Pervasives_Native.Some sd ->
              matches_shape_expr schema.ShEx_Schema.sch_shapes idtab []
                sd.ShEx_Schema.sd_expr t g fuel
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | FStar_Pervasives_Native.None ->
         (match schema.ShEx_Schema.sch_start with
          | FStar_Pervasives_Native.Some se ->
              matches_shape_expr schema.ShEx_Schema.sch_shapes idtab [] se t
                g fuel
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
