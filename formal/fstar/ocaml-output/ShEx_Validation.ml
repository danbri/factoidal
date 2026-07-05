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
let rec te_signature (te : ShEx_Schema.shex_triple_expr) :
  (Prims.bool * Prims.string) Prims.list FStar_Pervasives_Native.option=
  match te with
  | ShEx_Schema.TE_Ref uu___ -> FStar_Pervasives_Native.None
  | ShEx_Schema.TE_OneOf uu___ -> FStar_Pervasives_Native.None
  | ShEx_Schema.TE_TripleConstraint tc ->
      FStar_Pervasives_Native.Some
        [((tc.ShEx_Schema.tc_inverse), (tc.ShEx_Schema.tc_predicate))]
  | ShEx_Schema.TE_EachOf grp ->
      if
        (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_min) ||
          (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_max)
      then FStar_Pervasives_Native.None
      else te_signature_list grp.ShEx_Schema.gr_expressions
and te_signature_list (tes : ShEx_Schema.shex_triple_expr Prims.list) :
  (Prims.bool * Prims.string) Prims.list FStar_Pervasives_Native.option=
  match tes with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match ((te_signature hd), (te_signature_list tl)) with
       | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some s2)
           -> FStar_Pervasives_Native.Some (FStar_List_Tot_Base.append s1 s2)
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
let sig_mem (x : (Prims.bool * Prims.string))
  (l : (Prims.bool * Prims.string) Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun y ->
       ((FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)) &&
         ((FStar_Pervasives_Native.snd x) = (FStar_Pervasives_Native.snd y)))
    l
let rec sig_disjoint (a : (Prims.bool * Prims.string) Prims.list)
  (b : (Prims.bool * Prims.string) Prims.list) : Prims.bool=
  match a with
  | [] -> true
  | hd::tl -> (Prims.op_Negation (sig_mem hd b)) && (sig_disjoint tl b)
let rec te_fastpath_ok (te : ShEx_Schema.shex_triple_expr) : Prims.bool=
  match te with
  | ShEx_Schema.TE_TripleConstraint uu___ -> true
  | ShEx_Schema.TE_Ref uu___ -> false
  | ShEx_Schema.TE_OneOf uu___ -> false
  | ShEx_Schema.TE_EachOf grp ->
      if
        (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_min) ||
          (FStar_Pervasives_Native.uu___is_Some grp.ShEx_Schema.gr_max)
      then false
      else te_fastpath_ok_list grp.ShEx_Schema.gr_expressions
and te_fastpath_ok_list (tes : ShEx_Schema.shex_triple_expr Prims.list) :
  Prims.bool=
  match tes with
  | [] -> true
  | hd::tl ->
      ((te_fastpath_ok hd) && (te_fastpath_ok_list tl)) &&
        ((match ((te_signature hd), (te_signature_list tl)) with
          | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some
             s2) -> sig_disjoint s1 s2
          | (uu___, uu___1) -> false))
let rec te_claimed_predicates (te : ShEx_Schema.shex_triple_expr) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match te with
  | ShEx_Schema.TE_TripleConstraint tc ->
      FStar_Pervasives_Native.Some
        (if tc.ShEx_Schema.tc_inverse
         then []
         else [tc.ShEx_Schema.tc_predicate])
  | ShEx_Schema.TE_EachOf grp ->
      te_claimed_predicates_list grp.ShEx_Schema.gr_expressions
  | ShEx_Schema.TE_OneOf uu___ -> FStar_Pervasives_Native.None
  | ShEx_Schema.TE_Ref uu___ -> FStar_Pervasives_Native.None
and te_claimed_predicates_list
  (tes : ShEx_Schema.shex_triple_expr Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match tes with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match ((te_claimed_predicates hd), (te_claimed_predicates_list tl))
       with
       | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b) ->
           FStar_Pervasives_Native.Some (FStar_List_Tot_Base.append a b)
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
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
let rec lookup_shape_decl (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (label : Prims.string) :
  ShEx_Schema.shex_shape_decl FStar_Pervasives_Native.option=
  match decls with
  | [] -> FStar_Pervasives_Native.None
  | hd::tl ->
      if hd.ShEx_Schema.sd_id = label
      then FStar_Pervasives_Native.Some hd
      else lookup_shape_decl tl label
let rec matches_shape_expr (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (se : ShEx_Schema.shex_shape_expr) (t : RDF_Graph_Executable.rdf_term)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match se with
     | ShEx_Schema.SE_NodeConstraint nc ->
         FStar_Pervasives_Native.Some (node_constraint_matches nc t)
     | ShEx_Schema.SE_ShapeAnd ses -> matches_all decls ses t g fuel'
     | ShEx_Schema.SE_ShapeOr ses -> matches_any decls ses t g fuel'
     | ShEx_Schema.SE_ShapeNot se' ->
         (match matches_shape_expr decls se' t g fuel' with
          | FStar_Pervasives_Native.Some b ->
              FStar_Pervasives_Native.Some (Prims.op_Negation b)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ShEx_Schema.SE_Ref label ->
         (match lookup_shape_decl decls label with
          | FStar_Pervasives_Native.Some sd ->
              matches_shape_expr decls sd.ShEx_Schema.sd_expr t g fuel'
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ShEx_Schema.SE_Shape sh -> matches_shape decls sh t g fuel'
     | ShEx_Schema.SE_ShapeExternal -> FStar_Pervasives_Native.None)
and matches_all (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (ses : ShEx_Schema.shex_shape_expr Prims.list)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match ses with
     | [] -> FStar_Pervasives_Native.Some true
     | hd::tl ->
         (match ((matches_shape_expr decls hd t g fuel'),
                  (matches_all decls tl t g fuel'))
          with
          | (FStar_Pervasives_Native.Some false, uu___1) ->
              FStar_Pervasives_Native.Some false
          | (uu___1, FStar_Pervasives_Native.Some false) ->
              FStar_Pervasives_Native.Some false
          | (FStar_Pervasives_Native.Some true, FStar_Pervasives_Native.Some
             true) -> FStar_Pervasives_Native.Some true
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and matches_any (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (ses : ShEx_Schema.shex_shape_expr Prims.list)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match ses with
     | [] -> FStar_Pervasives_Native.Some false
     | hd::tl ->
         (match ((matches_shape_expr decls hd t g fuel'),
                  (matches_any decls tl t g fuel'))
          with
          | (FStar_Pervasives_Native.Some true, uu___1) ->
              FStar_Pervasives_Native.Some true
          | (uu___1, FStar_Pervasives_Native.Some true) ->
              FStar_Pervasives_Native.Some true
          | (FStar_Pervasives_Native.Some false, FStar_Pervasives_Native.Some
             false) -> FStar_Pervasives_Native.Some false
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and matches_shape (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (sh : ShEx_Schema.shex_shape) (t : RDF_Graph_Executable.rdf_term)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if Prims.op_Negation (Prims.uu___is_Nil sh.ShEx_Schema.sh_extends)
    then FStar_Pervasives_Native.None
    else
      (let fuel' = fuel - Prims.int_one in
       let arcs_out =
         match RDF_Graph_Executable.term_to_subject t with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some s -> triples_with_subject g s in
       let expr_result =
         match sh.ShEx_Schema.sh_expression with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some true
         | FStar_Pervasives_Native.Some te ->
             if te_fastpath_ok te
             then
               matches_triple_expr_value decls te t g sh.ShEx_Schema.sh_extra
                 fuel'
             else FStar_Pervasives_Native.None in
       let claimed_opt =
         match sh.ShEx_Schema.sh_expression with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some []
         | FStar_Pervasives_Native.Some te -> te_claimed_predicates te in
       let closed_result =
         if Prims.op_Negation sh.ShEx_Schema.sh_closed
         then FStar_Pervasives_Native.Some true
         else
           (match claimed_opt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some claimed ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.for_all
                     (fun tr ->
                        (FStar_List_Tot_Base.mem tr.RDF_Graph_Executable.p
                           claimed)
                          ||
                          (FStar_List_Tot_Base.mem tr.RDF_Graph_Executable.p
                             sh.ShEx_Schema.sh_extra)) arcs_out)) in
       match (expr_result, closed_result) with
       | (FStar_Pervasives_Native.Some false, uu___2) ->
           FStar_Pervasives_Native.Some false
       | (uu___2, FStar_Pervasives_Native.Some false) ->
           FStar_Pervasives_Native.Some false
       | (FStar_Pervasives_Native.Some true, FStar_Pervasives_Native.Some
          true) -> FStar_Pervasives_Native.Some true
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
and matches_triple_expr_value
  (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (te : ShEx_Schema.shex_triple_expr) (focus : RDF_Graph_Executable.rdf_term)
  (g : RDF_Graph_Executable.rdf_graph) (extra : Prims.string Prims.list)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match te with
     | ShEx_Schema.TE_Ref uu___1 -> FStar_Pervasives_Native.None
     | ShEx_Schema.TE_OneOf uu___1 -> FStar_Pervasives_Native.None
     | ShEx_Schema.TE_TripleConstraint tc ->
         let others =
           shex_gather_candidates g focus tc.ShEx_Schema.tc_inverse
             tc.ShEx_Schema.tc_predicate in
         (match shex_check_others decls others tc.ShEx_Schema.tc_value_expr g
                  fuel'
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some bools ->
              let n_total = FStar_List_Tot_Base.length others in
              let good_count =
                FStar_List_Tot_Base.length
                  (FStar_List_Tot_Base.filter (fun b -> b) bools) in
              let bad_count = n_total - good_count in
              let allowed_extra =
                FStar_List_Tot_Base.mem tc.ShEx_Schema.tc_predicate extra in
              let bad_ok = (bad_count = Prims.int_zero) || allowed_extra in
              FStar_Pervasives_Native.Some
                ((bad_ok && (good_count >= tc.ShEx_Schema.tc_min)) &&
                   ((tc.ShEx_Schema.tc_max = (Prims.of_int (-1))) ||
                      (good_count <= tc.ShEx_Schema.tc_max))))
     | ShEx_Schema.TE_EachOf grp ->
         matches_triple_expr_list decls grp.ShEx_Schema.gr_expressions focus
           g extra fuel')
and matches_triple_expr_list (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (tes : ShEx_Schema.shex_triple_expr Prims.list)
  (focus : RDF_Graph_Executable.rdf_term)
  (g : RDF_Graph_Executable.rdf_graph) (extra : Prims.string Prims.list)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match tes with
     | [] -> FStar_Pervasives_Native.Some true
     | hd::tl ->
         (match ((matches_triple_expr_value decls hd focus g extra fuel'),
                  (matches_triple_expr_list decls tl focus g extra fuel'))
          with
          | (FStar_Pervasives_Native.Some false, uu___1) ->
              FStar_Pervasives_Native.Some false
          | (uu___1, FStar_Pervasives_Native.Some false) ->
              FStar_Pervasives_Native.Some false
          | (FStar_Pervasives_Native.Some true, FStar_Pervasives_Native.Some
             true) -> FStar_Pervasives_Native.Some true
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
and shex_check_others (decls : ShEx_Schema.shex_shape_decl Prims.list)
  (others : RDF_Graph_Executable.rdf_term Prims.list)
  (ve : ShEx_Schema.shex_shape_expr FStar_Pervasives_Native.option)
  (g : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  Prims.bool Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let fuel' = fuel - Prims.int_one in
     match others with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::tl ->
         let this_ok =
           match ve with
           | FStar_Pervasives_Native.None ->
               FStar_Pervasives_Native.Some true
           | FStar_Pervasives_Native.Some se ->
               matches_shape_expr decls se hd g fuel' in
         (match (this_ok, (shex_check_others decls tl ve g fuel')) with
          | (FStar_Pervasives_Native.Some b, FStar_Pervasives_Native.Some
             rest) -> FStar_Pervasives_Native.Some (b :: rest)
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None))
let validate_focus (schema : ShEx_Schema.shex_schema)
  (shape_id : Prims.string FStar_Pervasives_Native.option)
  (t : RDF_Graph_Executable.rdf_term) (g : RDF_Graph_Executable.rdf_graph) :
  Prims.bool FStar_Pervasives_Native.option=
  let fuel =
    ((Prims.of_int (100)) +
       ((Prims.of_int (20)) *
          (FStar_List_Tot_Base.length schema.ShEx_Schema.sch_shapes)))
      + ((Prims.of_int (10)) * (FStar_List_Tot_Base.length g)) in
  match shape_id with
  | FStar_Pervasives_Native.Some label ->
      (match lookup_shape_decl schema.ShEx_Schema.sch_shapes label with
       | FStar_Pervasives_Native.Some sd ->
           matches_shape_expr schema.ShEx_Schema.sch_shapes
             sd.ShEx_Schema.sd_expr t g fuel
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None ->
      (match schema.ShEx_Schema.sch_start with
       | FStar_Pervasives_Native.Some se ->
           matches_shape_expr schema.ShEx_Schema.sch_shapes se t g fuel
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
