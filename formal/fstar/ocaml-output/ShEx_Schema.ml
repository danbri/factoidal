open Prims
let shex_char_to_digit (c : FStar_Char.char) :
  Prims.int FStar_Pervasives_Native.option=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
  then FStar_Pervasives_Native.Some (n - (Prims.of_int (48)))
  else FStar_Pervasives_Native.None
let rec shex_parse_int_chars (chars : FStar_Char.char Prims.list)
  (acc : Prims.int) : Prims.int FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      (match shex_char_to_digit c with
       | FStar_Pervasives_Native.Some d ->
           shex_parse_int_chars rest ((acc * (Prims.of_int (10))) + d)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let shex_parse_int_string (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match FStar_String.list_of_string s with
  | [] -> FStar_Pervasives_Native.None
  | chars ->
      if
        (FStar_List_Tot_Base.hd chars) =
          (FStar_Char.char_of_int (Prims.of_int (45)))
      then
        (match shex_parse_int_chars (FStar_List_Tot_Base.tl chars)
                 Prims.int_zero
         with
         | FStar_Pervasives_Native.Some n ->
             FStar_Pervasives_Native.Some (Prims.int_zero - n)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else shex_parse_int_chars chars Prims.int_zero
let json_get_number_lexeme (key : Prims.string) (obj : Parser_JSON.json_val)
  : Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field key obj with
  | FStar_Pervasives_Native.Some (Parser_JSON.JNumber s) ->
      FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
let json_get_int (key : Prims.string) (obj : Parser_JSON.json_val) :
  Prims.int FStar_Pervasives_Native.option=
  match json_get_number_lexeme key obj with
  | FStar_Pervasives_Native.Some s -> shex_parse_int_string s
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let json_get_int_default (key : Prims.string) (obj : Parser_JSON.json_val)
  (d : Prims.int) : Prims.int=
  match json_get_int key obj with
  | FStar_Pervasives_Native.Some n -> n
  | FStar_Pervasives_Native.None -> d
let json_get_bool_default (key : Prims.string) (obj : Parser_JSON.json_val)
  (d : Prims.bool) : Prims.bool=
  match Parser_JSON.json_get_bool key obj with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> d
type shex_node_kind =
  | ShexNK_Iri 
  | ShexNK_BNode 
  | ShexNK_NonLiteral 
  | ShexNK_Literal 
let uu___is_ShexNK_Iri (projectee : shex_node_kind) : Prims.bool=
  match projectee with | ShexNK_Iri -> true | uu___ -> false
let uu___is_ShexNK_BNode (projectee : shex_node_kind) : Prims.bool=
  match projectee with | ShexNK_BNode -> true | uu___ -> false
let uu___is_ShexNK_NonLiteral (projectee : shex_node_kind) : Prims.bool=
  match projectee with | ShexNK_NonLiteral -> true | uu___ -> false
let uu___is_ShexNK_Literal (projectee : shex_node_kind) : Prims.bool=
  match projectee with | ShexNK_Literal -> true | uu___ -> false
type shex_stem =
  | ShexStemPlain of Prims.string 
  | ShexStemWildcard 
let uu___is_ShexStemPlain (projectee : shex_stem) : Prims.bool=
  match projectee with | ShexStemPlain _0 -> true | uu___ -> false
let __proj__ShexStemPlain__item___0 (projectee : shex_stem) : Prims.string=
  match projectee with | ShexStemPlain _0 -> _0
let uu___is_ShexStemWildcard (projectee : shex_stem) : Prims.bool=
  match projectee with | ShexStemWildcard -> true | uu___ -> false
type shex_object_value =
  | ShexOV_Iri of Prims.string 
  | ShexOV_Literal of Prims.string * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option 
let uu___is_ShexOV_Iri (projectee : shex_object_value) : Prims.bool=
  match projectee with | ShexOV_Iri _0 -> true | uu___ -> false
let __proj__ShexOV_Iri__item___0 (projectee : shex_object_value) :
  Prims.string= match projectee with | ShexOV_Iri _0 -> _0
let uu___is_ShexOV_Literal (projectee : shex_object_value) : Prims.bool=
  match projectee with
  | ShexOV_Literal (value, language, datatype) -> true
  | uu___ -> false
let __proj__ShexOV_Literal__item__value (projectee : shex_object_value) :
  Prims.string=
  match projectee with | ShexOV_Literal (value, language, datatype) -> value
let __proj__ShexOV_Literal__item__language (projectee : shex_object_value) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | ShexOV_Literal (value, language, datatype) -> language
let __proj__ShexOV_Literal__item__datatype (projectee : shex_object_value) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | ShexOV_Literal (value, language, datatype) -> datatype
type shex_sem_act =
  {
  sa_name: Prims.string ;
  sa_code: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkshex_sem_act__item__sa_name (projectee : shex_sem_act) :
  Prims.string= match projectee with | { sa_name; sa_code;_} -> sa_name
let __proj__Mkshex_sem_act__item__sa_code (projectee : shex_sem_act) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { sa_name; sa_code;_} -> sa_code
type shex_annotation =
  {
  an_predicate: Prims.string ;
  an_object: shex_object_value }
let __proj__Mkshex_annotation__item__an_predicate
  (projectee : shex_annotation) : Prims.string=
  match projectee with | { an_predicate; an_object;_} -> an_predicate
let __proj__Mkshex_annotation__item__an_object (projectee : shex_annotation)
  : shex_object_value=
  match projectee with | { an_predicate; an_object;_} -> an_object
type shex_value_set_value =
  | VSV_Value of shex_object_value 
  | VSV_IriStem of shex_stem 
  | VSV_IriStemRange of shex_stem * shex_value_set_value Prims.list 
  | VSV_LiteralStem of shex_stem 
  | VSV_LiteralStemRange of shex_stem * shex_value_set_value Prims.list 
  | VSV_Language of Prims.string 
  | VSV_LanguageStem of shex_stem 
  | VSV_LanguageStemRange of shex_stem * shex_value_set_value Prims.list 
let uu___is_VSV_Value (projectee : shex_value_set_value) : Prims.bool=
  match projectee with | VSV_Value _0 -> true | uu___ -> false
let __proj__VSV_Value__item___0 (projectee : shex_value_set_value) :
  shex_object_value= match projectee with | VSV_Value _0 -> _0
let uu___is_VSV_IriStem (projectee : shex_value_set_value) : Prims.bool=
  match projectee with | VSV_IriStem _0 -> true | uu___ -> false
let __proj__VSV_IriStem__item___0 (projectee : shex_value_set_value) :
  shex_stem= match projectee with | VSV_IriStem _0 -> _0
let uu___is_VSV_IriStemRange (projectee : shex_value_set_value) : Prims.bool=
  match projectee with | VSV_IriStemRange (_0, _1) -> true | uu___ -> false
let __proj__VSV_IriStemRange__item___0 (projectee : shex_value_set_value) :
  shex_stem= match projectee with | VSV_IriStemRange (_0, _1) -> _0
let __proj__VSV_IriStemRange__item___1 (projectee : shex_value_set_value) :
  shex_value_set_value Prims.list=
  match projectee with | VSV_IriStemRange (_0, _1) -> _1
let uu___is_VSV_LiteralStem (projectee : shex_value_set_value) : Prims.bool=
  match projectee with | VSV_LiteralStem _0 -> true | uu___ -> false
let __proj__VSV_LiteralStem__item___0 (projectee : shex_value_set_value) :
  shex_stem= match projectee with | VSV_LiteralStem _0 -> _0
let uu___is_VSV_LiteralStemRange (projectee : shex_value_set_value) :
  Prims.bool=
  match projectee with
  | VSV_LiteralStemRange (_0, _1) -> true
  | uu___ -> false
let __proj__VSV_LiteralStemRange__item___0 (projectee : shex_value_set_value)
  : shex_stem= match projectee with | VSV_LiteralStemRange (_0, _1) -> _0
let __proj__VSV_LiteralStemRange__item___1 (projectee : shex_value_set_value)
  : shex_value_set_value Prims.list=
  match projectee with | VSV_LiteralStemRange (_0, _1) -> _1
let uu___is_VSV_Language (projectee : shex_value_set_value) : Prims.bool=
  match projectee with | VSV_Language _0 -> true | uu___ -> false
let __proj__VSV_Language__item___0 (projectee : shex_value_set_value) :
  Prims.string= match projectee with | VSV_Language _0 -> _0
let uu___is_VSV_LanguageStem (projectee : shex_value_set_value) : Prims.bool=
  match projectee with | VSV_LanguageStem _0 -> true | uu___ -> false
let __proj__VSV_LanguageStem__item___0 (projectee : shex_value_set_value) :
  shex_stem= match projectee with | VSV_LanguageStem _0 -> _0
let uu___is_VSV_LanguageStemRange (projectee : shex_value_set_value) :
  Prims.bool=
  match projectee with
  | VSV_LanguageStemRange (_0, _1) -> true
  | uu___ -> false
let __proj__VSV_LanguageStemRange__item___0
  (projectee : shex_value_set_value) : shex_stem=
  match projectee with | VSV_LanguageStemRange (_0, _1) -> _0
let __proj__VSV_LanguageStemRange__item___1
  (projectee : shex_value_set_value) : shex_value_set_value Prims.list=
  match projectee with | VSV_LanguageStemRange (_0, _1) -> _1
type shex_vsv_kind =
  | VSVK_Iri 
  | VSVK_Literal 
  | VSVK_Language 
let uu___is_VSVK_Iri (projectee : shex_vsv_kind) : Prims.bool=
  match projectee with | VSVK_Iri -> true | uu___ -> false
let uu___is_VSVK_Literal (projectee : shex_vsv_kind) : Prims.bool=
  match projectee with | VSVK_Literal -> true | uu___ -> false
let uu___is_VSVK_Language (projectee : shex_vsv_kind) : Prims.bool=
  match projectee with | VSVK_Language -> true | uu___ -> false
let decode_bare_vsv_string (kind : shex_vsv_kind) (s : Prims.string) :
  shex_value_set_value=
  match kind with
  | VSVK_Iri -> VSV_Value (ShexOV_Iri s)
  | VSVK_Literal ->
      VSV_Value
        (ShexOV_Literal
           (s, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
  | VSVK_Language -> VSV_Language s
type shex_node_constraint =
  {
  nc_node_kind: shex_node_kind FStar_Pervasives_Native.option ;
  nc_datatype: Prims.string FStar_Pervasives_Native.option ;
  nc_values: shex_value_set_value Prims.list ;
  nc_length: Prims.int FStar_Pervasives_Native.option ;
  nc_minlength: Prims.int FStar_Pervasives_Native.option ;
  nc_maxlength: Prims.int FStar_Pervasives_Native.option ;
  nc_pattern: Prims.string FStar_Pervasives_Native.option ;
  nc_flags: Prims.string FStar_Pervasives_Native.option ;
  nc_mininclusive: Prims.string FStar_Pervasives_Native.option ;
  nc_maxinclusive: Prims.string FStar_Pervasives_Native.option ;
  nc_minexclusive: Prims.string FStar_Pervasives_Native.option ;
  nc_maxexclusive: Prims.string FStar_Pervasives_Native.option ;
  nc_totaldigits: Prims.int FStar_Pervasives_Native.option ;
  nc_fractiondigits: Prims.int FStar_Pervasives_Native.option }
let __proj__Mkshex_node_constraint__item__nc_node_kind
  (projectee : shex_node_constraint) :
  shex_node_kind FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_node_kind
let __proj__Mkshex_node_constraint__item__nc_datatype
  (projectee : shex_node_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_datatype
let __proj__Mkshex_node_constraint__item__nc_values
  (projectee : shex_node_constraint) : shex_value_set_value Prims.list=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_values
let __proj__Mkshex_node_constraint__item__nc_length
  (projectee : shex_node_constraint) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_length
let __proj__Mkshex_node_constraint__item__nc_minlength
  (projectee : shex_node_constraint) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_minlength
let __proj__Mkshex_node_constraint__item__nc_maxlength
  (projectee : shex_node_constraint) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_maxlength
let __proj__Mkshex_node_constraint__item__nc_pattern
  (projectee : shex_node_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_pattern
let __proj__Mkshex_node_constraint__item__nc_flags
  (projectee : shex_node_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_flags
let __proj__Mkshex_node_constraint__item__nc_mininclusive
  (projectee : shex_node_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_mininclusive
let __proj__Mkshex_node_constraint__item__nc_maxinclusive
  (projectee : shex_node_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_maxinclusive
let __proj__Mkshex_node_constraint__item__nc_minexclusive
  (projectee : shex_node_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_minexclusive
let __proj__Mkshex_node_constraint__item__nc_maxexclusive
  (projectee : shex_node_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_maxexclusive
let __proj__Mkshex_node_constraint__item__nc_totaldigits
  (projectee : shex_node_constraint) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_totaldigits
let __proj__Mkshex_node_constraint__item__nc_fractiondigits
  (projectee : shex_node_constraint) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { nc_node_kind; nc_datatype; nc_values; nc_length; nc_minlength;
      nc_maxlength; nc_pattern; nc_flags; nc_mininclusive; nc_maxinclusive;
      nc_minexclusive; nc_maxexclusive; nc_totaldigits; nc_fractiondigits;_}
      -> nc_fractiondigits
type shex_shape_expr =
  | SE_Ref of Prims.string 
  | SE_ShapeAnd of shex_shape_expr Prims.list 
  | SE_ShapeOr of shex_shape_expr Prims.list 
  | SE_ShapeNot of shex_shape_expr 
  | SE_NodeConstraint of shex_node_constraint 
  | SE_Shape of shex_shape 
  | SE_ShapeExternal 
and shex_shape =
  {
  sh_closed: Prims.bool ;
  sh_extra: Prims.string Prims.list ;
  sh_expression: shex_triple_expr FStar_Pervasives_Native.option ;
  sh_semacts: shex_sem_act Prims.list ;
  sh_annotations: shex_annotation Prims.list ;
  sh_extends: Prims.string Prims.list }
and shex_triple_expr =
  | TE_Ref of Prims.string 
  | TE_TripleConstraint of shex_triple_constraint 
  | TE_EachOf of shex_group 
  | TE_OneOf of shex_group 
and shex_group =
  {
  gr_id: Prims.string FStar_Pervasives_Native.option ;
  gr_expressions: shex_triple_expr Prims.list ;
  gr_min: Prims.int FStar_Pervasives_Native.option ;
  gr_max: Prims.int FStar_Pervasives_Native.option ;
  gr_semacts: shex_sem_act Prims.list ;
  gr_annotations: shex_annotation Prims.list }
and shex_triple_constraint =
  {
  tc_id: Prims.string FStar_Pervasives_Native.option ;
  tc_inverse: Prims.bool ;
  tc_predicate: Prims.string ;
  tc_value_expr: shex_shape_expr FStar_Pervasives_Native.option ;
  tc_min: Prims.int ;
  tc_max: Prims.int ;
  tc_semacts: shex_sem_act Prims.list ;
  tc_annotations: shex_annotation Prims.list }
let uu___is_SE_Ref (projectee : shex_shape_expr) : Prims.bool=
  match projectee with | SE_Ref _0 -> true | uu___ -> false
let __proj__SE_Ref__item___0 (projectee : shex_shape_expr) : Prims.string=
  match projectee with | SE_Ref _0 -> _0
let uu___is_SE_ShapeAnd (projectee : shex_shape_expr) : Prims.bool=
  match projectee with | SE_ShapeAnd _0 -> true | uu___ -> false
let __proj__SE_ShapeAnd__item___0 (projectee : shex_shape_expr) :
  shex_shape_expr Prims.list= match projectee with | SE_ShapeAnd _0 -> _0
let uu___is_SE_ShapeOr (projectee : shex_shape_expr) : Prims.bool=
  match projectee with | SE_ShapeOr _0 -> true | uu___ -> false
let __proj__SE_ShapeOr__item___0 (projectee : shex_shape_expr) :
  shex_shape_expr Prims.list= match projectee with | SE_ShapeOr _0 -> _0
let uu___is_SE_ShapeNot (projectee : shex_shape_expr) : Prims.bool=
  match projectee with | SE_ShapeNot _0 -> true | uu___ -> false
let __proj__SE_ShapeNot__item___0 (projectee : shex_shape_expr) :
  shex_shape_expr= match projectee with | SE_ShapeNot _0 -> _0
let uu___is_SE_NodeConstraint (projectee : shex_shape_expr) : Prims.bool=
  match projectee with | SE_NodeConstraint _0 -> true | uu___ -> false
let __proj__SE_NodeConstraint__item___0 (projectee : shex_shape_expr) :
  shex_node_constraint= match projectee with | SE_NodeConstraint _0 -> _0
let uu___is_SE_Shape (projectee : shex_shape_expr) : Prims.bool=
  match projectee with | SE_Shape _0 -> true | uu___ -> false
let __proj__SE_Shape__item___0 (projectee : shex_shape_expr) : shex_shape=
  match projectee with | SE_Shape _0 -> _0
let uu___is_SE_ShapeExternal (projectee : shex_shape_expr) : Prims.bool=
  match projectee with | SE_ShapeExternal -> true | uu___ -> false
let __proj__Mkshex_shape__item__sh_closed (projectee : shex_shape) :
  Prims.bool=
  match projectee with
  | { sh_closed; sh_extra; sh_expression; sh_semacts; sh_annotations;
      sh_extends;_} -> sh_closed
let __proj__Mkshex_shape__item__sh_extra (projectee : shex_shape) :
  Prims.string Prims.list=
  match projectee with
  | { sh_closed; sh_extra; sh_expression; sh_semacts; sh_annotations;
      sh_extends;_} -> sh_extra
let __proj__Mkshex_shape__item__sh_expression (projectee : shex_shape) :
  shex_triple_expr FStar_Pervasives_Native.option=
  match projectee with
  | { sh_closed; sh_extra; sh_expression; sh_semacts; sh_annotations;
      sh_extends;_} -> sh_expression
let __proj__Mkshex_shape__item__sh_semacts (projectee : shex_shape) :
  shex_sem_act Prims.list=
  match projectee with
  | { sh_closed; sh_extra; sh_expression; sh_semacts; sh_annotations;
      sh_extends;_} -> sh_semacts
let __proj__Mkshex_shape__item__sh_annotations (projectee : shex_shape) :
  shex_annotation Prims.list=
  match projectee with
  | { sh_closed; sh_extra; sh_expression; sh_semacts; sh_annotations;
      sh_extends;_} -> sh_annotations
let __proj__Mkshex_shape__item__sh_extends (projectee : shex_shape) :
  Prims.string Prims.list=
  match projectee with
  | { sh_closed; sh_extra; sh_expression; sh_semacts; sh_annotations;
      sh_extends;_} -> sh_extends
let uu___is_TE_Ref (projectee : shex_triple_expr) : Prims.bool=
  match projectee with | TE_Ref _0 -> true | uu___ -> false
let __proj__TE_Ref__item___0 (projectee : shex_triple_expr) : Prims.string=
  match projectee with | TE_Ref _0 -> _0
let uu___is_TE_TripleConstraint (projectee : shex_triple_expr) : Prims.bool=
  match projectee with | TE_TripleConstraint _0 -> true | uu___ -> false
let __proj__TE_TripleConstraint__item___0 (projectee : shex_triple_expr) :
  shex_triple_constraint= match projectee with | TE_TripleConstraint _0 -> _0
let uu___is_TE_EachOf (projectee : shex_triple_expr) : Prims.bool=
  match projectee with | TE_EachOf _0 -> true | uu___ -> false
let __proj__TE_EachOf__item___0 (projectee : shex_triple_expr) : shex_group=
  match projectee with | TE_EachOf _0 -> _0
let uu___is_TE_OneOf (projectee : shex_triple_expr) : Prims.bool=
  match projectee with | TE_OneOf _0 -> true | uu___ -> false
let __proj__TE_OneOf__item___0 (projectee : shex_triple_expr) : shex_group=
  match projectee with | TE_OneOf _0 -> _0
let __proj__Mkshex_group__item__gr_id (projectee : shex_group) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { gr_id; gr_expressions; gr_min; gr_max; gr_semacts; gr_annotations;_} ->
      gr_id
let __proj__Mkshex_group__item__gr_expressions (projectee : shex_group) :
  shex_triple_expr Prims.list=
  match projectee with
  | { gr_id; gr_expressions; gr_min; gr_max; gr_semacts; gr_annotations;_} ->
      gr_expressions
let __proj__Mkshex_group__item__gr_min (projectee : shex_group) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { gr_id; gr_expressions; gr_min; gr_max; gr_semacts; gr_annotations;_} ->
      gr_min
let __proj__Mkshex_group__item__gr_max (projectee : shex_group) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { gr_id; gr_expressions; gr_min; gr_max; gr_semacts; gr_annotations;_} ->
      gr_max
let __proj__Mkshex_group__item__gr_semacts (projectee : shex_group) :
  shex_sem_act Prims.list=
  match projectee with
  | { gr_id; gr_expressions; gr_min; gr_max; gr_semacts; gr_annotations;_} ->
      gr_semacts
let __proj__Mkshex_group__item__gr_annotations (projectee : shex_group) :
  shex_annotation Prims.list=
  match projectee with
  | { gr_id; gr_expressions; gr_min; gr_max; gr_semacts; gr_annotations;_} ->
      gr_annotations
let __proj__Mkshex_triple_constraint__item__tc_id
  (projectee : shex_triple_constraint) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_id
let __proj__Mkshex_triple_constraint__item__tc_inverse
  (projectee : shex_triple_constraint) : Prims.bool=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_inverse
let __proj__Mkshex_triple_constraint__item__tc_predicate
  (projectee : shex_triple_constraint) : Prims.string=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_predicate
let __proj__Mkshex_triple_constraint__item__tc_value_expr
  (projectee : shex_triple_constraint) :
  shex_shape_expr FStar_Pervasives_Native.option=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_value_expr
let __proj__Mkshex_triple_constraint__item__tc_min
  (projectee : shex_triple_constraint) : Prims.int=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_min
let __proj__Mkshex_triple_constraint__item__tc_max
  (projectee : shex_triple_constraint) : Prims.int=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_max
let __proj__Mkshex_triple_constraint__item__tc_semacts
  (projectee : shex_triple_constraint) : shex_sem_act Prims.list=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_semacts
let __proj__Mkshex_triple_constraint__item__tc_annotations
  (projectee : shex_triple_constraint) : shex_annotation Prims.list=
  match projectee with
  | { tc_id; tc_inverse; tc_predicate; tc_value_expr; tc_min; tc_max;
      tc_semacts; tc_annotations;_} -> tc_annotations
type shex_shape_decl =
  {
  sd_id: Prims.string ;
  sd_is_abstract: Prims.bool ;
  sd_expr: shex_shape_expr }
let __proj__Mkshex_shape_decl__item__sd_id (projectee : shex_shape_decl) :
  Prims.string=
  match projectee with | { sd_id; sd_is_abstract; sd_expr;_} -> sd_id
let __proj__Mkshex_shape_decl__item__sd_is_abstract
  (projectee : shex_shape_decl) : Prims.bool=
  match projectee with
  | { sd_id; sd_is_abstract; sd_expr;_} -> sd_is_abstract
let __proj__Mkshex_shape_decl__item__sd_expr (projectee : shex_shape_decl) :
  shex_shape_expr=
  match projectee with | { sd_id; sd_is_abstract; sd_expr;_} -> sd_expr
type shex_schema =
  {
  sch_start: shex_shape_expr FStar_Pervasives_Native.option ;
  sch_start_acts: shex_sem_act Prims.list ;
  sch_shapes: shex_shape_decl Prims.list ;
  sch_imports: Prims.string Prims.list }
let __proj__Mkshex_schema__item__sch_start (projectee : shex_schema) :
  shex_shape_expr FStar_Pervasives_Native.option=
  match projectee with
  | { sch_start; sch_start_acts; sch_shapes; sch_imports;_} -> sch_start
let __proj__Mkshex_schema__item__sch_start_acts (projectee : shex_schema) :
  shex_sem_act Prims.list=
  match projectee with
  | { sch_start; sch_start_acts; sch_shapes; sch_imports;_} -> sch_start_acts
let __proj__Mkshex_schema__item__sch_shapes (projectee : shex_schema) :
  shex_shape_decl Prims.list=
  match projectee with
  | { sch_start; sch_start_acts; sch_shapes; sch_imports;_} -> sch_shapes
let __proj__Mkshex_schema__item__sch_imports (projectee : shex_schema) :
  Prims.string Prims.list=
  match projectee with
  | { sch_start; sch_start_acts; sch_shapes; sch_imports;_} -> sch_imports
let decode_node_kind (s : Prims.string) :
  shex_node_kind FStar_Pervasives_Native.option=
  if s = "iri"
  then FStar_Pervasives_Native.Some ShexNK_Iri
  else
    if s = "bnode"
    then FStar_Pervasives_Native.Some ShexNK_BNode
    else
      if s = "nonliteral"
      then FStar_Pervasives_Native.Some ShexNK_NonLiteral
      else
        if s = "literal"
        then FStar_Pervasives_Native.Some ShexNK_Literal
        else FStar_Pervasives_Native.None
let resolve_against (base : Prims.string) (s : Prims.string) : Prims.string=
  if
    ((FStar_String.strlen s) >= (Prims.of_int (2))) &&
      ((FStar_String.sub s Prims.int_zero (Prims.of_int (2))) = "_:")
  then s
  else Parser_IRI.resolve_iri_v2 base s
let resolve_against_opt (base : Prims.string)
  (o : Prims.string FStar_Pervasives_Native.option) :
  Prims.string FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some s ->
      FStar_Pervasives_Native.Some (resolve_against base s)
let decode_stem (base : Prims.string) (kind : shex_vsv_kind)
  (v : Parser_JSON.json_val) : shex_stem FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString s ->
      FStar_Pervasives_Native.Some
        (ShexStemPlain
           ((match kind with
             | VSVK_Iri -> resolve_against base s
             | uu___ -> s)))
  | Parser_JSON.JObject uu___ ->
      (match Parser_JSON.json_get_string "type" v with
       | FStar_Pervasives_Native.Some "Wildcard" ->
           FStar_Pervasives_Native.Some ShexStemWildcard
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let rec decode_string_list (items : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | (Parser_JSON.JString s)::tl ->
      (match decode_string_list tl with
       | FStar_Pervasives_Native.Some rest ->
           FStar_Pervasives_Native.Some (s :: rest)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let decode_sem_act (v : Parser_JSON.json_val) :
  shex_sem_act FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_string "name" v with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some nm ->
      FStar_Pervasives_Native.Some
        { sa_name = nm; sa_code = (Parser_JSON.json_get_string "code" v) }
let rec decode_sem_act_list (items : Parser_JSON.json_val Prims.list) :
  shex_sem_act Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match decode_sem_act hd with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sa ->
           (match decode_sem_act_list tl with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some rest ->
                FStar_Pervasives_Native.Some (sa :: rest)))
let decode_object_value (v : Parser_JSON.json_val) :
  shex_object_value FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString s -> FStar_Pervasives_Native.Some (ShexOV_Iri s)
  | Parser_JSON.JObject uu___ ->
      (match Parser_JSON.json_get_string "value" v with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some value ->
           FStar_Pervasives_Native.Some
             (ShexOV_Literal
                (value, (Parser_JSON.json_get_string "language" v),
                  (Parser_JSON.json_get_string "type" v))))
  | uu___ -> FStar_Pervasives_Native.None
let decode_annotation (v : Parser_JSON.json_val) :
  shex_annotation FStar_Pervasives_Native.option=
  match ((Parser_JSON.json_get_string "predicate" v),
          (Parser_JSON.json_get_field "object" v))
  with
  | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.Some ov) ->
      (match decode_object_value ov with
       | FStar_Pervasives_Native.Some ovv ->
           FStar_Pervasives_Native.Some { an_predicate = p; an_object = ovv }
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let rec decode_annotation_list (items : Parser_JSON.json_val Prims.list) :
  shex_annotation Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match decode_annotation hd with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some an ->
           (match decode_annotation_list tl with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some rest ->
                FStar_Pervasives_Native.Some (an :: rest)))
let rec decode_shape_expr (base : Prims.string) (v : Parser_JSON.json_val)
  (fuel : Prims.nat) : shex_shape_expr FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match v with
     | Parser_JSON.JString s ->
         FStar_Pervasives_Native.Some (SE_Ref (resolve_against base s))
     | Parser_JSON.JObject uu___1 ->
         (match Parser_JSON.json_get_string "type" v with
          | FStar_Pervasives_Native.Some "ShapeAnd" ->
              (match Parser_JSON.json_get_array "shapeExprs" v with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some items ->
                   (match decode_shape_expr_list base items
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.Some ses ->
                        FStar_Pervasives_Native.Some (SE_ShapeAnd ses)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None))
          | FStar_Pervasives_Native.Some "ShapeOr" ->
              (match Parser_JSON.json_get_array "shapeExprs" v with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some items ->
                   (match decode_shape_expr_list base items
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.Some ses ->
                        FStar_Pervasives_Native.Some (SE_ShapeOr ses)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None))
          | FStar_Pervasives_Native.Some "ShapeNot" ->
              (match Parser_JSON.json_get_field "shapeExpr" v with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some sub ->
                   (match decode_shape_expr base sub (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.Some se ->
                        FStar_Pervasives_Native.Some (SE_ShapeNot se)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None))
          | FStar_Pervasives_Native.Some "NodeConstraint" ->
              (match decode_node_constraint base v (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.Some nc ->
                   FStar_Pervasives_Native.Some (SE_NodeConstraint nc)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.Some "Shape" ->
              (match decode_shape base v (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.Some sh ->
                   FStar_Pervasives_Native.Some (SE_Shape sh)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.Some "ShapeExternal" ->
              FStar_Pervasives_Native.Some SE_ShapeExternal
          | uu___2 -> FStar_Pervasives_Native.None)
     | uu___1 -> FStar_Pervasives_Native.None)
and decode_shape_expr_list (base : Prims.string)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  shex_shape_expr Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::tl ->
         (match decode_shape_expr base hd (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some se ->
              (match decode_shape_expr_list base tl (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some rest ->
                   FStar_Pervasives_Native.Some (se :: rest))))
and decode_shape (base : Prims.string) (v : Parser_JSON.json_val)
  (fuel : Prims.nat) : shex_shape FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let uu___1 =
       match Parser_JSON.json_get_field "expression" v with
       | FStar_Pervasives_Native.None -> (true, FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.Some ej ->
           (match decode_triple_expr base ej (fuel - Prims.int_one) with
            | FStar_Pervasives_Native.Some te ->
                (true, (FStar_Pervasives_Native.Some te))
            | FStar_Pervasives_Native.None ->
                (false, FStar_Pervasives_Native.None)) in
     match uu___1 with
     | (expr_ok, expr) ->
         if Prims.op_Negation expr_ok
         then FStar_Pervasives_Native.None
         else
           (let uu___3 =
              match Parser_JSON.json_get_array "extra" v with
              | FStar_Pervasives_Native.None -> (true, [])
              | FStar_Pervasives_Native.Some items ->
                  (match decode_string_list items with
                   | FStar_Pervasives_Native.Some l -> (true, l)
                   | FStar_Pervasives_Native.None -> (false, [])) in
            match uu___3 with
            | (extra_ok, extra) ->
                if Prims.op_Negation extra_ok
                then FStar_Pervasives_Native.None
                else
                  (let uu___5 =
                     match Parser_JSON.json_get_array "semActs" v with
                     | FStar_Pervasives_Native.None -> (true, [])
                     | FStar_Pervasives_Native.Some items ->
                         (match decode_sem_act_list items with
                          | FStar_Pervasives_Native.Some sa -> (true, sa)
                          | FStar_Pervasives_Native.None -> (false, [])) in
                   match uu___5 with
                   | (semacts_ok, semacts) ->
                       if Prims.op_Negation semacts_ok
                       then FStar_Pervasives_Native.None
                       else
                         (let uu___7 =
                            match Parser_JSON.json_get_array "annotations" v
                            with
                            | FStar_Pervasives_Native.None -> (true, [])
                            | FStar_Pervasives_Native.Some items ->
                                (match decode_annotation_list items with
                                 | FStar_Pervasives_Native.Some an ->
                                     (true, an)
                                 | FStar_Pervasives_Native.None ->
                                     (false, [])) in
                          match uu___7 with
                          | (annots_ok, annots) ->
                              if Prims.op_Negation annots_ok
                              then FStar_Pervasives_Native.None
                              else
                                (let uu___9 =
                                   match Parser_JSON.json_get_array "extends"
                                           v
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       (true, [])
                                   | FStar_Pervasives_Native.Some items ->
                                       (match decode_string_list items with
                                        | FStar_Pervasives_Native.Some l ->
                                            (true, l)
                                        | FStar_Pervasives_Native.None ->
                                            (false, [])) in
                                 match uu___9 with
                                 | (extends_ok, extends) ->
                                     if Prims.op_Negation extends_ok
                                     then FStar_Pervasives_Native.None
                                     else
                                       FStar_Pervasives_Native.Some
                                         {
                                           sh_closed =
                                             (json_get_bool_default "closed"
                                                v false);
                                           sh_extra = extra;
                                           sh_expression = expr;
                                           sh_semacts = semacts;
                                           sh_annotations = annots;
                                           sh_extends = extends
                                         })))))
and decode_triple_expr (base : Prims.string) (v : Parser_JSON.json_val)
  (fuel : Prims.nat) : shex_triple_expr FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match v with
     | Parser_JSON.JString s ->
         FStar_Pervasives_Native.Some (TE_Ref (resolve_against base s))
     | Parser_JSON.JObject uu___1 ->
         (match Parser_JSON.json_get_string "type" v with
          | FStar_Pervasives_Native.Some "TripleConstraint" ->
              (match decode_triple_constraint base v (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.Some tc ->
                   FStar_Pervasives_Native.Some (TE_TripleConstraint tc)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.Some "EachOf" ->
              (match decode_group base v (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.Some g ->
                   FStar_Pervasives_Native.Some (TE_EachOf g)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.Some "OneOf" ->
              (match decode_group base v (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.Some g ->
                   FStar_Pervasives_Native.Some (TE_OneOf g)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          | uu___2 -> FStar_Pervasives_Native.None)
     | uu___1 -> FStar_Pervasives_Native.None)
and decode_triple_expr_list (base : Prims.string)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  shex_triple_expr Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::tl ->
         (match decode_triple_expr base hd (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some te ->
              (match decode_triple_expr_list base tl (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some rest ->
                   FStar_Pervasives_Native.Some (te :: rest))))
and decode_group (base : Prims.string) (v : Parser_JSON.json_val)
  (fuel : Prims.nat) : shex_group FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match Parser_JSON.json_get_array "expressions" v with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some items ->
         (match decode_triple_expr_list base items (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some exprs ->
              let uu___1 =
                match Parser_JSON.json_get_array "semActs" v with
                | FStar_Pervasives_Native.None -> (true, [])
                | FStar_Pervasives_Native.Some sitems ->
                    (match decode_sem_act_list sitems with
                     | FStar_Pervasives_Native.Some sa -> (true, sa)
                     | FStar_Pervasives_Native.None -> (false, [])) in
              (match uu___1 with
               | (semacts_ok, semacts) ->
                   if Prims.op_Negation semacts_ok
                   then FStar_Pervasives_Native.None
                   else
                     (let uu___3 =
                        match Parser_JSON.json_get_array "annotations" v with
                        | FStar_Pervasives_Native.None -> (true, [])
                        | FStar_Pervasives_Native.Some aitems ->
                            (match decode_annotation_list aitems with
                             | FStar_Pervasives_Native.Some an -> (true, an)
                             | FStar_Pervasives_Native.None -> (false, [])) in
                      match uu___3 with
                      | (annots_ok, annots) ->
                          if Prims.op_Negation annots_ok
                          then FStar_Pervasives_Native.None
                          else
                            FStar_Pervasives_Native.Some
                              {
                                gr_id = (Parser_JSON.json_get_string "id" v);
                                gr_expressions = exprs;
                                gr_min = (json_get_int "min" v);
                                gr_max = (json_get_int "max" v);
                                gr_semacts = semacts;
                                gr_annotations = annots
                              }))))
and decode_triple_constraint (base : Prims.string) (v : Parser_JSON.json_val)
  (fuel : Prims.nat) : shex_triple_constraint FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match Parser_JSON.json_get_string "predicate" v with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some pred ->
         let uu___1 =
           match Parser_JSON.json_get_field "valueExpr" v with
           | FStar_Pervasives_Native.None ->
               (true, FStar_Pervasives_Native.None)
           | FStar_Pervasives_Native.Some vej ->
               (match decode_shape_expr base vej (fuel - Prims.int_one) with
                | FStar_Pervasives_Native.Some se ->
                    (true, (FStar_Pervasives_Native.Some se))
                | FStar_Pervasives_Native.None ->
                    (false, FStar_Pervasives_Native.None)) in
         (match uu___1 with
          | (ve_ok, ve) ->
              if Prims.op_Negation ve_ok
              then FStar_Pervasives_Native.None
              else
                (let uu___3 =
                   match Parser_JSON.json_get_array "semActs" v with
                   | FStar_Pervasives_Native.None -> (true, [])
                   | FStar_Pervasives_Native.Some items ->
                       (match decode_sem_act_list items with
                        | FStar_Pervasives_Native.Some sa -> (true, sa)
                        | FStar_Pervasives_Native.None -> (false, [])) in
                 match uu___3 with
                 | (semacts_ok, semacts) ->
                     if Prims.op_Negation semacts_ok
                     then FStar_Pervasives_Native.None
                     else
                       (let uu___5 =
                          match Parser_JSON.json_get_array "annotations" v
                          with
                          | FStar_Pervasives_Native.None -> (true, [])
                          | FStar_Pervasives_Native.Some items ->
                              (match decode_annotation_list items with
                               | FStar_Pervasives_Native.Some an ->
                                   (true, an)
                               | FStar_Pervasives_Native.None -> (false, [])) in
                        match uu___5 with
                        | (annots_ok, annots) ->
                            if Prims.op_Negation annots_ok
                            then FStar_Pervasives_Native.None
                            else
                              FStar_Pervasives_Native.Some
                                {
                                  tc_id =
                                    (Parser_JSON.json_get_string "id" v);
                                  tc_inverse =
                                    (json_get_bool_default "inverse" v false);
                                  tc_predicate = (resolve_against base pred);
                                  tc_value_expr = ve;
                                  tc_min =
                                    (json_get_int_default "min" v
                                       Prims.int_one);
                                  tc_max =
                                    (json_get_int_default "max" v
                                       Prims.int_one);
                                  tc_semacts = semacts;
                                  tc_annotations = annots
                                }))))
and decode_node_constraint (base : Prims.string) (v : Parser_JSON.json_val)
  (fuel : Prims.nat) : shex_node_constraint FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let uu___1 =
       match Parser_JSON.json_get_string "nodeKind" v with
       | FStar_Pervasives_Native.None -> (true, FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.Some s ->
           (match decode_node_kind s with
            | FStar_Pervasives_Native.Some k ->
                (true, (FStar_Pervasives_Native.Some k))
            | FStar_Pervasives_Native.None ->
                (false, FStar_Pervasives_Native.None)) in
     match uu___1 with
     | (nk_ok, nk) ->
         if Prims.op_Negation nk_ok
         then FStar_Pervasives_Native.None
         else
           (let uu___3 =
              match Parser_JSON.json_get_array "values" v with
              | FStar_Pervasives_Native.None -> (true, [])
              | FStar_Pervasives_Native.Some items ->
                  (match decode_value_set_value_list base items
                           (fuel - Prims.int_one)
                   with
                   | FStar_Pervasives_Native.Some vs -> (true, vs)
                   | FStar_Pervasives_Native.None -> (false, [])) in
            match uu___3 with
            | (values_ok, values) ->
                if Prims.op_Negation values_ok
                then FStar_Pervasives_Native.None
                else
                  FStar_Pervasives_Native.Some
                    {
                      nc_node_kind = nk;
                      nc_datatype =
                        (resolve_against_opt base
                           (Parser_JSON.json_get_string "datatype" v));
                      nc_values = values;
                      nc_length = (json_get_int "length" v);
                      nc_minlength = (json_get_int "minlength" v);
                      nc_maxlength = (json_get_int "maxlength" v);
                      nc_pattern = (Parser_JSON.json_get_string "pattern" v);
                      nc_flags = (Parser_JSON.json_get_string "flags" v);
                      nc_mininclusive =
                        (json_get_number_lexeme "mininclusive" v);
                      nc_maxinclusive =
                        (json_get_number_lexeme "maxinclusive" v);
                      nc_minexclusive =
                        (json_get_number_lexeme "minexclusive" v);
                      nc_maxexclusive =
                        (json_get_number_lexeme "maxexclusive" v);
                      nc_totaldigits = (json_get_int "totaldigits" v);
                      nc_fractiondigits = (json_get_int "fractiondigits" v)
                    }))
and decode_value_set_value (base : Prims.string) (v : Parser_JSON.json_val)
  (fuel : Prims.nat) : shex_value_set_value FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match v with
     | Parser_JSON.JString s ->
         FStar_Pervasives_Native.Some
           (VSV_Value (ShexOV_Iri (resolve_against base s)))
     | Parser_JSON.JObject uu___1 ->
         (match Parser_JSON.json_get_string "value" v with
          | FStar_Pervasives_Native.Some value ->
              FStar_Pervasives_Native.Some
                (VSV_Value
                   (ShexOV_Literal
                      (value, (Parser_JSON.json_get_string "language" v),
                        (Parser_JSON.json_get_string "type" v))))
          | FStar_Pervasives_Native.None ->
              (match Parser_JSON.json_get_string "type" v with
               | FStar_Pervasives_Native.Some "IriStem" ->
                   (match Parser_JSON.json_get_field "stem" v with
                    | FStar_Pervasives_Native.Some stv ->
                        (match decode_stem base VSVK_Iri stv with
                         | FStar_Pervasives_Native.Some st ->
                             FStar_Pervasives_Native.Some (VSV_IriStem st)
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some "LiteralStem" ->
                   (match Parser_JSON.json_get_field "stem" v with
                    | FStar_Pervasives_Native.Some stv ->
                        (match decode_stem base VSVK_Literal stv with
                         | FStar_Pervasives_Native.Some st ->
                             FStar_Pervasives_Native.Some
                               (VSV_LiteralStem st)
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some "LanguageStem" ->
                   (match Parser_JSON.json_get_field "stem" v with
                    | FStar_Pervasives_Native.Some stv ->
                        (match decode_stem base VSVK_Language stv with
                         | FStar_Pervasives_Native.Some st ->
                             FStar_Pervasives_Native.Some
                               (VSV_LanguageStem st)
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some "Language" ->
                   (match Parser_JSON.json_get_string "languageTag" v with
                    | FStar_Pervasives_Native.Some lt ->
                        FStar_Pervasives_Native.Some (VSV_Language lt)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some "IriStemRange" ->
                   (match decode_stem_range_parts base v VSVK_Iri
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.Some (st, excl) ->
                        FStar_Pervasives_Native.Some
                          (VSV_IriStemRange (st, excl))
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some "LiteralStemRange" ->
                   (match decode_stem_range_parts base v VSVK_Literal
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.Some (st, excl) ->
                        FStar_Pervasives_Native.Some
                          (VSV_LiteralStemRange (st, excl))
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some "LanguageStemRange" ->
                   (match decode_stem_range_parts base v VSVK_Language
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.Some (st, excl) ->
                        FStar_Pervasives_Native.Some
                          (VSV_LanguageStemRange (st, excl))
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | uu___2 -> FStar_Pervasives_Native.None))
     | uu___1 -> FStar_Pervasives_Native.None)
and decode_value_set_value_list (base : Prims.string)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  shex_value_set_value Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::tl ->
         (match decode_value_set_value base hd (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some vv ->
              (match decode_value_set_value_list base tl
                       (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some rest ->
                   FStar_Pervasives_Native.Some (vv :: rest))))
and decode_value_set_value_list_kind (base : Prims.string)
  (items : Parser_JSON.json_val Prims.list) (kind : shex_vsv_kind)
  (fuel : Prims.nat) :
  shex_value_set_value Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | (Parser_JSON.JString s)::tl ->
         (match decode_value_set_value_list_kind base tl kind
                  (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rest ->
              FStar_Pervasives_Native.Some ((decode_bare_vsv_string kind s)
                :: rest))
     | hd::tl ->
         (match decode_value_set_value base hd (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some vv ->
              (match decode_value_set_value_list_kind base tl kind
                       (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some rest ->
                   FStar_Pervasives_Native.Some (vv :: rest))))
and decode_stem_range_parts (base : Prims.string) (v : Parser_JSON.json_val)
  (kind : shex_vsv_kind) (fuel : Prims.nat) :
  (shex_stem * shex_value_set_value Prims.list)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match Parser_JSON.json_get_field "stem" v with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some stv ->
         (match decode_stem base kind stv with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some st ->
              (match Parser_JSON.json_get_array "exclusions" v with
               | FStar_Pervasives_Native.None ->
                   FStar_Pervasives_Native.Some (st, [])
               | FStar_Pervasives_Native.Some items ->
                   (match decode_value_set_value_list_kind base items kind
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.Some excl ->
                        FStar_Pervasives_Native.Some (st, excl)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None))))
let decode_shape_decl (base : Prims.string) (v : Parser_JSON.json_val) :
  shex_shape_decl FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_string "id" v with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some sid ->
      let sej =
        match Parser_JSON.json_get_field "shapeExpr" v with
        | FStar_Pervasives_Native.Some nested -> nested
        | FStar_Pervasives_Native.None -> v in
      (match decode_shape_expr base sej (Parser_JSON.json_size sej) with
       | FStar_Pervasives_Native.Some se ->
           FStar_Pervasives_Native.Some
             {
               sd_id = (resolve_against base sid);
               sd_is_abstract = (json_get_bool_default "abstract" v false);
               sd_expr = se
             }
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec decode_shape_decl_list (base : Prims.string)
  (items : Parser_JSON.json_val Prims.list) :
  shex_shape_decl Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match decode_shape_decl base hd with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some sd ->
           (match decode_shape_decl_list base tl with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some rest ->
                FStar_Pervasives_Native.Some (sd :: rest)))
let decode_schema (base : Prims.string) (v : Parser_JSON.json_val) :
  shex_schema FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_string "type" v with
  | FStar_Pervasives_Native.Some "Schema" ->
      let uu___ =
        match Parser_JSON.json_get_field "start" v with
        | FStar_Pervasives_Native.None ->
            (true, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some sv ->
            (match decode_shape_expr base sv (Parser_JSON.json_size sv) with
             | FStar_Pervasives_Native.Some se ->
                 (true, (FStar_Pervasives_Native.Some se))
             | FStar_Pervasives_Native.None ->
                 (false, FStar_Pervasives_Native.None)) in
      (match uu___ with
       | (start_ok, start) ->
           if Prims.op_Negation start_ok
           then FStar_Pervasives_Native.None
           else
             (let uu___2 =
                match Parser_JSON.json_get_array "startActs" v with
                | FStar_Pervasives_Native.None -> (true, [])
                | FStar_Pervasives_Native.Some items ->
                    (match decode_sem_act_list items with
                     | FStar_Pervasives_Native.Some sa -> (true, sa)
                     | FStar_Pervasives_Native.None -> (false, [])) in
              match uu___2 with
              | (startacts_ok, startacts) ->
                  if Prims.op_Negation startacts_ok
                  then FStar_Pervasives_Native.None
                  else
                    (let uu___4 =
                       match Parser_JSON.json_get_array "shapes" v with
                       | FStar_Pervasives_Native.None -> (true, [])
                       | FStar_Pervasives_Native.Some items ->
                           (match decode_shape_decl_list base items with
                            | FStar_Pervasives_Native.Some sd -> (true, sd)
                            | FStar_Pervasives_Native.None -> (false, [])) in
                     match uu___4 with
                     | (shapes_ok, shapes) ->
                         if Prims.op_Negation shapes_ok
                         then FStar_Pervasives_Native.None
                         else
                           (let uu___6 =
                              match Parser_JSON.json_get_array "imports" v
                              with
                              | FStar_Pervasives_Native.None -> (true, [])
                              | FStar_Pervasives_Native.Some items ->
                                  (match decode_string_list items with
                                   | FStar_Pervasives_Native.Some l ->
                                       (true, l)
                                   | FStar_Pervasives_Native.None ->
                                       (false, [])) in
                            match uu___6 with
                            | (imports_ok, imports) ->
                                if Prims.op_Negation imports_ok
                                then FStar_Pervasives_Native.None
                                else
                                  FStar_Pervasives_Native.Some
                                    {
                                      sch_start = start;
                                      sch_start_acts = startacts;
                                      sch_shapes = shapes;
                                      sch_imports = imports
                                    }))))
  | uu___ -> FStar_Pervasives_Native.None
let decode_shex_schema (input : Prims.string) (base : Prims.string) :
  shex_schema FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> decode_schema base v
