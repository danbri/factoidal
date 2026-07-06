open Prims
let scaled_eq (mant_a : Prims.int) (scale_a : Prims.nat) (mant_b : Prims.int)
  (scale_b : Prims.nat) : Prims.bool=
  if scale_a <= scale_b
  then (mant_a * (SPARQL11_Algebra.pow10 (scale_b - scale_a))) = mant_b
  else (mant_b * (SPARQL11_Algebra.pow10 (scale_a - scale_b))) = mant_a
let numeric_lexeme_eq (a : Prims.string) (b : Prims.string) : Prims.bool=
  match ((SPARQL11_Algebra.parse_double_to_scaled a),
          (SPARQL11_Algebra.parse_double_to_scaled b))
  with
  | (FStar_Pervasives_Native.Some (mant_a, scale_a),
     FStar_Pervasives_Native.Some (mant_b, scale_b)) ->
      scaled_eq mant_a scale_a mant_b scale_b
  | uu___ -> a = b
let opt_numeric_lexeme_eq (a : Prims.string FStar_Pervasives_Native.option)
  (b : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  match (a, b) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
      numeric_lexeme_eq x y
  | uu___ -> false
let opt_str_eq (a : Prims.string FStar_Pervasives_Native.option)
  (b : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  match (a, b) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) -> x = y
  | uu___ -> false
let opt_int_eq (a : Prims.int FStar_Pervasives_Native.option)
  (b : Prims.int FStar_Pervasives_Native.option) : Prims.bool=
  match (a, b) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) -> x = y
  | uu___ -> false
let rec remove_one :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a -> 'a Prims.list -> 'a Prims.list FStar_Pervasives_Native.option
  =
  fun eq x xs ->
    match xs with
    | [] -> FStar_Pervasives_Native.None
    | hd::tl ->
        if eq x hd
        then FStar_Pervasives_Native.Some tl
        else
          (match remove_one eq x tl with
           | FStar_Pervasives_Native.Some tl' ->
               FStar_Pervasives_Native.Some (hd :: tl')
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec multiset_eq :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq xs ys ->
    match xs with
    | [] -> (match ys with | [] -> true | uu___ -> false)
    | hd::tl ->
        (match remove_one eq hd ys with
         | FStar_Pervasives_Native.None -> false
         | FStar_Pervasives_Native.Some ys' -> multiset_eq eq tl ys')
let string_multiset_eq (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) : Prims.bool=
  multiset_eq (fun a b -> a = b) xs ys
let node_kind_eq (a : ShEx_Schema.shex_node_kind)
  (b : ShEx_Schema.shex_node_kind) : Prims.bool= a = b
let stem_eq (a : ShEx_Schema.shex_stem) (b : ShEx_Schema.shex_stem) :
  Prims.bool=
  match (a, b) with
  | (ShEx_Schema.ShexStemWildcard, ShEx_Schema.ShexStemWildcard) -> true
  | (ShEx_Schema.ShexStemPlain x, ShEx_Schema.ShexStemPlain y) -> x = y
  | uu___ -> false
let object_value_eq (a : ShEx_Schema.shex_object_value)
  (b : ShEx_Schema.shex_object_value) : Prims.bool=
  match (a, b) with
  | (ShEx_Schema.ShexOV_Iri x, ShEx_Schema.ShexOV_Iri y) -> x = y
  | (ShEx_Schema.ShexOV_Literal (v1, l1, d1), ShEx_Schema.ShexOV_Literal
     (v2, l2, d2)) -> ((v1 = v2) && (opt_str_eq l1 l2)) && (opt_str_eq d1 d2)
  | uu___ -> false
let sem_act_eq (a : ShEx_Schema.shex_sem_act) (b : ShEx_Schema.shex_sem_act)
  : Prims.bool=
  (a.ShEx_Schema.sa_name = b.ShEx_Schema.sa_name) &&
    (opt_str_eq a.ShEx_Schema.sa_code b.ShEx_Schema.sa_code)
let rec sem_act_list_eq (a : ShEx_Schema.shex_sem_act Prims.list)
  (b : ShEx_Schema.shex_sem_act Prims.list) : Prims.bool=
  match (a, b) with
  | ([], []) -> true
  | (x::xs, y::ys) -> (sem_act_eq x y) && (sem_act_list_eq xs ys)
  | uu___ -> false
let annotation_eq (a : ShEx_Schema.shex_annotation)
  (b : ShEx_Schema.shex_annotation) : Prims.bool=
  (a.ShEx_Schema.an_predicate = b.ShEx_Schema.an_predicate) &&
    (object_value_eq a.ShEx_Schema.an_object b.ShEx_Schema.an_object)
let rec annotation_list_eq (a : ShEx_Schema.shex_annotation Prims.list)
  (b : ShEx_Schema.shex_annotation Prims.list) : Prims.bool=
  match (a, b) with
  | ([], []) -> true
  | (x::xs, y::ys) -> (annotation_eq x y) && (annotation_list_eq xs ys)
  | uu___ -> false
let rec value_set_value_eq (a : ShEx_Schema.shex_value_set_value)
  (b : ShEx_Schema.shex_value_set_value) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (a, b) with
     | (ShEx_Schema.VSV_Value x, ShEx_Schema.VSV_Value y) ->
         object_value_eq x y
     | (ShEx_Schema.VSV_IriStem x, ShEx_Schema.VSV_IriStem y) -> stem_eq x y
     | (ShEx_Schema.VSV_LiteralStem x, ShEx_Schema.VSV_LiteralStem y) ->
         stem_eq x y
     | (ShEx_Schema.VSV_LanguageStem x, ShEx_Schema.VSV_LanguageStem y) ->
         stem_eq x y
     | (ShEx_Schema.VSV_Language x, ShEx_Schema.VSV_Language y) -> x = y
     | (ShEx_Schema.VSV_IriStemRange (sx, ex), ShEx_Schema.VSV_IriStemRange
        (sy, ey)) ->
         (stem_eq sx sy) &&
           (value_set_value_multiset_eq ex ey (fuel - Prims.int_one))
     | (ShEx_Schema.VSV_LiteralStemRange (sx, ex),
        ShEx_Schema.VSV_LiteralStemRange (sy, ey)) ->
         (stem_eq sx sy) &&
           (value_set_value_multiset_eq ex ey (fuel - Prims.int_one))
     | (ShEx_Schema.VSV_LanguageStemRange (sx, ex),
        ShEx_Schema.VSV_LanguageStemRange (sy, ey)) ->
         (stem_eq sx sy) &&
           (value_set_value_multiset_eq ex ey (fuel - Prims.int_one))
     | uu___1 -> false)
and value_set_value_multiset_eq
  (xs : ShEx_Schema.shex_value_set_value Prims.list)
  (ys : ShEx_Schema.shex_value_set_value Prims.list) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match xs with
     | [] -> (match ys with | [] -> true | uu___1 -> false)
     | hd::tl ->
         (match remove_one_vsv hd ys (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some ys' ->
              value_set_value_multiset_eq tl ys' (fuel - Prims.int_one)))
and remove_one_vsv (x : ShEx_Schema.shex_value_set_value)
  (xs : ShEx_Schema.shex_value_set_value Prims.list) (fuel : Prims.nat) :
  ShEx_Schema.shex_value_set_value Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match xs with
     | [] -> FStar_Pervasives_Native.None
     | hd::tl ->
         if value_set_value_eq x hd (fuel - Prims.int_one)
         then FStar_Pervasives_Native.Some tl
         else
           (match remove_one_vsv x tl (fuel - Prims.int_one) with
            | FStar_Pervasives_Native.Some tl' ->
                FStar_Pervasives_Native.Some (hd :: tl')
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let node_constraint_eq (a : ShEx_Schema.shex_node_constraint)
  (b : ShEx_Schema.shex_node_constraint) : Prims.bool=
  (((((((((((((match ((a.ShEx_Schema.nc_node_kind),
                       (b.ShEx_Schema.nc_node_kind))
               with
               | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                   -> true
               | (FStar_Pervasives_Native.Some x,
                  FStar_Pervasives_Native.Some y) -> node_kind_eq x y
               | uu___ -> false) &&
                (opt_str_eq a.ShEx_Schema.nc_datatype
                   b.ShEx_Schema.nc_datatype))
               &&
               (value_set_value_multiset_eq a.ShEx_Schema.nc_values
                  b.ShEx_Schema.nc_values (Prims.of_int (10000))))
              && (opt_int_eq a.ShEx_Schema.nc_length b.ShEx_Schema.nc_length))
             &&
             (opt_int_eq a.ShEx_Schema.nc_minlength
                b.ShEx_Schema.nc_minlength))
            &&
            (opt_int_eq a.ShEx_Schema.nc_maxlength b.ShEx_Schema.nc_maxlength))
           && (opt_str_eq a.ShEx_Schema.nc_pattern b.ShEx_Schema.nc_pattern))
          && (opt_str_eq a.ShEx_Schema.nc_flags b.ShEx_Schema.nc_flags))
         &&
         (opt_numeric_lexeme_eq a.ShEx_Schema.nc_mininclusive
            b.ShEx_Schema.nc_mininclusive))
        &&
        (opt_numeric_lexeme_eq a.ShEx_Schema.nc_maxinclusive
           b.ShEx_Schema.nc_maxinclusive))
       &&
       (opt_numeric_lexeme_eq a.ShEx_Schema.nc_minexclusive
          b.ShEx_Schema.nc_minexclusive))
      &&
      (opt_numeric_lexeme_eq a.ShEx_Schema.nc_maxexclusive
         b.ShEx_Schema.nc_maxexclusive))
     &&
     (opt_int_eq a.ShEx_Schema.nc_totaldigits b.ShEx_Schema.nc_totaldigits))
    &&
    (opt_int_eq a.ShEx_Schema.nc_fractiondigits
       b.ShEx_Schema.nc_fractiondigits)
let rec shape_expr_eq (a : ShEx_Schema.shex_shape_expr)
  (b : ShEx_Schema.shex_shape_expr) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (a, b) with
     | (ShEx_Schema.SE_Ref x, ShEx_Schema.SE_Ref y) -> x = y
     | (ShEx_Schema.SE_ShapeAnd xs, ShEx_Schema.SE_ShapeAnd ys) ->
         shape_expr_list_eq xs ys (fuel - Prims.int_one)
     | (ShEx_Schema.SE_ShapeOr xs, ShEx_Schema.SE_ShapeOr ys) ->
         shape_expr_list_eq xs ys (fuel - Prims.int_one)
     | (ShEx_Schema.SE_ShapeNot x, ShEx_Schema.SE_ShapeNot y) ->
         shape_expr_eq x y (fuel - Prims.int_one)
     | (ShEx_Schema.SE_NodeConstraint x, ShEx_Schema.SE_NodeConstraint y) ->
         node_constraint_eq x y
     | (ShEx_Schema.SE_Shape x, ShEx_Schema.SE_Shape y) ->
         shape_eq x y (fuel - Prims.int_one)
     | (ShEx_Schema.SE_ShapeExternal, ShEx_Schema.SE_ShapeExternal) -> true
     | uu___1 -> false)
and shape_expr_list_eq (a : ShEx_Schema.shex_shape_expr Prims.list)
  (b : ShEx_Schema.shex_shape_expr Prims.list) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (a, b) with
     | ([], []) -> true
     | (x::xs, y::ys) ->
         (shape_expr_eq x y (fuel - Prims.int_one)) &&
           (shape_expr_list_eq xs ys (fuel - Prims.int_one))
     | uu___1 -> false)
and shape_eq (a : ShEx_Schema.shex_shape) (b : ShEx_Schema.shex_shape)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (((((a.ShEx_Schema.sh_closed = b.ShEx_Schema.sh_closed) &&
          (string_multiset_eq a.ShEx_Schema.sh_extra b.ShEx_Schema.sh_extra))
         &&
         (string_multiset_eq a.ShEx_Schema.sh_extends
            b.ShEx_Schema.sh_extends))
        &&
        (sem_act_list_eq a.ShEx_Schema.sh_semacts b.ShEx_Schema.sh_semacts))
       &&
       (annotation_list_eq a.ShEx_Schema.sh_annotations
          b.ShEx_Schema.sh_annotations))
      &&
      ((match ((a.ShEx_Schema.sh_expression), (b.ShEx_Schema.sh_expression))
        with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
            triple_expr_eq x y (fuel - Prims.int_one)
        | uu___1 -> false))
and triple_expr_eq (a : ShEx_Schema.shex_triple_expr)
  (b : ShEx_Schema.shex_triple_expr) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (a, b) with
     | (ShEx_Schema.TE_Ref x, ShEx_Schema.TE_Ref y) -> x = y
     | (ShEx_Schema.TE_TripleConstraint x, ShEx_Schema.TE_TripleConstraint y)
         -> triple_constraint_eq x y (fuel - Prims.int_one)
     | (ShEx_Schema.TE_EachOf x, ShEx_Schema.TE_EachOf y) ->
         group_eq x y (fuel - Prims.int_one)
     | (ShEx_Schema.TE_OneOf x, ShEx_Schema.TE_OneOf y) ->
         group_eq x y (fuel - Prims.int_one)
     | uu___1 -> false)
and triple_expr_list_eq (a : ShEx_Schema.shex_triple_expr Prims.list)
  (b : ShEx_Schema.shex_triple_expr Prims.list) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (a, b) with
     | ([], []) -> true
     | (x::xs, y::ys) ->
         (triple_expr_eq x y (fuel - Prims.int_one)) &&
           (triple_expr_list_eq xs ys (fuel - Prims.int_one))
     | uu___1 -> false)
and group_eq (a : ShEx_Schema.shex_group) (b : ShEx_Schema.shex_group)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    ((((opt_int_eq a.ShEx_Schema.gr_min b.ShEx_Schema.gr_min) &&
         (opt_int_eq a.ShEx_Schema.gr_max b.ShEx_Schema.gr_max))
        &&
        (sem_act_list_eq a.ShEx_Schema.gr_semacts b.ShEx_Schema.gr_semacts))
       &&
       (annotation_list_eq a.ShEx_Schema.gr_annotations
          b.ShEx_Schema.gr_annotations))
      &&
      (triple_expr_list_eq a.ShEx_Schema.gr_expressions
         b.ShEx_Schema.gr_expressions (fuel - Prims.int_one))
and triple_constraint_eq (a : ShEx_Schema.shex_triple_constraint)
  (b : ShEx_Schema.shex_triple_constraint) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    ((((((a.ShEx_Schema.tc_inverse = b.ShEx_Schema.tc_inverse) &&
           (a.ShEx_Schema.tc_predicate = b.ShEx_Schema.tc_predicate))
          && (a.ShEx_Schema.tc_min = b.ShEx_Schema.tc_min))
         && (a.ShEx_Schema.tc_max = b.ShEx_Schema.tc_max))
        &&
        (sem_act_list_eq a.ShEx_Schema.tc_semacts b.ShEx_Schema.tc_semacts))
       &&
       (annotation_list_eq a.ShEx_Schema.tc_annotations
          b.ShEx_Schema.tc_annotations))
      &&
      ((match ((a.ShEx_Schema.tc_value_expr), (b.ShEx_Schema.tc_value_expr))
        with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
            shape_expr_eq x y (fuel - Prims.int_one)
        | uu___1 -> false))
let shape_decl_eq (a : ShEx_Schema.shex_shape_decl)
  (b : ShEx_Schema.shex_shape_decl) (fuel : Prims.nat) : Prims.bool=
  ((a.ShEx_Schema.sd_id = b.ShEx_Schema.sd_id) &&
     (a.ShEx_Schema.sd_is_abstract = b.ShEx_Schema.sd_is_abstract))
    && (shape_expr_eq a.ShEx_Schema.sd_expr b.ShEx_Schema.sd_expr fuel)
let rec shape_decl_list_eq (a : ShEx_Schema.shex_shape_decl Prims.list)
  (b : ShEx_Schema.shex_shape_decl Prims.list) (fuel : Prims.nat) :
  Prims.bool=
  match (a, b) with
  | ([], []) -> true
  | (x::xs, y::ys) ->
      (shape_decl_eq x y fuel) && (shape_decl_list_eq xs ys fuel)
  | uu___ -> false
let schema_eq_fuel : Prims.nat= (Prims.parse_int "200000")
let shex_schema_equal (a : ShEx_Schema.shex_schema)
  (b : ShEx_Schema.shex_schema) : Prims.bool=
  (((match ((a.ShEx_Schema.sch_start), (b.ShEx_Schema.sch_start)) with
     | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         shape_expr_eq x y schema_eq_fuel
     | uu___ -> false) &&
      (sem_act_list_eq a.ShEx_Schema.sch_start_acts
         b.ShEx_Schema.sch_start_acts))
     &&
     (string_multiset_eq a.ShEx_Schema.sch_imports b.ShEx_Schema.sch_imports))
    &&
    (shape_decl_list_eq a.ShEx_Schema.sch_shapes b.ShEx_Schema.sch_shapes
       schema_eq_fuel)
