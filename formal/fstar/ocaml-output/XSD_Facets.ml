open Prims
let is_integer_family_datatype (dt : RDF_Term.wf_iri) : Prims.bool=
  ((((((((((((dt = RDF_Term.xsd_integer) || (dt = OWL_Closure.xsd_long)) ||
              (dt = OWL_Closure.xsd_int))
             || (dt = OWL_Closure.xsd_short))
            || (dt = OWL_Closure.xsd_byte))
           || (dt = OWL_Closure.xsd_unsignedLong))
          || (dt = OWL_Closure.xsd_unsignedInt))
         || (dt = OWL_Closure.xsd_unsignedShort))
        || (dt = OWL_Closure.xsd_unsignedByte))
       || (dt = OWL_Closure.xsd_nonNegativeInteger))
      || (dt = OWL_Closure.xsd_positiveInteger))
     || (dt = OWL_Closure.xsd_nonPositiveInteger))
    || (dt = OWL_Closure.xsd_negativeInteger)
type xsd_family =
  | Fam_Numeric 
  | Fam_String 
  | Fam_Boolean 
let uu___is_Fam_Numeric (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_Numeric -> true | uu___ -> false
let uu___is_Fam_String (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_String -> true | uu___ -> false
let uu___is_Fam_Boolean (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_Boolean -> true | uu___ -> false
let xsd_family_eq (a : xsd_family) (b : xsd_family) : Prims.bool=
  match (a, b) with
  | (Fam_Numeric, Fam_Numeric) -> true
  | (Fam_String, Fam_String) -> true
  | (Fam_Boolean, Fam_Boolean) -> true
  | (uu___, uu___1) -> false
let classify_family (dt : RDF_Term.wf_iri) :
  xsd_family FStar_Pervasives_Native.option=
  if (is_integer_family_datatype dt) || (dt = RDF_Term.xsd_decimal)
  then FStar_Pervasives_Native.Some Fam_Numeric
  else
    if dt = RDF_Term.xsd_string
    then FStar_Pervasives_Native.Some Fam_String
    else
      if dt = RDF_Term.xsd_boolean
      then FStar_Pervasives_Native.Some Fam_Boolean
      else FStar_Pervasives_Native.None
let is_ascii_digit (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let digit_val (c : FStar_Char.char) : Prims.int=
  (FStar_Char.int_of_char c) - (Prims.of_int (48))
let rec digits_to_int (chars : FStar_Char.char Prims.list) (acc : Prims.int)
  : Prims.int FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::tl ->
      if is_ascii_digit c
      then digits_to_int tl ((acc * (Prims.of_int (10))) + (digit_val c))
      else FStar_Pervasives_Native.None
let parse_facet_int (lex : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let chars = FStar_String.list_of_string lex in
  match chars with
  | [] -> FStar_Pervasives_Native.None
  | c::tl ->
      let code = FStar_Char.int_of_char c in
      if code = (Prims.of_int (45))
      then
        (match tl with
         | [] -> FStar_Pervasives_Native.None
         | uu___ ->
             (match digits_to_int tl Prims.int_zero with
              | FStar_Pervasives_Native.Some v ->
                  FStar_Pervasives_Native.Some (Prims.int_zero - v)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
      else
        if code = (Prims.of_int (43))
        then
          (match tl with
           | [] -> FStar_Pervasives_Native.None
           | uu___1 -> digits_to_int tl Prims.int_zero)
        else digits_to_int chars Prims.int_zero
let literal_int_value (l : RDF_Term.literal) :
  Prims.int FStar_Pervasives_Native.option=
  if is_integer_family_datatype l.RDF_Term.datatype
  then parse_facet_int l.RDF_Term.lexical_form
  else FStar_Pervasives_Native.None
type bound =
  | B_Unbounded 
  | B_Incl of Prims.int 
  | B_Excl of Prims.int 
let uu___is_B_Unbounded (projectee : bound) : Prims.bool=
  match projectee with | B_Unbounded -> true | uu___ -> false
let uu___is_B_Incl (projectee : bound) : Prims.bool=
  match projectee with | B_Incl _0 -> true | uu___ -> false
let __proj__B_Incl__item___0 (projectee : bound) : Prims.int=
  match projectee with | B_Incl _0 -> _0
let uu___is_B_Excl (projectee : bound) : Prims.bool=
  match projectee with | B_Excl _0 -> true | uu___ -> false
let __proj__B_Excl__item___0 (projectee : bound) : Prims.int=
  match projectee with | B_Excl _0 -> _0
type interval = {
  iv_lo: bound ;
  iv_hi: bound }
let __proj__Mkinterval__item__iv_lo (projectee : interval) : bound=
  match projectee with | { iv_lo; iv_hi;_} -> iv_lo
let __proj__Mkinterval__item__iv_hi (projectee : interval) : bound=
  match projectee with | { iv_lo; iv_hi;_} -> iv_hi
let full_interval : interval= { iv_lo = B_Unbounded; iv_hi = B_Unbounded }
let interval_empty (iv : interval) : Prims.bool=
  match ((iv.iv_lo), (iv.iv_hi)) with
  | (B_Incl lo, B_Incl hi) -> lo > hi
  | (B_Incl lo, B_Excl hi) -> lo >= hi
  | (B_Excl lo, B_Incl hi) -> lo >= hi
  | (B_Excl lo, B_Excl hi) -> lo >= (hi - Prims.int_one)
  | (uu___, uu___1) -> false
let tighter_lo (a : bound) (b : bound) : bound=
  match (a, b) with
  | (B_Unbounded, uu___) -> b
  | (uu___, B_Unbounded) -> a
  | (B_Incl x, B_Incl y) -> if x >= y then a else b
  | (B_Excl x, B_Excl y) -> if x >= y then a else b
  | (B_Incl x, B_Excl y) -> if x > y then a else b
  | (B_Excl x, B_Incl y) -> if x >= y then a else b
let tighter_hi (a : bound) (b : bound) : bound=
  match (a, b) with
  | (B_Unbounded, uu___) -> b
  | (uu___, B_Unbounded) -> a
  | (B_Incl x, B_Incl y) -> if x <= y then a else b
  | (B_Excl x, B_Excl y) -> if x <= y then a else b
  | (B_Incl x, B_Excl y) -> if x < y then a else b
  | (B_Excl x, B_Incl y) -> if x <= y then a else b
let interval_intersect (a : interval) (b : interval) : interval=
  {
    iv_lo = (tighter_lo a.iv_lo b.iv_lo);
    iv_hi = (tighter_hi a.iv_hi b.iv_hi)
  }
let value_in_interval (v : Prims.int) (iv : interval) : Prims.bool=
  (match iv.iv_lo with
   | B_Unbounded -> true
   | B_Incl lo -> v >= lo
   | B_Excl lo -> v > lo) &&
    (match iv.iv_hi with
     | B_Unbounded -> true
     | B_Incl hi -> v <= hi
     | B_Excl hi -> v < hi)
let base_interval_for (dt : RDF_Term.wf_iri) : interval=
  if dt = OWL_Closure.xsd_byte
  then
    {
      iv_lo = (B_Incl (Prims.of_int (-128)));
      iv_hi = (B_Incl (Prims.of_int (127)))
    }
  else
    if dt = OWL_Closure.xsd_unsignedByte
    then
      {
        iv_lo = (B_Incl Prims.int_zero);
        iv_hi = (B_Incl (Prims.of_int (255)))
      }
    else
      if dt = OWL_Closure.xsd_short
      then
        {
          iv_lo = (B_Incl (Prims.of_int (-32768)));
          iv_hi = (B_Incl (Prims.of_int (32767)))
        }
      else
        if dt = OWL_Closure.xsd_unsignedShort
        then
          {
            iv_lo = (B_Incl Prims.int_zero);
            iv_hi = (B_Incl (Prims.parse_int "65535"))
          }
        else
          if dt = OWL_Closure.xsd_int
          then
            {
              iv_lo = (B_Incl (Prims.parse_int "-2147483648"));
              iv_hi = (B_Incl (Prims.parse_int "2147483647"))
            }
          else
            if dt = OWL_Closure.xsd_unsignedInt
            then
              {
                iv_lo = (B_Incl Prims.int_zero);
                iv_hi = (B_Incl (Prims.parse_int "4294967295"))
              }
            else
              if dt = OWL_Closure.xsd_nonNegativeInteger
              then { iv_lo = (B_Incl Prims.int_zero); iv_hi = B_Unbounded }
              else
                if dt = OWL_Closure.xsd_positiveInteger
                then { iv_lo = (B_Incl Prims.int_one); iv_hi = B_Unbounded }
                else
                  if dt = OWL_Closure.xsd_nonPositiveInteger
                  then
                    { iv_lo = B_Unbounded; iv_hi = (B_Incl Prims.int_zero) }
                  else
                    if dt = OWL_Closure.xsd_negativeInteger
                    then
                      {
                        iv_lo = B_Unbounded;
                        iv_hi = (B_Incl (Prims.of_int (-1)))
                      }
                    else full_interval
let facet_min_incl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#minInclusive"
let facet_max_incl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#maxInclusive"
let facet_min_excl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#minExclusive"
let facet_max_excl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#maxExclusive"
let rec facets_to_interval (base_dt : RDF_Term.wf_iri)
  (facets : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list)
  (acc : interval) : interval=
  match facets with
  | [] -> acc
  | (firi, fval)::tl ->
      let acc' =
        if Prims.op_Negation (is_integer_family_datatype base_dt)
        then acc
        else
          (match fval with
           | RDF_Term.T_Literal l ->
               (match parse_facet_int l.RDF_Term.lexical_form with
                | FStar_Pervasives_Native.None -> acc
                | FStar_Pervasives_Native.Some v ->
                    if firi = facet_min_incl_iri
                    then
                      interval_intersect acc
                        { iv_lo = (B_Incl v); iv_hi = B_Unbounded }
                    else
                      if firi = facet_max_incl_iri
                      then
                        interval_intersect acc
                          { iv_lo = B_Unbounded; iv_hi = (B_Incl v) }
                      else
                        if firi = facet_min_excl_iri
                        then
                          interval_intersect acc
                            { iv_lo = (B_Excl v); iv_hi = B_Unbounded }
                        else
                          if firi = facet_max_excl_iri
                          then
                            interval_intersect acc
                              { iv_lo = B_Unbounded; iv_hi = (B_Excl v) }
                          else acc)
           | uu___1 -> acc) in
      facets_to_interval base_dt tl acc'
type value_set =
  | VS_Unconstrained 
  | VS_Interval of interval 
  | VS_Enum of RDF_Term.rdf_term Prims.list 
  | VS_Family of xsd_family 
  | VS_Empty 
let uu___is_VS_Unconstrained (projectee : value_set) : Prims.bool=
  match projectee with | VS_Unconstrained -> true | uu___ -> false
let uu___is_VS_Interval (projectee : value_set) : Prims.bool=
  match projectee with | VS_Interval _0 -> true | uu___ -> false
let __proj__VS_Interval__item___0 (projectee : value_set) : interval=
  match projectee with | VS_Interval _0 -> _0
let uu___is_VS_Enum (projectee : value_set) : Prims.bool=
  match projectee with | VS_Enum _0 -> true | uu___ -> false
let __proj__VS_Enum__item___0 (projectee : value_set) :
  RDF_Term.rdf_term Prims.list= match projectee with | VS_Enum _0 -> _0
let uu___is_VS_Family (projectee : value_set) : Prims.bool=
  match projectee with | VS_Family _0 -> true | uu___ -> false
let __proj__VS_Family__item___0 (projectee : value_set) : xsd_family=
  match projectee with | VS_Family _0 -> _0
let uu___is_VS_Empty (projectee : value_set) : Prims.bool=
  match projectee with | VS_Empty -> true | uu___ -> false
let term_int_opt (t : RDF_Term.rdf_term) :
  Prims.int FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l -> literal_int_value l
  | uu___ -> FStar_Pervasives_Native.None
let term_family (t : RDF_Term.rdf_term) :
  xsd_family FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l -> classify_family l.RDF_Term.datatype
  | uu___ -> FStar_Pervasives_Native.None
let term_bool_opt (t : RDF_Term.rdf_term) :
  Prims.bool FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if l.RDF_Term.datatype = RDF_Term.xsd_boolean
      then
        (if
           (l.RDF_Term.lexical_form = "true") ||
             (l.RDF_Term.lexical_form = "1")
         then FStar_Pervasives_Native.Some true
         else
           if
             (l.RDF_Term.lexical_form = "false") ||
               (l.RDF_Term.lexical_form = "0")
           then FStar_Pervasives_Native.Some false
           else FStar_Pervasives_Native.None)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let term_provably_equal (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  (RDF_Term.rdf_term_eq a b) ||
    (match ((term_int_opt a), (term_int_opt b)) with
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         x = y
     | (uu___, uu___1) ->
         (match ((term_bool_opt a), (term_bool_opt b)) with
          | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y)
              -> x = y
          | (uu___2, uu___3) -> false))
let both_string (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) : Prims.bool=
  match (a, b) with
  | (RDF_Term.T_Literal la, RDF_Term.T_Literal lb) ->
      (la.RDF_Term.datatype = RDF_Term.xsd_string) &&
        (lb.RDF_Term.datatype = RDF_Term.xsd_string)
  | (uu___, uu___1) -> false
let string_lex_neq (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  match (a, b) with
  | (RDF_Term.T_Literal la, RDF_Term.T_Literal lb) ->
      la.RDF_Term.lexical_form <> lb.RDF_Term.lexical_form
  | (uu___, uu___1) -> false
let term_provably_distinct (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  (((match ((term_int_opt a), (term_int_opt b)) with
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         x <> y
     | (uu___, uu___1) -> false) ||
      (match ((term_family a), (term_family b)) with
       | (FStar_Pervasives_Native.Some fa, FStar_Pervasives_Native.Some fb)
           -> Prims.op_Negation (xsd_family_eq fa fb)
       | (uu___, uu___1) -> false))
     || ((both_string a b) && (string_lex_neq a b)))
    ||
    (match ((term_bool_opt a), (term_bool_opt b)) with
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         x <> y
     | (uu___, uu___1) -> false)
let rec all_literal_terms (ts : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match ts with
  | [] -> true
  | (RDF_Term.T_Literal uu___)::tl -> all_literal_terms tl
  | uu___ -> false
let rec filter_enum_by (f : RDF_Term.rdf_term -> Prims.bool)
  (xs : RDF_Term.rdf_term Prims.list) : RDF_Term.rdf_term Prims.list=
  match xs with
  | [] -> []
  | h::tl -> if f h then h :: (filter_enum_by f tl) else filter_enum_by f tl
let rec enum_intersect (xs : RDF_Term.rdf_term Prims.list)
  (ys : RDF_Term.rdf_term Prims.list) : RDF_Term.rdf_term Prims.list=
  match xs with
  | [] -> []
  | h::tl ->
      if FStar_List_Tot_Base.for_all (term_provably_distinct h) ys
      then enum_intersect tl ys
      else h :: (enum_intersect tl ys)
let provably_outside_interval (iv : interval) (t : RDF_Term.rdf_term) :
  Prims.bool=
  (match term_int_opt t with
   | FStar_Pervasives_Native.Some v ->
       Prims.op_Negation (value_in_interval v iv)
   | FStar_Pervasives_Native.None -> false) ||
    (match term_family t with
     | FStar_Pervasives_Native.Some f ->
         Prims.op_Negation (xsd_family_eq f Fam_Numeric)
     | FStar_Pervasives_Native.None -> false)
let provably_outside_family (f : xsd_family) (t : RDF_Term.rdf_term) :
  Prims.bool=
  match term_family t with
  | FStar_Pervasives_Native.Some g -> Prims.op_Negation (xsd_family_eq f g)
  | FStar_Pervasives_Native.None -> false
let value_set_intersect (a : value_set) (b : value_set) : value_set=
  match (a, b) with
  | (VS_Empty, uu___) -> VS_Empty
  | (uu___, VS_Empty) -> VS_Empty
  | (VS_Unconstrained, x) -> x
  | (x, VS_Unconstrained) -> x
  | (VS_Interval ia, VS_Interval ib) ->
      let ii = interval_intersect ia ib in
      if interval_empty ii then VS_Empty else VS_Interval ii
  | (VS_Enum xs, VS_Enum ys) ->
      let e = enum_intersect xs ys in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Enum xs, VS_Interval iv) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_interval iv t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Interval iv, VS_Enum xs) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_interval iv t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Enum xs, VS_Family f) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_family f t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Family f, VS_Enum xs) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_family f t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Interval iv, VS_Family f) ->
      if xsd_family_eq f Fam_Numeric then VS_Interval iv else VS_Empty
  | (VS_Family f, VS_Interval iv) ->
      if xsd_family_eq f Fam_Numeric then VS_Interval iv else VS_Empty
  | (VS_Family fa, VS_Family fb) ->
      if xsd_family_eq fa fb then VS_Family fa else VS_Empty
let value_set_is_empty (v : value_set) : Prims.bool=
  match v with | VS_Empty -> true | VS_Enum [] -> true | uu___ -> false
let value_set_subtract (acc : value_set) (remove : value_set) : value_set=
  match (acc, remove) with
  | (VS_Enum xs, VS_Enum ys) ->
      let e =
        filter_enum_by
          (fun t ->
             Prims.op_Negation
               (FStar_List_Tot_Base.existsb (term_provably_equal t) ys)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (uu___, uu___1) -> acc
