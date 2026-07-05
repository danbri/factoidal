open Prims
let rif_pred_ns : Prims.string=
  "http://www.w3.org/2007/rif-builtin-predicate#"
let rif_func_ns : Prims.string=
  "http://www.w3.org/2007/rif-builtin-function#"
let xsd_hexBinary : RDF_Graph_Executable.wf_iri=
  Prims.strcat RDF_Graph_Executable.xsd_ns_prefix "hexBinary"
let xsd_base64Binary : RDF_Graph_Executable.wf_iri=
  Prims.strcat RDF_Graph_Executable.xsd_ns_prefix "base64Binary"
let xsd_anyURI : RDF_Graph_Executable.wf_iri=
  Prims.strcat RDF_Graph_Executable.xsd_ns_prefix "anyURI"
let rdf_ns_prefix : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let rdf_XMLLiteral : RDF_Graph_Executable.wf_iri=
  Prims.strcat rdf_ns_prefix "XMLLiteral"
let is_hex_digit_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))) ||
     ((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (70)))))
    || ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (102))))
let is_hex_binary_lexical (lex : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string lex in
  (((mod) (FStar_List_Tot_Base.length cs) (Prims.of_int (2))) =
     Prims.int_zero)
    && (FStar_List_Tot_Base.for_all is_hex_digit_char cs)
let is_base64_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((((((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))) ||
        ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (122)))))
       || ((n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))))
      || (n = (Prims.of_int (43))))
     || (n = (Prims.of_int (47))))
    || (n = (Prims.of_int (61)))
let is_base64_binary_lexical (lex : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string lex in
  let len = FStar_List_Tot_Base.length cs in
  ((len > Prims.int_zero) &&
     (((mod) len (Prims.of_int (4))) = Prims.int_zero))
    && (FStar_List_Tot_Base.for_all is_base64_char cs)
let literal_ill_formed_ext (dt : RDF_Graph_Executable.wf_iri)
  (lex : Prims.string) : Prims.bool=
  if dt = xsd_hexBinary
  then Prims.op_Negation (is_hex_binary_lexical lex)
  else
    if dt = xsd_base64Binary
    then Prims.op_Negation (is_base64_binary_lexical lex)
    else XSD_Datatypes.literal_ill_formed dt lex
let unconstrained_lexical_space_datatypes :
  RDF_Graph_Executable.wf_iri Prims.list= [xsd_anyURI; rdf_XMLLiteral]
let is_literal_of_datatype (expected_dt : RDF_Graph_Executable.wf_iri)
  (t : RDF_Graph_Executable.rdf_term) : Prims.bool=
  match t with
  | RDF_Graph_Executable.T_Literal l ->
      if
        FStar_List_Tot_Base.mem expected_dt
          unconstrained_lexical_space_datatypes
      then l.RDF_Graph_Executable.datatype = expected_dt
      else
        Prims.op_Negation
          (literal_ill_formed_ext expected_dt
             l.RDF_Graph_Executable.lexical_form)
  | uu___ -> false
let is_literal_datatype_table :
  (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list=
  [("decimal", RDF_Graph_Executable.xsd_decimal);
  ("double", RDF_Graph_Executable.xsd_double);
  ("float", SPARQL11_Algebra.xsd_float);
  ("integer", RDF_Graph_Executable.xsd_integer);
  ("long", RDF_Graph_Executable.xsd_long);
  ("int", RDF_Graph_Executable.xsd_int);
  ("short", RDF_Graph_Executable.xsd_short);
  ("byte", RDF_Graph_Executable.xsd_byte);
  ("negativeInteger", RDF_Graph_Executable.xsd_negativeInteger);
  ("nonNegativeInteger", RDF_Graph_Executable.xsd_nonNegativeInteger);
  ("nonPositiveInteger", RDF_Graph_Executable.xsd_nonPositiveInteger);
  ("positiveInteger", RDF_Graph_Executable.xsd_positiveInteger);
  ("unsignedLong", RDF_Graph_Executable.xsd_unsignedLong);
  ("unsignedInt", RDF_Graph_Executable.xsd_unsignedInt);
  ("unsignedShort", RDF_Graph_Executable.xsd_unsignedShort);
  ("unsignedByte", RDF_Graph_Executable.xsd_unsignedByte);
  ("hexBinary", xsd_hexBinary);
  ("base64Binary", xsd_base64Binary);
  ("anyURI", xsd_anyURI);
  ("boolean", RDF_Graph_Executable.xsd_boolean);
  ("XMLLiteral", rdf_XMLLiteral)]
let rec lookup_datatype (name : Prims.string)
  (tbl : (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  match tbl with
  | [] -> FStar_Pervasives_Native.None
  | (n, dt)::rest ->
      if n = name
      then FStar_Pervasives_Native.Some dt
      else lookup_datatype name rest
let is_literal_pred_shape (local : Prims.string) :
  (RDF_Graph_Executable.wf_iri * Prims.bool) FStar_Pervasives_Native.option=
  if
    ((FStar_String.strlen local) > (FStar_String.strlen "is-literal-not-"))
      &&
      ((FStar_String.sub local Prims.int_zero
          (FStar_String.strlen "is-literal-not-"))
         = "is-literal-not-")
  then
    let ty =
      FStar_String.sub local (FStar_String.strlen "is-literal-not-")
        ((FStar_String.strlen local) -
           (FStar_String.strlen "is-literal-not-")) in
    match lookup_datatype ty is_literal_datatype_table with
    | FStar_Pervasives_Native.Some dt ->
        FStar_Pervasives_Native.Some (dt, true)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else
    if
      ((FStar_String.strlen local) > (FStar_String.strlen "is-literal-")) &&
        ((FStar_String.sub local Prims.int_zero
            (FStar_String.strlen "is-literal-"))
           = "is-literal-")
    then
      (let ty =
         FStar_String.sub local (FStar_String.strlen "is-literal-")
           ((FStar_String.strlen local) - (FStar_String.strlen "is-literal-")) in
       match lookup_datatype ty is_literal_datatype_table with
       | FStar_Pervasives_Native.Some dt ->
           FStar_Pervasives_Native.Some (dt, false)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    else FStar_Pervasives_Native.None
let term_to_arith_expr (t : RDF_Graph_Executable.rdf_term) :
  SPARQL11_Algebra.expr FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_Literal l ->
      if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_integer
      then
        (match SPARQL11_Algebra.parse_int_string
                 l.RDF_Graph_Executable.lexical_form
         with
         | FStar_Pervasives_Native.Some n ->
             FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_NumericLit n)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_decimal
        then
          FStar_Pervasives_Native.Some
            (SPARQL11_Algebra.E_DecimalLit
               (l.RDF_Graph_Executable.lexical_form))
        else
          if
            (l.RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.xsd_double)
              ||
              (l.RDF_Graph_Executable.datatype = SPARQL11_Algebra.xsd_float)
          then
            FStar_Pervasives_Native.Some
              (SPARQL11_Algebra.E_DoubleLit
                 (l.RDF_Graph_Executable.lexical_form))
          else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let eval_numeric_binop (op : SPARQL11_Algebra.arith_op)
  (a : RDF_Graph_Executable.rdf_term) (b : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match ((term_to_arith_expr a), (term_to_arith_expr b)) with
  | (FStar_Pervasives_Native.Some ea, FStar_Pervasives_Native.Some eb) ->
      let result =
        SPARQL11_Algebra.eval_expr_with_base FStar_Pervasives_Native.None
          (SPARQL11_Algebra.E_Arith (op, ea, eb)) SPARQL11_Algebra.sm_empty in
      SPARQL11_Algebra.er_to_term result
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let term_to_er (t : RDF_Graph_Executable.rdf_term) :
  SPARQL11_Algebra.eval_result=
  match t with
  | RDF_Graph_Executable.T_Literal l ->
      if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_integer
      then
        (match SPARQL11_Algebra.parse_int_string
                 l.RDF_Graph_Executable.lexical_form
         with
         | FStar_Pervasives_Native.Some n -> SPARQL11_Algebra.ER_Num n
         | FStar_Pervasives_Native.None -> SPARQL11_Algebra.ER_Term t)
      else
        if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_decimal
        then SPARQL11_Algebra.ER_Dec (l.RDF_Graph_Executable.lexical_form)
        else
          if
            (l.RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.xsd_double)
              ||
              (l.RDF_Graph_Executable.datatype = SPARQL11_Algebra.xsd_float)
          then SPARQL11_Algebra.ER_Dbl (l.RDF_Graph_Executable.lexical_form)
          else
            if
              l.RDF_Graph_Executable.datatype =
                RDF_Graph_Executable.xsd_boolean
            then
              SPARQL11_Algebra.ER_Bool
                ((l.RDF_Graph_Executable.lexical_form = "true") ||
                   (l.RDF_Graph_Executable.lexical_form = "1"))
            else SPARQL11_Algebra.ER_Term t
  | uu___ -> SPARQL11_Algebra.ER_Term t
let numeric_predicate (cmp : SPARQL11_Algebra.comp_op)
  (a : RDF_Graph_Executable.rdf_term) (b : RDF_Graph_Executable.rdf_term) :
  Prims.bool FStar_Pervasives_Native.option=
  SPARQL11_Algebra.value_compare (term_to_er a) (term_to_er b) cmp
let term_to_int (t : RDF_Graph_Executable.rdf_term) :
  Prims.int FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_Literal l ->
      if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_integer
      then
        SPARQL11_Algebra.parse_int_string l.RDF_Graph_Executable.lexical_form
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let trunc_div (a : Prims.int) (b : Prims.int) : Prims.int=
  if b = Prims.int_zero
  then Prims.int_zero
  else
    (let q = a / b in
     let r = a - (q * b) in
     if
       (r <> Prims.int_zero) &&
         ((a < Prims.int_zero) <> (b < Prims.int_zero))
     then q + Prims.int_one
     else q)
let trunc_mod (a : Prims.int) (b : Prims.int) : Prims.int=
  if b = Prims.int_zero then Prims.int_zero else a - ((trunc_div a b) * b)
let mk_int_literal (n : Prims.int) : RDF_Graph_Executable.rdf_term=
  RDF_Graph_Executable.T_Literal
    {
      RDF_Graph_Executable.lexical_form = (Prims.string_of_int n);
      RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_integer;
      RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
    }
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
let supported_cast_targets : RDF_Graph_Executable.wf_iri Prims.list=
  FStar_List_Tot_Base.map (fun p -> FStar_Pervasives_Native.snd p)
    is_literal_datatype_table
let xsd_constructor_cast (op : RDF_Graph_Executable.wf_iri)
  (args : RDF_Graph_Executable.rdf_term Prims.list) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match args with
  | (RDF_Graph_Executable.T_Literal l)::[] ->
      if
        (FStar_List_Tot_Base.mem op supported_cast_targets) &&
          (op <> RDF_Graph_Executable.rdf_lang_string)
      then
        FStar_Pervasives_Native.Some
          (RDF_Graph_Executable.T_Literal
             {
               RDF_Graph_Executable.lexical_form =
                 (l.RDF_Graph_Executable.lexical_form);
               RDF_Graph_Executable.datatype = op;
               RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
             })
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let eval_function (op : RDF_Graph_Executable.wf_iri)
  (args : RDF_Graph_Executable.rdf_term Prims.list) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if
    Prims.op_Negation
      (((FStar_String.strlen op) > (FStar_String.strlen rif_func_ns)) &&
         ((FStar_String.sub op Prims.int_zero
             (FStar_String.strlen rif_func_ns))
            = rif_func_ns))
  then xsd_constructor_cast op args
  else
    (let local = local_name_of_iri op in
     match (local, args) with
     | ("numeric-add", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Add a b
     | ("numeric-subtract", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Sub a b
     | ("numeric-multiply", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Mul a b
     | ("numeric-divide", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Div a b
     | ("numeric-integer-divide", a::b::[]) ->
         (match ((term_to_int a), (term_to_int b)) with
          | (FStar_Pervasives_Native.Some ia, FStar_Pervasives_Native.Some
             ib) ->
              if ib = Prims.int_zero
              then FStar_Pervasives_Native.None
              else
                FStar_Pervasives_Native.Some
                  (mk_int_literal (trunc_div ia ib))
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("numeric-integer-mod", a::b::[]) ->
         (match ((term_to_int a), (term_to_int b)) with
          | (FStar_Pervasives_Native.Some ia, FStar_Pervasives_Native.Some
             ib) ->
              if ib = Prims.int_zero
              then FStar_Pervasives_Native.None
              else
                FStar_Pervasives_Native.Some
                  (mk_int_literal (trunc_mod ia ib))
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
let eval_predicate (op : RDF_Graph_Executable.wf_iri)
  (args : RDF_Graph_Executable.rdf_term Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  if
    Prims.op_Negation
      (((FStar_String.strlen op) > (FStar_String.strlen rif_pred_ns)) &&
         ((FStar_String.sub op Prims.int_zero
             (FStar_String.strlen rif_pred_ns))
            = rif_pred_ns))
  then FStar_Pervasives_Native.None
  else
    (let local = local_name_of_iri op in
     match (local, args) with
     | ("numeric-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpEq a b
     | ("numeric-not-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpNe a b
     | ("numeric-less-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpLt a b
     | ("numeric-less-than-or-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpLe a b
     | ("numeric-greater-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpGt a b
     | ("numeric-greater-than-or-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpGe a b
     | ("boolean-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpEq a b
     | ("boolean-less-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpLt a b
     | ("boolean-greater-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpGt a b
     | ("literal-not-identical", a::b::[]) ->
         FStar_Pervasives_Native.Some
           (Prims.op_Negation (RDF_Graph_Executable.rdf_term_eq a b))
     | (uu___1, x::[]) ->
         (match is_literal_pred_shape local with
          | FStar_Pervasives_Native.Some (dt, negated) ->
              let v = is_literal_of_datatype dt x in
              FStar_Pervasives_Native.Some
                (if negated then Prims.op_Negation v else v)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
