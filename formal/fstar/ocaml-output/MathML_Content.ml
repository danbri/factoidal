open Prims
let local_name (tag : Prims.string) : Prims.string=
  let rec after_colon l acc =
    match l with
    | [] -> FStar_List_Tot_Base.rev acc
    | c::rest ->
        if c = 58 then after_colon rest [] else after_colon rest (c :: acc) in
  FStar_String.string_of_list
    (after_colon (FStar_String.list_of_string tag) [])
let is_element (n : Parser_XML.xml_node) : Prims.bool=
  Parser_XML.uu___is_XElement n
let rec element_children_only (nodes : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node Prims.list=
  match nodes with
  | [] -> []
  | n::rest ->
      if is_element n
      then n :: (element_children_only rest)
      else element_children_only rest
let first_element (nodes : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match element_children_only nodes with
  | e::uu___ -> FStar_Pervasives_Native.Some e
  | [] -> FStar_Pervasives_Native.None
let is_qualifier (n : Parser_XML.xml_node) : Prims.bool=
  match n with
  | Parser_XML.XElement (tag, uu___, uu___1) ->
      let ln = local_name tag in
      ((((((((ln = "degree") || (ln = "logbase")) || (ln = "bvar")) ||
             (ln = "lowlimit"))
            || (ln = "uplimit"))
           || (ln = "condition"))
          || (ln = "domainofapplication"))
         || (ln = "interval"))
        || (ln = "momentabout")
  | uu___ -> false
let rec drop_qualifiers (nodes : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node Prims.list=
  match nodes with
  | [] -> []
  | n::rest ->
      if is_qualifier n
      then drop_qualifiers rest
      else n :: (drop_qualifiers rest)
let rec find_local (name : Prims.string)
  (nodes : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match nodes with
  | [] -> FStar_Pervasives_Native.None
  | n::rest ->
      (match n with
       | Parser_XML.XElement (tag, uu___, uu___1) ->
           if (local_name tag) = name
           then FStar_Pervasives_Native.Some n
           else find_local name rest
       | uu___ -> find_local name rest)
let rec split_at_sep (children : Parser_XML.xml_node Prims.list)
  (before : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match children with
  | [] -> ((FStar_List_Tot_Base.rev before), FStar_Pervasives_Native.None)
  | n::rest ->
      (match n with
       | Parser_XML.XElement (tag, uu___, uu___1) ->
           if (local_name tag) = "sep"
           then
             ((FStar_List_Tot_Base.rev before),
               (FStar_Pervasives_Native.Some
                  (FStar_String.list_of_string
                     (Parser_XML.text_content
                        (Parser_XML.XElement ("wrap", [], rest))))))
           else split_at_sep rest before
       | Parser_XML.XText t ->
           split_at_sep rest
             (FStar_List_Tot_Base.op_At
                (FStar_List_Tot_Base.rev (FStar_String.list_of_string t))
                before)
       | uu___ -> split_at_sep rest before)
let eval_cn_value (attrs : Parser_XML.xml_attribute Prims.list)
  (children : Parser_XML.xml_node Prims.list) : Math_Expr.mvalue=
  let ty =
    match Parser_XML.find_attr "type" attrs with
    | FStar_Pervasives_Native.Some t -> t
    | FStar_Pervasives_Native.None -> "real" in
  if ty = "rational"
  then
    let uu___ = split_at_sep children [] in
    match uu___ with
    | (num_cs, den_opt) ->
        (match den_opt with
         | FStar_Pervasives_Native.None ->
             Math_Expr.parse_decimal (FStar_String.string_of_list num_cs)
         | FStar_Pervasives_Native.Some den_cs ->
             let nv =
               Math_Expr.parse_decimal (FStar_String.string_of_list num_cs) in
             let dv =
               Math_Expr.parse_decimal (FStar_String.string_of_list den_cs) in
             Math_Expr.m_div nv dv)
  else
    Math_Expr.parse_decimal
      (Parser_XML.text_content (Parser_XML.XElement ("wrap", [], children)))
let canonical_op (ln : Prims.string) : Prims.string=
  match ln with
  | "plus" -> "plus"
  | "times" -> "times"
  | "minus" -> "minus"
  | "divide" -> "divide"
  | "power" -> "power"
  | "root" -> "root"
  | "abs" -> "abs"
  | "quotient" -> "quotient"
  | "rem" -> "rem"
  | "factorial" -> "factorial"
  | "gcd" -> "gcd"
  | "max" -> "max"
  | "min" -> "min"
  | "eq" -> "eq"
  | "neq" -> "neq"
  | "lt" -> "lt"
  | "gt" -> "gt"
  | "leq" -> "leq"
  | "geq" -> "geq"
  | other -> other
let mathml_op_name (opnode : Parser_XML.xml_node) : Prims.string=
  match opnode with
  | Parser_XML.XElement (tag, uu___, uu___1) ->
      let ln = local_name tag in
      if ln = "csymbol"
      then canonical_op (Math_Expr.trim_str (Parser_XML.text_content opnode))
      else canonical_op ln
  | uu___ -> ""
let rec mathml_to_expr (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  Math_Expr.expr FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (tag, attrs, children) ->
         let ln = local_name tag in
         if ln = "cn"
         then
           FStar_Pervasives_Native.Some
             (Math_Expr.value_to_lit (eval_cn_value attrs children))
         else
           if ln = "ci"
           then
             FStar_Pervasives_Native.Some
               (Math_Expr.E_Sym
                  (Math_Expr.trim_str (Parser_XML.text_content n)))
           else
             if ln = "csymbol"
             then
               FStar_Pervasives_Native.Some
                 (Math_Expr.E_Sym
                    (Math_Expr.trim_str (Parser_XML.text_content n)))
             else
               if ln = "true"
               then FStar_Pervasives_Native.Some (Math_Expr.E_Bool true)
               else
                 if ln = "false"
                 then FStar_Pervasives_Native.Some (Math_Expr.E_Bool false)
                 else
                   if (ln = "math") || (ln = "cerror")
                   then
                     (match first_element children with
                      | FStar_Pervasives_Native.Some e ->
                          mathml_to_expr e (fuel - Prims.int_one)
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None)
                   else
                     if ln = "apply"
                     then
                       (match element_children_only children with
                        | [] -> FStar_Pervasives_Native.None
                        | opnode::rest ->
                            let op = mathml_op_name opnode in
                            let arg_nodes = drop_qualifiers rest in
                            (match mathml_to_expr_list arg_nodes
                                     (fuel - Prims.int_one)
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some arglist ->
                                 if op = "root"
                                 then
                                   (match find_local "degree" rest with
                                    | FStar_Pervasives_Native.Some d ->
                                        (match first_element
                                                 (Parser_XML.element_children
                                                    d)
                                         with
                                         | FStar_Pervasives_Native.Some de ->
                                             (match mathml_to_expr de
                                                      (fuel - Prims.int_one)
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  dexpr ->
                                                  FStar_Pervasives_Native.Some
                                                    (Math_Expr.E_App
                                                       ("root", (dexpr ::
                                                         arglist)))
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  FStar_Pervasives_Native.Some
                                                    (Math_Expr.E_App
                                                       ("root", arglist)))
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.Some
                                               (Math_Expr.E_App
                                                  ("root", arglist)))
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.Some
                                          (Math_Expr.E_App ("root", arglist)))
                                 else
                                   FStar_Pervasives_Native.Some
                                     (Math_Expr.E_App (op, arglist))))
                     else
                       FStar_Pervasives_Native.Some
                         (Math_Expr.E_App (ln, []))
     | uu___1 -> FStar_Pervasives_Native.None)
and mathml_to_expr_list (ns : Parser_XML.xml_node Prims.list)
  (fuel : Prims.nat) :
  Math_Expr.expr Prims.list FStar_Pervasives_Native.option=
  match ns with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match mathml_to_expr hd fuel with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some e ->
           (match mathml_to_expr_list tl fuel with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some es ->
                FStar_Pervasives_Native.Some (e :: es)))
let eval_doc (env : (Prims.string * Math_Expr.mvalue) Prims.list)
  (root : Parser_XML.xml_node) : Math_Expr.mvalue=
  let start =
    match root with
    | Parser_XML.XElement (tag, uu___, children) ->
        if (local_name tag) = "math"
        then
          (match first_element children with
           | FStar_Pervasives_Native.Some e -> e
           | FStar_Pervasives_Native.None -> root)
        else root
    | uu___ -> root in
  match mathml_to_expr start Math_Expr.eval_fuel with
  | FStar_Pervasives_Native.Some e ->
      Math_Expr.eval env e Math_Expr.eval_fuel
  | FStar_Pervasives_Native.None -> Math_Expr.MV_Undef "unmappable-mathml"
let eval_doc_env (pairs : (Prims.string * Prims.string) Prims.list)
  (root : Parser_XML.xml_node) : Math_Expr.mvalue=
  eval_doc (Math_Expr.mk_env pairs) root
let value_to_string (v : Math_Expr.mvalue) : Prims.string=
  Math_Expr.value_to_string v
let value_reason (v : Math_Expr.mvalue) : Prims.string=
  Math_Expr.value_reason v
let eval_scalar (env : (Prims.string * Math_Expr.mvalue) Prims.list)
  (n : Parser_XML.xml_node) : Math_Expr.mvalue=
  match mathml_to_expr n Math_Expr.eval_fuel with
  | FStar_Pervasives_Native.Some e ->
      Math_Expr.eval env e Math_Expr.eval_fuel
  | FStar_Pervasives_Native.None -> Math_Expr.MV_Undef "unmappable-mathml"
let rec eval_entries (env : (Prims.string * Math_Expr.mvalue) Prims.list)
  (nodes : Parser_XML.xml_node Prims.list) : Math_Expr.mvalue Prims.list=
  match nodes with
  | [] -> []
  | e::rest -> (eval_scalar env e) :: (eval_entries env rest)
let rec eval_matrix_rows (env : (Prims.string * Math_Expr.mvalue) Prims.list)
  (rows : Parser_XML.xml_node Prims.list) :
  Math_Expr.mvalue Prims.list Prims.list=
  match rows with
  | [] -> []
  | r::rest ->
      let cells =
        match r with
        | Parser_XML.XElement (uu___, uu___1, children) ->
            eval_entries env (element_children_only children)
        | uu___ -> [] in
      cells :: (eval_matrix_rows env rest)
let mres_int (x : Math_Matrix.mres) :
  Prims.int FStar_Pervasives_Native.option=
  match x with
  | Math_Matrix.R_Scalar v -> Math_Expr.as_int v
  | uu___ -> FStar_Pervasives_Native.None
let rec fold_mres
  (f : Math_Matrix.mres -> Math_Matrix.mres -> Math_Matrix.mres)
  (acc : Math_Matrix.mres) (xs : Math_Matrix.mres Prims.list) :
  Math_Matrix.mres=
  match xs with | [] -> acc | h::t -> fold_mres f (f acc h) t
let neg_mres (x : Math_Matrix.mres) : Math_Matrix.mres=
  Math_Matrix.dyn_times
    (Math_Matrix.R_Scalar
       (Math_Expr.MV_Rat ((Prims.of_int (-1)), Prims.int_one))) x
let rec eval_mres (env : (Prims.string * Math_Expr.mvalue) Prims.list)
  (n : Parser_XML.xml_node) (fuel : Prims.nat) : Math_Matrix.mres=
  if fuel = Prims.int_zero
  then Math_Matrix.R_Undef "fuel-exhausted"
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         let ln = local_name tag in
         if (ln = "math") || (ln = "cerror")
         then
           (match first_element children with
            | FStar_Pervasives_Native.Some e ->
                eval_mres env e (fuel - Prims.int_one)
            | FStar_Pervasives_Native.None ->
                Math_Matrix.R_Undef "empty-document")
         else
           if ln = "matrix"
           then
             Math_Matrix.mk_matrix_res
               (eval_matrix_rows env (element_children_only children))
           else
             if ln = "vector"
             then
               Math_Matrix.mk_vector_res
                 (eval_entries env (element_children_only children))
             else
               if ln = "apply"
               then
                 (match element_children_only children with
                  | [] -> Math_Matrix.R_Undef "empty-apply"
                  | opnode::rest ->
                      let op = mathml_op_name opnode in
                      let args = drop_qualifiers rest in
                      let vals =
                        eval_mres_list env args (fuel - Prims.int_one) in
                      if op = "determinant"
                      then
                        (match vals with
                         | a::[] -> Math_Matrix.dyn_determinant a
                         | uu___5 -> Math_Matrix.R_Undef "determinant-arity")
                      else
                        if op = "transpose"
                        then
                          (match vals with
                           | a::[] -> Math_Matrix.dyn_transpose a
                           | uu___6 -> Math_Matrix.R_Undef "transpose-arity")
                        else
                          if op = "trace"
                          then
                            (match vals with
                             | a::[] -> Math_Matrix.dyn_trace a
                             | uu___7 -> Math_Matrix.R_Undef "trace-arity")
                          else
                            if op = "scalarproduct"
                            then
                              (match vals with
                               | a::b::[] ->
                                   Math_Matrix.dyn_scalarproduct a b
                               | uu___8 ->
                                   Math_Matrix.R_Undef "scalarproduct-arity")
                            else
                              if op = "vectorproduct"
                              then
                                (match vals with
                                 | a::b::[] ->
                                     Math_Matrix.dyn_vectorproduct a b
                                 | uu___9 ->
                                     Math_Matrix.R_Undef
                                       "vectorproduct-arity")
                              else
                                if op = "outerproduct"
                                then
                                  (match vals with
                                   | a::b::[] ->
                                       Math_Matrix.dyn_outerproduct a b
                                   | uu___10 ->
                                       Math_Matrix.R_Undef
                                         "outerproduct-arity")
                                else
                                  if op = "selector"
                                  then
                                    (match vals with
                                     | a::i::[] ->
                                         (match mres_int i with
                                          | FStar_Pervasives_Native.Some iv
                                              ->
                                              Math_Matrix.dyn_selector_matrix
                                                a iv Prims.int_one
                                          | FStar_Pervasives_Native.None ->
                                              Math_Matrix.R_Undef
                                                "selector-index-not-integer")
                                     | a::i::j::[] ->
                                         (match ((mres_int i), (mres_int j))
                                          with
                                          | (FStar_Pervasives_Native.Some iv,
                                             FStar_Pervasives_Native.Some jv)
                                              ->
                                              Math_Matrix.dyn_selector_matrix
                                                a iv jv
                                          | uu___11 ->
                                              Math_Matrix.R_Undef
                                                "selector-index-not-integer")
                                     | uu___11 ->
                                         Math_Matrix.R_Undef "selector-arity")
                                  else
                                    if op = "plus"
                                    then
                                      (match vals with
                                       | [] ->
                                           Math_Matrix.R_Scalar
                                             (Math_Expr.MV_Rat
                                                (Prims.int_zero,
                                                  Prims.int_one))
                                       | h::t ->
                                           fold_mres Math_Matrix.dyn_add h t)
                                    else
                                      if op = "times"
                                      then
                                        (match vals with
                                         | [] ->
                                             Math_Matrix.R_Scalar
                                               (Math_Expr.MV_Rat
                                                  (Prims.int_one,
                                                    Prims.int_one))
                                         | h::t ->
                                             fold_mres Math_Matrix.dyn_times
                                               h t)
                                      else
                                        if op = "minus"
                                        then
                                          (match vals with
                                           | a::[] -> neg_mres a
                                           | a::b::[] ->
                                               Math_Matrix.dyn_sub a b
                                           | uu___14 ->
                                               Math_Matrix.R_Undef
                                                 "minus-arity")
                                        else
                                          Math_Matrix.R_Scalar
                                            (eval_scalar env n))
               else Math_Matrix.R_Scalar (eval_scalar env n)
     | uu___1 -> Math_Matrix.R_Undef "non-element")
and eval_mres_list (env : (Prims.string * Math_Expr.mvalue) Prims.list)
  (ns : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) :
  Math_Matrix.mres Prims.list=
  match ns with
  | [] -> []
  | hd::tl -> (eval_mres env hd fuel) :: (eval_mres_list env tl fuel)
let eval_doc_mres (env : (Prims.string * Math_Expr.mvalue) Prims.list)
  (root : Parser_XML.xml_node) : Math_Matrix.mres=
  let start =
    match root with
    | Parser_XML.XElement (tag, uu___, children) ->
        if (local_name tag) = "math"
        then
          (match first_element children with
           | FStar_Pervasives_Native.Some e -> e
           | FStar_Pervasives_Native.None -> root)
        else root
    | uu___ -> root in
  eval_mres env start Math_Expr.eval_fuel
let eval_doc_env_string (pairs : (Prims.string * Prims.string) Prims.list)
  (root : Parser_XML.xml_node) : Prims.string=
  Math_Matrix.mres_to_string (eval_doc_mres (Math_Expr.mk_env pairs) root)
let eval_doc_env_reason (pairs : (Prims.string * Prims.string) Prims.list)
  (root : Parser_XML.xml_node) : Prims.string=
  Math_Matrix.mres_reason (eval_doc_mres (Math_Expr.mk_env pairs) root)
type mathml_kind =
  | MK_Content 
  | MK_Presentation 
  | MK_Unknown 
let uu___is_MK_Content (projectee : mathml_kind) : Prims.bool=
  match projectee with | MK_Content -> true | uu___ -> false
let uu___is_MK_Presentation (projectee : mathml_kind) : Prims.bool=
  match projectee with | MK_Presentation -> true | uu___ -> false
let uu___is_MK_Unknown (projectee : mathml_kind) : Prims.bool=
  match projectee with | MK_Unknown -> true | uu___ -> false
let content_vocab (ln : Prims.string) : Prims.bool=
  (((((((((ln = "apply") || (ln = "cn")) || (ln = "ci")) || (ln = "csymbol"))
         || (ln = "bind"))
        || (ln = "bvar"))
       || (ln = "cbytes"))
      || (ln = "cs"))
     || (ln = "cerror"))
    || (ln = "share")
let presentation_vocab (ln : Prims.string) : Prims.bool=
  ((((((((((((((((((((ln = "mi") || (ln = "mo")) || (ln = "mn")) ||
                     (ln = "mrow"))
                    || (ln = "mfrac"))
                   || (ln = "msqrt"))
                  || (ln = "mroot"))
                 || (ln = "msup"))
                || (ln = "msub"))
               || (ln = "msubsup"))
              || (ln = "mtable"))
             || (ln = "mtr"))
            || (ln = "mtd"))
           || (ln = "mtext"))
          || (ln = "mspace"))
         || (ln = "mover"))
        || (ln = "munder"))
       || (ln = "munderover"))
      || (ln = "mfenced"))
     || (ln = "mpadded"))
    || (ln = "mstyle")
let rec tree_has (pred : Prims.string -> Prims.bool)
  (n : Parser_XML.xml_node) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if pred (local_name tag)
         then true
         else tree_has_list pred children (fuel - Prims.int_one)
     | uu___1 -> false)
and tree_has_list (pred : Prims.string -> Prims.bool)
  (ns : Parser_XML.xml_node Prims.list) (fuel : Prims.nat) : Prims.bool=
  match ns with
  | [] -> false
  | hd::tl ->
      if tree_has pred hd fuel then true else tree_has_list pred tl fuel
let mathml_kind_of (root : Parser_XML.xml_node) : mathml_kind=
  if tree_has content_vocab root Math_Expr.eval_fuel
  then MK_Content
  else
    if tree_has presentation_vocab root Math_Expr.eval_fuel
    then MK_Presentation
    else MK_Unknown
