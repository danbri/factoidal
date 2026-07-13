open Prims
let escape_char (c : FStar_Char.char) : Prims.string=
  if c = 38
  then "&amp;"
  else
    if c = 60
    then "&lt;"
    else
      if c = 62
      then "&gt;"
      else
        if c = 34
        then "&quot;"
        else if c = 39 then "&apos;" else FStar_String.string_of_list [c]
let rec escape_chars (l : FStar_Char.char Prims.list) : Prims.string=
  match l with
  | [] -> ""
  | c::t -> FStar_String.concat "" [escape_char c; escape_chars t]
let escape_xml (s : Prims.string) : Prims.string=
  escape_chars (FStar_String.list_of_string s)
let render_int (n : Prims.int) : Prims.string=
  FStar_String.concat "" ["<mn>"; Prims.string_of_int n; "</mn>"]
let render_rat (n : Prims.int) (d : Prims.int) : Prims.string=
  FStar_String.concat ""
    ["<mfrac><mn>";
    Prims.string_of_int n;
    "</mn><mn>";
    Prims.string_of_int d;
    "</mn></mfrac>"]
let is_relation (fn : Prims.string) : Prims.bool=
  (((((fn = "eq") || (fn = "neq")) || (fn = "lt")) || (fn = "gt")) ||
     (fn = "leq"))
    || (fn = "geq")
let prec (e : Math_Expr.expr) : Prims.int=
  match e with
  | Math_Expr.E_Int n ->
      if n < Prims.int_zero then Prims.int_one else (Prims.of_int (4))
  | Math_Expr.E_Rat (n, uu___) ->
      if n < Prims.int_zero then Prims.int_one else (Prims.of_int (4))
  | Math_Expr.E_Bool uu___ -> (Prims.of_int (4))
  | Math_Expr.E_Sym uu___ -> (Prims.of_int (4))
  | Math_Expr.E_App (fn, args) ->
      if fn = "plus"
      then Prims.int_one
      else
        if fn = "minus"
        then
          (match args with
           | uu___1::[] -> (Prims.of_int (2))
           | uu___1 -> Prims.int_one)
        else
          if fn = "times"
          then (Prims.of_int (2))
          else
            if fn = "power"
            then (Prims.of_int (3))
            else
              if fn = "divide"
              then (Prims.of_int (4))
              else
                if is_relation fn then Prims.int_zero else (Prims.of_int (4))
let fence (s : Prims.string) : Prims.string=
  FStar_String.concat "" ["<mrow><mo>(</mo>"; s; "<mo>)</mo></mrow>"]
let relation_token (fn : Prims.string) : Prims.string=
  if fn = "eq"
  then "<mo>=</mo>"
  else
    if fn = "neq"
    then "<mo>&#x2260;</mo>"
    else
      if fn = "lt"
      then "<mo>&lt;</mo>"
      else
        if fn = "gt"
        then "<mo>&gt;</mo>"
        else if fn = "leq" then "<mo>&#x2264;</mo>" else "<mo>&#x2265;</mo>"
let rec expr_size (e : Math_Expr.expr) : Prims.nat=
  match e with
  | Math_Expr.E_App (uu___, args) -> Prims.int_one + (exprs_size args)
  | uu___ -> Prims.int_one
and exprs_size (es : Math_Expr.expr Prims.list) : Prims.nat=
  match es with
  | [] -> Prims.int_zero
  | h::t -> (expr_size h) + (exprs_size t)
let fenced (minp : Prims.int) (p : Prims.int) (s : Prims.string) :
  Prims.string= if p < minp then fence s else s
let rec pres (e : Math_Expr.expr) : Prims.string=
  match e with
  | Math_Expr.E_Int n -> render_int n
  | Math_Expr.E_Rat (n, d) -> render_rat n d
  | Math_Expr.E_Bool b ->
      FStar_String.concat "" ["<mi>"; if b then "true" else "false"; "</mi>"]
  | Math_Expr.E_Sym s ->
      FStar_String.concat "" ["<mi>"; escape_xml s; "</mi>"]
  | Math_Expr.E_App (fn, args) ->
      if fn = "plus"
      then
        (match args with
         | [] -> render_int Prims.int_zero
         | a::rest ->
             FStar_String.concat ""
               [fenced Prims.int_one (prec a) (pres a); pres_plus_rest rest])
      else
        if fn = "minus"
        then
          (match args with
           | a::[] ->
               FStar_String.concat ""
                 ["<mo>-</mo>"; fenced (Prims.of_int (2)) (prec a) (pres a)]
           | a::b::[] ->
               FStar_String.concat ""
                 [fenced Prims.int_one (prec a) (pres a);
                 "<mo>-</mo>";
                 fenced (Prims.of_int (2)) (prec b) (pres b)]
           | uu___1 -> pres_apply fn args)
        else
          if fn = "times"
          then
            (match args with
             | [] -> render_int Prims.int_one
             | a::rest ->
                 FStar_String.concat ""
                   [fenced (Prims.of_int (2)) (prec a) (pres a);
                   pres_times_rest rest])
          else
            if fn = "divide"
            then
              (match args with
               | a::b::[] ->
                   FStar_String.concat ""
                     ["<mfrac><mrow>";
                     pres a;
                     "</mrow><mrow>";
                     pres b;
                     "</mrow></mfrac>"]
               | uu___3 -> pres_apply fn args)
            else
              if fn = "power"
              then
                (match args with
                 | a::b::[] ->
                     FStar_String.concat ""
                       ["<msup><mrow>";
                       fenced (Prims.of_int (4)) (prec a) (pres a);
                       "</mrow><mrow>";
                       pres b;
                       "</mrow></msup>"]
                 | uu___4 -> pres_apply fn args)
              else
                if fn = "root"
                then
                  (match args with
                   | a::[] ->
                       FStar_String.concat ""
                         ["<msqrt><mrow>"; pres a; "</mrow></msqrt>"]
                   | d::a::[] ->
                       FStar_String.concat ""
                         ["<mroot><mrow>";
                         pres a;
                         "</mrow><mrow>";
                         pres d;
                         "</mrow></mroot>"]
                   | uu___5 -> pres_apply fn args)
                else
                  if is_relation fn
                  then
                    (match args with
                     | a::rest ->
                         FStar_String.concat ""
                           [fenced Prims.int_one (prec a) (pres a);
                           pres_rel_rest fn rest]
                     | [] -> pres_apply fn args)
                  else
                    if fn = "abs"
                    then
                      (match args with
                       | a::[] ->
                           FStar_String.concat ""
                             ["<mrow><mo>|</mo>";
                             pres a;
                             "<mo>|</mo></mrow>"]
                       | uu___7 -> pres_apply fn args)
                    else
                      if fn = "factorial"
                      then
                        (match args with
                         | a::[] ->
                             FStar_String.concat ""
                               [fenced (Prims.of_int (4)) (prec a) (pres a);
                               "<mo>!</mo>"]
                         | uu___8 -> pres_apply fn args)
                      else
                        if fn = "exp"
                        then
                          (match args with
                           | a::[] ->
                               FStar_String.concat ""
                                 ["<msup><mi>e</mi><mrow>";
                                 pres a;
                                 "</mrow></msup>"]
                           | uu___9 -> pres_apply fn args)
                        else
                          if fn = "diff_unsupported"
                          then
                            "<merror><mtext>unsupported derivative</mtext></merror>"
                          else pres_apply fn args
and pres_plus_rest (es : Math_Expr.expr Prims.list) : Prims.string=
  match es with
  | [] -> ""
  | a::rest ->
      FStar_String.concat ""
        ["<mo>+</mo>";
        fenced Prims.int_one (prec a) (pres a);
        pres_plus_rest rest]
and pres_times_rest (es : Math_Expr.expr Prims.list) : Prims.string=
  match es with
  | [] -> ""
  | a::rest ->
      FStar_String.concat ""
        ["<mo>&#x2062;</mo>";
        fenced (Prims.of_int (2)) (prec a) (pres a);
        pres_times_rest rest]
and pres_rel_rest (fn : Prims.string) (es : Math_Expr.expr Prims.list) :
  Prims.string=
  match es with
  | [] -> ""
  | a::rest ->
      FStar_String.concat ""
        [relation_token fn;
        fenced Prims.int_one (prec a) (pres a);
        pres_rel_rest fn rest]
and pres_apply (fn : Prims.string) (args : Math_Expr.expr Prims.list) :
  Prims.string=
  FStar_String.concat ""
    ["<mrow><mi>";
    escape_xml fn;
    "</mi><mo>&#x2061;</mo><mo>(</mo>";
    pres_apply_args args;
    "<mo>)</mo></mrow>"]
and pres_apply_args (es : Math_Expr.expr Prims.list) : Prims.string=
  match es with
  | [] -> ""
  | a::[] -> pres a
  | a::rest ->
      FStar_String.concat "" [pres a; "<mo>,</mo>"; pres_apply_args rest]
let to_presentation_mathml (e : Math_Expr.expr) : Prims.string=
  FStar_String.concat ""
    ["<math xmlns=\"http://www.w3.org/1998/Math/MathML\">";
    pres e;
    "</math>"]
let known_content_op (fn : Prims.string) : Prims.bool=
  (((((((((((((((((((fn = "plus") || (fn = "times")) || (fn = "minus")) ||
                    (fn = "divide"))
                   || (fn = "power"))
                  || (fn = "root"))
                 || (fn = "abs"))
                || (fn = "quotient"))
               || (fn = "rem"))
              || (fn = "factorial"))
             || (fn = "gcd"))
            || (fn = "max"))
           || (fn = "min"))
          || (fn = "eq"))
         || (fn = "neq"))
        || (fn = "lt"))
       || (fn = "gt"))
      || (fn = "leq"))
     || (fn = "geq"))
    || (fn = "exp")
let content_op (fn : Prims.string) : Prims.string=
  if known_content_op fn
  then FStar_String.concat "" ["<"; fn; "/>"]
  else FStar_String.concat "" ["<csymbol>"; escape_xml fn; "</csymbol>"]
let rec content (e : Math_Expr.expr) : Prims.string=
  match e with
  | Math_Expr.E_Int n ->
      FStar_String.concat ""
        ["<cn type=\"integer\">"; Prims.string_of_int n; "</cn>"]
  | Math_Expr.E_Rat (n, d) ->
      FStar_String.concat ""
        ["<cn type=\"rational\">";
        Prims.string_of_int n;
        "<sep/>";
        Prims.string_of_int d;
        "</cn>"]
  | Math_Expr.E_Bool b -> if b then "<true/>" else "<false/>"
  | Math_Expr.E_Sym s ->
      FStar_String.concat "" ["<ci>"; escape_xml s; "</ci>"]
  | Math_Expr.E_App (fn, args) ->
      FStar_String.concat ""
        ["<apply>"; content_op fn; content_args args; "</apply>"]
and content_args (es : Math_Expr.expr Prims.list) : Prims.string=
  match es with
  | [] -> ""
  | a::rest -> FStar_String.concat "" [content a; content_args rest]
let to_content_mathml (e : Math_Expr.expr) : Prims.string=
  FStar_String.concat ""
    ["<math xmlns=\"http://www.w3.org/1998/Math/MathML\">";
    content e;
    "</math>"]
