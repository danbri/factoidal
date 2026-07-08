open Prims
type xpath_number =
  | XN_NaN 
  | XN_PosInf 
  | XN_NegInf 
  | XN_Finite of Prims.int * Prims.nat 
let uu___is_XN_NaN (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_NaN -> true | uu___ -> false
let uu___is_XN_PosInf (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_PosInf -> true | uu___ -> false
let uu___is_XN_NegInf (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_NegInf -> true | uu___ -> false
let uu___is_XN_Finite (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_Finite (mantissa, scale) -> true | uu___ -> false
let __proj__XN_Finite__item__mantissa (projectee : xpath_number) : Prims.int=
  match projectee with | XN_Finite (mantissa, scale) -> mantissa
let __proj__XN_Finite__item__scale (projectee : xpath_number) : Prims.nat=
  match projectee with | XN_Finite (mantissa, scale) -> scale
let rec xn_pow10 (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (xn_pow10 (n - Prims.int_one))
let xn_abs (n : Prims.int) : Prims.int=
  if n >= Prims.int_zero then n else Prims.int_zero - n
let xn_align (v1 : Prims.int) (s1 : Prims.nat) (v2 : Prims.int)
  (s2 : Prims.nat) : (Prims.int * Prims.int * Prims.nat)=
  if s1 >= s2
  then (v1, (v2 * (xn_pow10 (s1 - s2))), s1)
  else ((v1 * (xn_pow10 (s2 - s1))), v2, s2)
let xn_neg (n : xpath_number) : xpath_number=
  match n with
  | XN_NaN -> XN_NaN
  | XN_PosInf -> XN_NegInf
  | XN_NegInf -> XN_PosInf
  | XN_Finite (v, s) -> XN_Finite ((Prims.int_zero - v), s)
let xn_compare (a : xpath_number) (b : xpath_number) :
  Prims.int FStar_Pervasives_Native.option=
  match (a, b) with
  | (XN_NaN, uu___) -> FStar_Pervasives_Native.None
  | (uu___, XN_NaN) -> FStar_Pervasives_Native.None
  | (XN_PosInf, XN_PosInf) -> FStar_Pervasives_Native.Some Prims.int_zero
  | (XN_NegInf, XN_NegInf) -> FStar_Pervasives_Native.Some Prims.int_zero
  | (XN_PosInf, XN_NegInf) -> FStar_Pervasives_Native.Some Prims.int_one
  | (XN_NegInf, XN_PosInf) ->
      FStar_Pervasives_Native.Some (Prims.of_int (-1))
  | (XN_PosInf, XN_Finite (uu___, uu___1)) ->
      FStar_Pervasives_Native.Some Prims.int_one
  | (XN_Finite (uu___, uu___1), XN_PosInf) ->
      FStar_Pervasives_Native.Some (Prims.of_int (-1))
  | (XN_NegInf, XN_Finite (uu___, uu___1)) ->
      FStar_Pervasives_Native.Some (Prims.of_int (-1))
  | (XN_Finite (uu___, uu___1), XN_NegInf) ->
      FStar_Pervasives_Native.Some Prims.int_one
  | (XN_Finite (v1, s1), XN_Finite (v2, s2)) ->
      let uu___ = xn_align v1 s1 v2 s2 in
      (match uu___ with
       | (n1, n2, uu___1) ->
           FStar_Pervasives_Native.Some
             (if n1 < n2
              then (Prims.of_int (-1))
              else if n1 > n2 then Prims.int_one else Prims.int_zero))
let xn_arith (op : Parser_XPath.xp_arith_op) (a : xpath_number)
  (b : xpath_number) : xpath_number=
  match (a, b) with
  | (XN_NaN, uu___) -> XN_NaN
  | (uu___, XN_NaN) -> XN_NaN
  | (XN_PosInf, XN_PosInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_PosInf
       | Parser_XPath.Ar_Sub -> XN_NaN
       | Parser_XPath.Ar_Mul -> XN_PosInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_NegInf, XN_NegInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NegInf
       | Parser_XPath.Ar_Sub -> XN_NaN
       | Parser_XPath.Ar_Mul -> XN_PosInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_PosInf, XN_NegInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NaN
       | Parser_XPath.Ar_Sub -> XN_PosInf
       | Parser_XPath.Ar_Mul -> XN_NegInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_NegInf, XN_PosInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NaN
       | Parser_XPath.Ar_Sub -> XN_NegInf
       | Parser_XPath.Ar_Mul -> XN_NegInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_PosInf, XN_Finite (v, uu___)) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_PosInf
       | Parser_XPath.Ar_Sub -> XN_PosInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_PosInf else XN_NegInf
       | Parser_XPath.Ar_Div ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_PosInf else XN_NegInf
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_NegInf, XN_Finite (v, uu___)) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NegInf
       | Parser_XPath.Ar_Sub -> XN_NegInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_NegInf else XN_PosInf
       | Parser_XPath.Ar_Div ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_NegInf else XN_PosInf
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_Finite (v, uu___), XN_PosInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_PosInf
       | Parser_XPath.Ar_Sub -> XN_NegInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_PosInf else XN_NegInf
       | Parser_XPath.Ar_Div -> XN_Finite (Prims.int_zero, Prims.int_zero)
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_Finite (v, uu___), XN_NegInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NegInf
       | Parser_XPath.Ar_Sub -> XN_PosInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_NegInf else XN_PosInf
       | Parser_XPath.Ar_Div -> XN_Finite (Prims.int_zero, Prims.int_zero)
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_Finite (v1, s1), XN_Finite (v2, s2)) ->
      (match op with
       | Parser_XPath.Ar_Add ->
           let uu___ = xn_align v1 s1 v2 s2 in
           (match uu___ with | (n1, n2, s) -> XN_Finite ((n1 + n2), s))
       | Parser_XPath.Ar_Sub ->
           let uu___ = xn_align v1 s1 v2 s2 in
           (match uu___ with | (n1, n2, s) -> XN_Finite ((n1 - n2), s))
       | Parser_XPath.Ar_Mul -> XN_Finite ((v1 * v2), (s1 + s2))
       | Parser_XPath.Ar_Div ->
           if v2 = Prims.int_zero
           then
             (if v1 = Prims.int_zero
              then XN_NaN
              else if v1 > Prims.int_zero then XN_PosInf else XN_NegInf)
           else
             (let extra = (Prims.of_int (12)) in
              let scaled = v1 * (xn_pow10 (s2 + extra)) in
              XN_Finite ((scaled / v2), (s1 + extra)))
       | Parser_XPath.Ar_Mod ->
           if v2 = Prims.int_zero
           then XN_NaN
           else
             (let uu___1 = xn_align v1 s1 v2 s2 in
              match uu___1 with
              | (n1, n2, s) ->
                  if n2 = Prims.int_zero
                  then XN_NaN
                  else XN_Finite ((n1 - ((n1 / n2) * n2)), s)))
let rec xn_list_drop_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then xn_list_drop_while f xs else x :: xs
let string_to_xn (s : Prims.string) : xpath_number=
  let len = FStar_String.strlen s in
  let cs = FStar_String.list_of_string s in
  let is_sp c = (((c = 32) || (c = 9)) || (c = 10)) || (c = 13) in
  let trimmed =
    FStar_List_Tot_Base.rev
      (xn_list_drop_while is_sp
         (FStar_List_Tot_Base.rev (xn_list_drop_while is_sp cs))) in
  match trimmed with
  | [] -> XN_NaN
  | hd::tl ->
      let uu___ = if hd = 45 then (true, tl) else (false, trimmed) in
      (match uu___ with
       | (neg, digits) ->
           let s' = FStar_String.string_of_list digits in
           (match Parser_XPath.parse_number_lit s' Prims.int_zero with
            | FStar_Pervasives_Native.Some (v, scale, pos') ->
                if
                  (pos' = (FStar_String.strlen s')) &&
                    (pos' > Prims.int_zero)
                then
                  XN_Finite
                    (((if neg then Prims.int_zero - v else v)), scale)
                else XN_NaN
            | FStar_Pervasives_Native.None -> XN_NaN))
let xn_to_string (n : xpath_number) : Prims.string=
  match n with
  | XN_NaN -> "NaN"
  | XN_PosInf -> "Infinity"
  | XN_NegInf -> "-Infinity"
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then Prims.string_of_int v
      else
        (let neg = v < Prims.int_zero in
         let av = xn_abs v in
         let p = xn_pow10 s in
         let ip = if p = Prims.int_zero then av else av / p in
         let fp =
           if p = Prims.int_zero then Prims.int_zero else av - (ip * p) in
         if fp = Prims.int_zero
         then
           Prims.strcat (if neg && (ip <> Prims.int_zero) then "-" else "")
             (Prims.string_of_int ip)
         else
           (let rec pad n1 target =
              if (FStar_String.strlen n1) >= target
              then n1
              else pad (Prims.strcat "0" n1) (target - Prims.int_one) in
            let frac_str = pad (Prims.string_of_int fp) s in
            let rev_chars =
              FStar_List_Tot_Base.rev (FStar_String.list_of_string frac_str) in
            let rev_stripped = xn_list_drop_while (fun c -> c = 48) rev_chars in
            let stripped_chars =
              if Prims.uu___is_Nil rev_stripped
              then [48]
              else FStar_List_Tot_Base.rev rev_stripped in
            let stripped = FStar_String.string_of_list stripped_chars in
            Prims.strcat (if neg then "-" else "")
              (Prims.strcat (Prims.string_of_int ip)
                 (Prims.strcat "." stripped))))
let xn_is_zero (n : xpath_number) : Prims.bool=
  match n with
  | XN_Finite (uu___, uu___1) when uu___ = Prims.int_zero -> true
  | uu___ -> false
let xn_to_bool (n : xpath_number) : Prims.bool=
  match n with
  | XN_NaN -> false
  | XN_PosInf -> true
  | XN_NegInf -> true
  | XN_Finite (v, uu___) -> v <> Prims.int_zero
let xn_round (n : xpath_number) : xpath_number=
  match n with
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then n
      else
        (let p = xn_pow10 s in
         if p = Prims.int_zero
         then n
         else
           (let half = p / (Prims.of_int (2)) in
            let q =
              if v >= Prims.int_zero
              then (v + half) / p
              else
                Prims.int_zero -
                  (((Prims.int_zero - v) + ((p - half) - Prims.int_one)) / p) in
            XN_Finite (q, Prims.int_zero)))
  | uu___ -> n
let xn_floor (n : xpath_number) : xpath_number=
  match n with
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then n
      else
        (let p = xn_pow10 s in
         if p = Prims.int_zero
         then n
         else
           (let q =
              if v >= Prims.int_zero
              then v / p
              else
                Prims.int_zero -
                  ((((Prims.int_zero - v) + p) - Prims.int_one) / p) in
            XN_Finite (q, Prims.int_zero)))
  | uu___ -> n
let xn_ceiling (n : xpath_number) : xpath_number=
  match n with
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then n
      else
        (let p = xn_pow10 s in
         if p = Prims.int_zero
         then n
         else
           (let q =
              if v >= Prims.int_zero
              then ((v + p) - Prims.int_one) / p
              else Prims.int_zero - ((Prims.int_zero - v) / p) in
            XN_Finite (q, Prims.int_zero)))
  | uu___ -> n
type xctx_item =
  | CI_Elem of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node 
  | CI_Attr of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Parser_XML.xml_attribute 
  | CI_Text of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Prims.string 
  | CI_Comment of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Prims.string 
  | CI_PI of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Prims.string * Prims.string 
let uu___is_CI_Elem (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Elem (path, ancestors, node) -> true
  | uu___ -> false
let __proj__CI_Elem__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Elem (path, ancestors, node) -> path
let __proj__CI_Elem__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with | CI_Elem (path, ancestors, node) -> ancestors
let __proj__CI_Elem__item__node (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Elem (path, ancestors, node) -> node
let uu___is_CI_Attr (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Attr (path, ancestors, owner, attr) -> true
  | uu___ -> false
let __proj__CI_Attr__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> path
let __proj__CI_Attr__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> ancestors
let __proj__CI_Attr__item__owner (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> owner
let __proj__CI_Attr__item__attr (projectee : xctx_item) :
  Parser_XML.xml_attribute=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> attr
let uu___is_CI_Text (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Text (path, ancestors, parent, text) -> true
  | uu___ -> false
let __proj__CI_Text__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Text (path, ancestors, parent, text) -> path
let __proj__CI_Text__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with | CI_Text (path, ancestors, parent, text) -> ancestors
let __proj__CI_Text__item__parent (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Text (path, ancestors, parent, text) -> parent
let __proj__CI_Text__item__text (projectee : xctx_item) : Prims.string=
  match projectee with | CI_Text (path, ancestors, parent, text) -> text
let uu___is_CI_Comment (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Comment (path, ancestors, parent, text) -> true
  | uu___ -> false
let __proj__CI_Comment__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Comment (path, ancestors, parent, text) -> path
let __proj__CI_Comment__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | CI_Comment (path, ancestors, parent, text) -> ancestors
let __proj__CI_Comment__item__parent (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Comment (path, ancestors, parent, text) -> parent
let __proj__CI_Comment__item__text (projectee : xctx_item) : Prims.string=
  match projectee with | CI_Comment (path, ancestors, parent, text) -> text
let uu___is_CI_PI (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> true
  | uu___ -> false
let __proj__CI_PI__item__path (projectee : xctx_item) : Prims.int Prims.list=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> path
let __proj__CI_PI__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> ancestors
let __proj__CI_PI__item__parent (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> parent
let __proj__CI_PI__item__target (projectee : xctx_item) : Prims.string=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> target
let __proj__CI_PI__item__data (projectee : xctx_item) : Prims.string=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> data
let item_path (it : xctx_item) : Prims.int Prims.list=
  match it with
  | CI_Elem (p, uu___, uu___1) -> p
  | CI_Attr (p, uu___, uu___1, uu___2) -> p
  | CI_Text (p, uu___, uu___1, uu___2) -> p
  | CI_Comment (p, uu___, uu___1, uu___2) -> p
  | CI_PI (p, uu___, uu___1, uu___2, uu___3) -> p
let rec path_drop_last (l : Prims.int Prims.list) : Prims.int Prims.list=
  match l with
  | [] -> []
  | uu___::[] -> []
  | x::tl -> x :: (path_drop_last tl)
let attr_owner_path (p : Prims.int Prims.list) : Prims.int Prims.list=
  path_drop_last (path_drop_last p)
let rec path_compare (a : Prims.int Prims.list) (b : Prims.int Prims.list) :
  Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      if x < y
      then (Prims.of_int (-1))
      else if x > y then Prims.int_one else path_compare xs ys
let rec path_is_prefix (a : Prims.int Prims.list) (b : Prims.int Prims.list)
  : Prims.bool=
  match (a, b) with
  | ([], uu___) -> true
  | (uu___, []) -> false
  | (x::xs, y::ys) -> (x = y) && (path_is_prefix xs ys)
let rec children_with_paths (parent_path : Prims.int Prims.list)
  (new_anc : Parser_XML.xml_node Prims.list) (parent : Parser_XML.xml_node)
  (nodes : Parser_XML.xml_node Prims.list) (i : Prims.nat) :
  xctx_item Prims.list=
  match nodes with
  | [] -> []
  | c::rest ->
      let cpath = FStar_List_Tot_Base.op_At parent_path [i] in
      let item =
        match c with
        | Parser_XML.XElement (uu___, uu___1, uu___2) ->
            CI_Elem (cpath, new_anc, c)
        | Parser_XML.XText t -> CI_Text (cpath, new_anc, parent, t)
        | Parser_XML.XCDATA t -> CI_Text (cpath, new_anc, parent, t)
        | Parser_XML.XComment t -> CI_Comment (cpath, new_anc, parent, t)
        | Parser_XML.XPI (tg, d) -> CI_PI (cpath, new_anc, parent, tg, d) in
      item ::
        (children_with_paths parent_path new_anc parent rest
           (i + Prims.int_one))
let child_items (path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (node : Parser_XML.xml_node) :
  xctx_item Prims.list=
  children_with_paths path (node :: ancestors) node
    (Parser_XML.element_children node) Prims.int_zero
let rec attrs_with_paths (owner_path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (owner : Parser_XML.xml_node)
  (attrs : Parser_XML.xml_attribute Prims.list) (j : Prims.nat) :
  xctx_item Prims.list=
  match attrs with
  | [] -> []
  | a::rest ->
      (CI_Attr
         ((FStar_List_Tot_Base.op_At owner_path [(Prims.of_int (-1)); j]),
           ancestors, owner, a))
      ::
      (attrs_with_paths owner_path ancestors owner rest (j + Prims.int_one))
let attribute_items (path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (node : Parser_XML.xml_node) :
  xctx_item Prims.list=
  attrs_with_paths path ancestors node (Parser_XML.element_attrs node)
    Prims.int_zero
let rec descendant_items (path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (node : Parser_XML.xml_node) :
  xctx_item Prims.list=
  match node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      descendant_items_children path (node :: ancestors) node children
        Prims.int_zero
  | uu___ -> []
and descendant_items_children (parent_path : Prims.int Prims.list)
  (new_anc : Parser_XML.xml_node Prims.list) (parent : Parser_XML.xml_node)
  (nodes : Parser_XML.xml_node Prims.list) (i : Prims.nat) :
  xctx_item Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      let cpath = FStar_List_Tot_Base.op_At parent_path [i] in
      let self_item =
        match hd with
        | Parser_XML.XElement (uu___, uu___1, uu___2) ->
            [CI_Elem (cpath, new_anc, hd)]
        | Parser_XML.XText t -> [CI_Text (cpath, new_anc, parent, t)]
        | Parser_XML.XCDATA t -> [CI_Text (cpath, new_anc, parent, t)]
        | Parser_XML.XComment t -> [CI_Comment (cpath, new_anc, parent, t)]
        | Parser_XML.XPI (tg, d) -> [CI_PI (cpath, new_anc, parent, tg, d)] in
      FStar_List_Tot_Base.op_At self_item
        (FStar_List_Tot_Base.op_At (descendant_items cpath new_anc hd)
           (descendant_items_children parent_path new_anc parent tl
              (i + Prims.int_one)))
let rec ancestor_items (self_path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) : xctx_item Prims.list=
  match ancestors with
  | [] -> []
  | p::rest ->
      let ppath = path_drop_last self_path in (CI_Elem (ppath, rest, p)) ::
        (ancestor_items ppath rest)
let item_ancestors (it : xctx_item) : Parser_XML.xml_node Prims.list=
  match it with
  | CI_Elem (uu___, anc, uu___1) -> anc
  | CI_Attr (uu___, anc, uu___1, uu___2) -> anc
  | CI_Text (uu___, anc, uu___1, uu___2) -> anc
  | CI_Comment (uu___, anc, uu___1, uu___2) -> anc
  | CI_PI (uu___, anc, uu___1, uu___2, uu___3) -> anc
let parent_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Attr (p, anc, owner, uu___) ->
      [CI_Elem ((attr_owner_path p), anc, owner)]
  | CI_Elem (p, anc, uu___) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
  | CI_Text (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
  | CI_Comment (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
  | CI_PI (p, anc, uu___, uu___1, uu___2) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
let ancestor_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Attr (p, anc, owner, uu___) ->
      let opath = attr_owner_path p in (CI_Elem (opath, anc, owner)) ::
        (ancestor_items opath anc)
  | CI_Elem (p, anc, uu___) -> ancestor_items p anc
  | CI_Text (p, anc, uu___, uu___1) -> ancestor_items p anc
  | CI_Comment (p, anc, uu___, uu___1) -> ancestor_items p anc
  | CI_PI (p, anc, uu___, uu___1, uu___2) -> ancestor_items p anc
let child_axis (it : xctx_item) : xctx_item Prims.list=
  match it with | CI_Elem (p, anc, n) -> child_items p anc n | uu___ -> []
let descendant_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Elem (p, anc, n) -> descendant_items p anc n
  | uu___ -> []
let attribute_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Elem (p, anc, n) -> attribute_items p anc n
  | uu___ -> []
let siblings_of (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Elem (p, anc, uu___) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_Text (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_Comment (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_PI (p, anc, uu___, uu___1, uu___2) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_Attr (uu___, uu___1, uu___2, uu___3) -> []
let following_sibling_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.filter
    (fun s -> (path_compare (item_path s) p) > Prims.int_zero)
    (siblings_of it)
let preceding_sibling_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.rev
    (FStar_List_Tot_Base.filter
       (fun s -> (path_compare (item_path s) p) < Prims.int_zero)
       (siblings_of it))
let string_starts_with (s : Prims.string) (prefix : Prims.string) :
  Prims.bool=
  let lp = FStar_String.strlen prefix in
  ((FStar_String.strlen s) >= lp) &&
    ((FStar_String.sub s Prims.int_zero lp) = prefix)
let matches_node_test (test : Parser_XPath.xp_nodetest) (it : xctx_item) :
  Prims.bool=
  match (test, it) with
  | (Parser_XPath.NT_Node, uu___) -> true
  | (Parser_XPath.NT_Text, CI_Text (uu___, uu___1, uu___2, uu___3)) -> true
  | (Parser_XPath.NT_Text, uu___) -> false
  | (Parser_XPath.NT_Comment, CI_Comment (uu___, uu___1, uu___2, uu___3)) ->
      true
  | (Parser_XPath.NT_Comment, uu___) -> false
  | (Parser_XPath.NT_PI (FStar_Pervasives_Native.None), CI_PI
     (uu___, uu___1, uu___2, uu___3, uu___4)) -> true
  | (Parser_XPath.NT_PI (FStar_Pervasives_Native.Some tgt), CI_PI
     (uu___, uu___1, uu___2, t, uu___3)) -> t = tgt
  | (Parser_XPath.NT_PI uu___, uu___1) -> false
  | (Parser_XPath.NT_Any, CI_Elem (uu___, uu___1, uu___2)) -> true
  | (Parser_XPath.NT_Any, CI_Attr (uu___, uu___1, uu___2, uu___3)) -> true
  | (Parser_XPath.NT_Any, uu___) -> false
  | (Parser_XPath.NT_Name nm, CI_Elem (uu___, uu___1, n)) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t -> t = nm
       | FStar_Pervasives_Native.None -> false)
  | (Parser_XPath.NT_Name nm, CI_Attr (uu___, uu___1, uu___2, a)) ->
      a.Parser_XML.attr_name = nm
  | (Parser_XPath.NT_Name uu___, uu___1) -> false
  | (Parser_XPath.NT_Prefix pfx, CI_Elem (uu___, uu___1, n)) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t ->
           string_starts_with t (Prims.strcat pfx ":")
       | FStar_Pervasives_Native.None -> false)
  | (Parser_XPath.NT_Prefix pfx, CI_Attr (uu___, uu___1, uu___2, a)) ->
      string_starts_with a.Parser_XML.attr_name (Prims.strcat pfx ":")
  | (Parser_XPath.NT_Prefix uu___, uu___1) -> false
let filter_by_node_test (test : Parser_XPath.xp_nodetest)
  (items : xctx_item Prims.list) : xctx_item Prims.list=
  FStar_List_Tot_Base.filter (matches_node_test test) items
let rec list_last_or (default_val : Parser_XML.xml_node)
  (l : Parser_XML.xml_node Prims.list) : Parser_XML.xml_node=
  match l with
  | [] -> default_val
  | x::[] -> x
  | uu___::tl -> list_last_or default_val tl
let root_of_item (it : xctx_item) : Parser_XML.xml_node=
  let self_node =
    match it with
    | CI_Elem (uu___, uu___1, n) -> n
    | CI_Attr (uu___, uu___1, owner, uu___2) -> owner
    | CI_Text (uu___, uu___1, parent, uu___2) -> parent
    | CI_Comment (uu___, uu___1, parent, uu___2) -> parent
    | CI_PI (uu___, uu___1, parent, uu___2, uu___3) -> parent in
  list_last_or self_node (item_ancestors it)
let all_document_items (it : xctx_item) : xctx_item Prims.list=
  let root = root_of_item it in (CI_Elem ([], [], root)) ::
    (descendant_items [] [] root)
let following_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.filter
    (fun x ->
       ((path_compare (item_path x) p) > Prims.int_zero) &&
         (Prims.op_Negation (path_is_prefix p (item_path x))))
    (all_document_items it)
let preceding_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.rev
    (FStar_List_Tot_Base.filter
       (fun x ->
          ((path_compare (item_path x) p) < Prims.int_zero) &&
            (Prims.op_Negation (path_is_prefix (item_path x) p)))
       (all_document_items it))
let apply_axis (ax : Parser_XPath.xp_axis) (it : xctx_item) :
  xctx_item Prims.list=
  match ax with
  | Parser_XPath.Ax_Self -> [it]
  | Parser_XPath.Ax_Child -> child_axis it
  | Parser_XPath.Ax_Descendant -> descendant_axis it
  | Parser_XPath.Ax_DescendantOrSelf -> it :: (descendant_axis it)
  | Parser_XPath.Ax_Parent -> parent_axis it
  | Parser_XPath.Ax_Ancestor -> ancestor_axis it
  | Parser_XPath.Ax_AncestorOrSelf -> it :: (ancestor_axis it)
  | Parser_XPath.Ax_Attribute -> attribute_axis it
  | Parser_XPath.Ax_FollowingSibling -> following_sibling_axis it
  | Parser_XPath.Ax_PrecedingSibling -> preceding_sibling_axis it
  | Parser_XPath.Ax_Following -> following_axis it
  | Parser_XPath.Ax_Preceding -> preceding_axis it
type xp_value =
  | XV_Nodes of xctx_item Prims.list 
  | XV_Bool of Prims.bool 
  | XV_Num of xpath_number 
  | XV_Str of Prims.string 
let uu___is_XV_Nodes (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Nodes _0 -> true | uu___ -> false
let __proj__XV_Nodes__item___0 (projectee : xp_value) : xctx_item Prims.list=
  match projectee with | XV_Nodes _0 -> _0
let uu___is_XV_Bool (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Bool _0 -> true | uu___ -> false
let __proj__XV_Bool__item___0 (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Bool _0 -> _0
let uu___is_XV_Num (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Num _0 -> true | uu___ -> false
let __proj__XV_Num__item___0 (projectee : xp_value) : xpath_number=
  match projectee with | XV_Num _0 -> _0
let uu___is_XV_Str (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Str _0 -> true | uu___ -> false
let __proj__XV_Str__item___0 (projectee : xp_value) : Prims.string=
  match projectee with | XV_Str _0 -> _0
type xp_env =
  {
  env_item: xctx_item ;
  env_pos: Prims.nat ;
  env_size: Prims.nat ;
  env_vars: (Prims.string * xp_value) Prims.list }
let __proj__Mkxp_env__item__env_item (projectee : xp_env) : xctx_item=
  match projectee with
  | { env_item; env_pos; env_size; env_vars;_} -> env_item
let __proj__Mkxp_env__item__env_pos (projectee : xp_env) : Prims.nat=
  match projectee with
  | { env_item; env_pos; env_size; env_vars;_} -> env_pos
let __proj__Mkxp_env__item__env_size (projectee : xp_env) : Prims.nat=
  match projectee with
  | { env_item; env_pos; env_size; env_vars;_} -> env_size
let __proj__Mkxp_env__item__env_vars (projectee : xp_env) :
  (Prims.string * xp_value) Prims.list=
  match projectee with
  | { env_item; env_pos; env_size; env_vars;_} -> env_vars
let lookup_var (vars : (Prims.string * xp_value) Prims.list)
  (name : Prims.string) : xp_value FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find
          (fun kv -> (FStar_Pervasives_Native.fst kv) = name) vars
  with
  | FStar_Pervasives_Native.Some (uu___, v) -> FStar_Pervasives_Native.Some v
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let item_string_value (it : xctx_item) : Prims.string=
  match it with
  | CI_Elem (uu___, uu___1, n) -> Parser_XML.text_content n
  | CI_Attr (uu___, uu___1, uu___2, a) -> a.Parser_XML.attr_value
  | CI_Text (uu___, uu___1, uu___2, t) -> t
  | CI_Comment (uu___, uu___1, uu___2, t) -> t
  | CI_PI (uu___, uu___1, uu___2, uu___3, d) -> d
let nodeset_string_value (items : xctx_item Prims.list) : Prims.string=
  match items with | [] -> "" | hd::uu___ -> item_string_value hd
let to_string_val (v : xp_value) : Prims.string=
  match v with
  | XV_Str s -> s
  | XV_Num n -> xn_to_string n
  | XV_Bool b -> if b then "true" else "false"
  | XV_Nodes items -> nodeset_string_value items
let to_bool_val (v : xp_value) : Prims.bool=
  match v with
  | XV_Bool b -> b
  | XV_Num n -> xn_to_bool n
  | XV_Str s -> (FStar_String.strlen s) > Prims.int_zero
  | XV_Nodes items -> Prims.op_Negation (Prims.uu___is_Nil items)
let to_number_val (v : xp_value) : xpath_number=
  match v with
  | XV_Num n -> n
  | XV_Bool b ->
      XN_Finite
        ((if b then Prims.int_one else Prims.int_zero), Prims.int_zero)
  | XV_Str s -> string_to_xn s
  | XV_Nodes items -> string_to_xn (nodeset_string_value items)
let xn_finite_int (n : xpath_number) :
  Prims.int FStar_Pervasives_Native.option=
  match n with
  | XN_Finite (v, uu___) when uu___ = Prims.int_zero ->
      FStar_Pervasives_Native.Some v
  | XN_Finite (v, s) ->
      let p = xn_pow10 s in
      if p = Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some (v / p)
  | uu___ -> FStar_Pervasives_Native.None
let apply_comp_bool (op : Parser_XPath.xp_comp_op) (a : Prims.bool)
  (b : Prims.bool) : Prims.bool=
  match op with
  | Parser_XPath.Cmp_Eq -> a = b
  | Parser_XPath.Cmp_Ne -> a <> b
  | Parser_XPath.Cmp_Lt -> (Prims.op_Negation a) && b
  | Parser_XPath.Cmp_Le -> (Prims.op_Negation a) || b
  | Parser_XPath.Cmp_Gt -> a && (Prims.op_Negation b)
  | Parser_XPath.Cmp_Ge -> a || (Prims.op_Negation b)
let apply_comp_num (op : Parser_XPath.xp_comp_op) (a : xpath_number)
  (b : xpath_number) : Prims.bool=
  match xn_compare a b with
  | FStar_Pervasives_Native.None -> op = Parser_XPath.Cmp_Ne
  | FStar_Pervasives_Native.Some c ->
      (match op with
       | Parser_XPath.Cmp_Eq -> c = Prims.int_zero
       | Parser_XPath.Cmp_Ne -> c <> Prims.int_zero
       | Parser_XPath.Cmp_Lt -> c < Prims.int_zero
       | Parser_XPath.Cmp_Le -> c <= Prims.int_zero
       | Parser_XPath.Cmp_Gt -> c > Prims.int_zero
       | Parser_XPath.Cmp_Ge -> c >= Prims.int_zero)
let apply_comp_str (op : Parser_XPath.xp_comp_op) (a : Prims.string)
  (b : Prims.string) : Prims.bool=
  match op with
  | Parser_XPath.Cmp_Eq -> a = b
  | Parser_XPath.Cmp_Ne -> a <> b
  | Parser_XPath.Cmp_Lt -> (FStar_String.compare a b) < Prims.int_zero
  | Parser_XPath.Cmp_Le -> (FStar_String.compare a b) <= Prims.int_zero
  | Parser_XPath.Cmp_Gt -> (FStar_String.compare a b) > Prims.int_zero
  | Parser_XPath.Cmp_Ge -> (FStar_String.compare a b) >= Prims.int_zero
let rec exists_str (pred : Prims.string -> Prims.bool)
  (items : xctx_item Prims.list) : Prims.bool=
  match items with
  | [] -> false
  | hd::tl -> (pred (item_string_value hd)) || (exists_str pred tl)
let is_relational_op (op : Parser_XPath.xp_comp_op) : Prims.bool=
  match op with
  | Parser_XPath.Cmp_Lt -> true
  | Parser_XPath.Cmp_Le -> true
  | Parser_XPath.Cmp_Gt -> true
  | Parser_XPath.Cmp_Ge -> true
  | uu___ -> false
let xp_compare (op : Parser_XPath.xp_comp_op) (a : xp_value) (b : xp_value) :
  Prims.bool=
  match (a, b) with
  | (XV_Nodes na, XV_Nodes nb) ->
      if is_relational_op op
      then
        exists_str
          (fun sa ->
             exists_str
               (fun sb ->
                  apply_comp_num op (string_to_xn sa) (string_to_xn sb)) nb)
          na
      else
        exists_str
          (fun sa -> exists_str (fun sb -> apply_comp_str op sa sb) nb) na
  | (XV_Nodes na, XV_Num nb) ->
      exists_str (fun sa -> apply_comp_num op (string_to_xn sa) nb) na
  | (XV_Num na, XV_Nodes nb) ->
      exists_str (fun sb -> apply_comp_num op na (string_to_xn sb)) nb
  | (XV_Nodes na, XV_Str sb) ->
      if is_relational_op op
      then
        exists_str
          (fun sa -> apply_comp_num op (string_to_xn sa) (string_to_xn sb))
          na
      else exists_str (fun sa -> apply_comp_str op sa sb) na
  | (XV_Str sa, XV_Nodes nb) ->
      if is_relational_op op
      then
        exists_str
          (fun sb -> apply_comp_num op (string_to_xn sa) (string_to_xn sb))
          nb
      else exists_str (fun sb -> apply_comp_str op sa sb) nb
  | (XV_Nodes na, XV_Bool bb) ->
      apply_comp_bool op (Prims.op_Negation (Prims.uu___is_Nil na)) bb
  | (XV_Bool ba, XV_Nodes nb) ->
      apply_comp_bool op ba (Prims.op_Negation (Prims.uu___is_Nil nb))
  | (XV_Bool uu___, uu___1) ->
      apply_comp_bool op (to_bool_val a) (to_bool_val b)
  | (uu___, XV_Bool uu___1) ->
      apply_comp_bool op (to_bool_val a) (to_bool_val b)
  | (XV_Num uu___, uu___1) ->
      apply_comp_num op (to_number_val a) (to_number_val b)
  | (uu___, XV_Num uu___1) ->
      apply_comp_num op (to_number_val a) (to_number_val b)
  | (uu___, uu___1) -> apply_comp_str op (to_string_val a) (to_string_val b)
let rec str_find_from (s : Prims.string) (sub : Prims.string)
  (pos : Prims.nat) (slen : Prims.nat) (sublen : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if (pos + sublen) > slen
  then FStar_Pervasives_Native.None
  else
    if (FStar_String.sub s pos sublen) = sub
    then FStar_Pervasives_Native.Some pos
    else
      if pos >= slen
      then FStar_Pervasives_Native.None
      else str_find_from s sub (pos + Prims.int_one) slen sublen
let str_find (s : Prims.string) (sub : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  let slen = FStar_String.strlen s in
  let sublen = FStar_String.strlen sub in
  if sublen = Prims.int_zero
  then FStar_Pervasives_Native.Some Prims.int_zero
  else str_find_from s sub Prims.int_zero slen sublen
let string_starts_with2 (s : Prims.string) (prefix : Prims.string) :
  Prims.bool= string_starts_with s prefix
let is_xp_space (c : FStar_Char.char) : Prims.bool=
  (((c = 32) || (c = 9)) || (c = 10)) || (c = 13)
let rec normalize_space_chars (cs : FStar_Char.char Prims.list)
  (in_space : Prims.bool) : FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if is_xp_space c
      then
        (if in_space
         then normalize_space_chars rest true
         else 32 :: (normalize_space_chars rest true))
      else c :: (normalize_space_chars rest false)
let normalize_space (s : Prims.string) : Prims.string=
  let collapsed = normalize_space_chars (FStar_String.list_of_string s) true in
  let rev = FStar_List_Tot_Base.rev collapsed in
  let rev' = match rev with | 32::rest -> rest | uu___ -> rev in
  FStar_String.string_of_list (FStar_List_Tot_Base.rev rev')
let xn_le_int (a : xpath_number) (k : Prims.int) : Prims.bool=
  match xn_compare a (XN_Finite (k, Prims.int_zero)) with
  | FStar_Pervasives_Native.Some c -> c <= Prims.int_zero
  | FStar_Pervasives_Native.None -> false
let xn_lt_int (k : Prims.int) (a : xpath_number) : Prims.bool=
  match xn_compare (XN_Finite (k, Prims.int_zero)) a with
  | FStar_Pervasives_Native.Some c -> c < Prims.int_zero
  | FStar_Pervasives_Native.None -> false
let rec substring_collect (s : Prims.string) (start_r : xpath_number)
  (end_bound : xpath_number) (p : Prims.nat) (slen : Prims.nat) :
  Prims.string=
  if p > slen
  then ""
  else
    (let rest =
       substring_collect s start_r end_bound (p + Prims.int_one) slen in
     if (xn_le_int start_r p) && (xn_lt_int p end_bound)
     then
       FStar_String.concat ""
         [FStar_String.sub s (p - Prims.int_one) Prims.int_one; rest]
     else rest)
let substring_impl (s : Prims.string) (start_n : xpath_number)
  (len_n : xpath_number) : Prims.string=
  let start_r = xn_round start_n in
  let len_r = xn_round len_n in
  let end_bound = xn_arith Parser_XPath.Ar_Add start_r len_r in
  substring_collect s start_r end_bound Prims.int_one (FStar_String.strlen s)
let item_qname (it : xctx_item) : Prims.string=
  match it with
  | CI_Elem (uu___, uu___1, n) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None -> "")
  | CI_Attr (uu___, uu___1, uu___2, a) -> a.Parser_XML.attr_name
  | CI_PI (uu___, uu___1, uu___2, tg, uu___3) -> tg
  | uu___ -> ""
let rec find_char_from (s : Prims.string) (c : FStar_Char.char)
  (pos : Prims.nat) (len : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if pos >= len
  then FStar_Pervasives_Native.None
  else
    if (FStar_String.index s pos) = c
    then FStar_Pervasives_Native.Some pos
    else find_char_from s c (pos + Prims.int_one) len
let local_name_of (qn : Prims.string) : Prims.string=
  match find_char_from qn 58 Prims.int_zero (FStar_String.strlen qn) with
  | FStar_Pervasives_Native.Some i ->
      FStar_String.sub qn (i + Prims.int_one)
        (((FStar_String.strlen qn) - i) - Prims.int_one)
  | FStar_Pervasives_Native.None -> qn
let rec sum_items (items : xctx_item Prims.list) : xpath_number=
  match items with
  | [] -> XN_Finite (Prims.int_zero, Prims.int_zero)
  | hd::tl ->
      xn_arith Parser_XPath.Ar_Add (string_to_xn (item_string_value hd))
        (sum_items tl)
let rec insert_by_doc (x : xctx_item) (l : xctx_item Prims.list) :
  xctx_item Prims.list=
  match l with
  | [] -> [x]
  | y::ys ->
      let c = path_compare (item_path x) (item_path y) in
      if c < Prims.int_zero
      then x :: l
      else if c = Prims.int_zero then l else y :: (insert_by_doc x ys)
let rec doc_sort_dedup (l : xctx_item Prims.list) : xctx_item Prims.list=
  match l with | [] -> [] | x::xs -> insert_by_doc x (doc_sort_dedup xs)
let rec xp_expr_size (e : Parser_XPath.xp_expr) : Prims.nat=
  match e with
  | Parser_XPath.XE_Path (uu___, steps) ->
      Prims.int_one + (xp_steps_size steps)
  | Parser_XPath.XE_FilterPath (primary, preds, steps) ->
      ((Prims.int_one + (xp_expr_size primary)) + (xp_exprs_size preds)) +
        (xp_steps_size steps)
  | Parser_XPath.XE_Union (a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Or (a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_And (a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Compare (uu___, a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Arith (uu___, a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Neg a -> Prims.int_one + (xp_expr_size a)
  | Parser_XPath.XE_Number (uu___, uu___1) -> Prims.int_one
  | Parser_XPath.XE_Literal uu___ -> Prims.int_one
  | Parser_XPath.XE_VarRef uu___ -> Prims.int_one
  | Parser_XPath.XE_FunCall (uu___, args) ->
      Prims.int_one + (xp_exprs_size args)
and xp_exprs_size (es : Parser_XPath.xp_expr Prims.list) : Prims.nat=
  match es with
  | [] -> Prims.int_zero
  | hd::tl -> (Prims.int_one + (xp_expr_size hd)) + (xp_exprs_size tl)
and xp_steps_size (ss : Parser_XPath.xp_step Prims.list) : Prims.nat=
  match ss with
  | [] -> Prims.int_zero
  | hd::tl -> (Prims.int_one + (xp_step_size hd)) + (xp_steps_size tl)
and xp_step_size (s : Parser_XPath.xp_step) : Prims.nat=
  Prims.int_one + (xp_exprs_size s.Parser_XPath.step_preds)
let rec xml_node_count (n : Parser_XML.xml_node) : Prims.nat=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      Prims.int_one + (xml_nodes_count children)
  | uu___ -> Prims.int_one
and xml_nodes_count (ns : Parser_XML.xml_node Prims.list) : Prims.nat=
  match ns with
  | [] -> Prims.int_zero
  | hd::tl -> (xml_node_count hd) + (xml_nodes_count tl)
let initial_eval_fuel (e : Parser_XPath.xp_expr) (doc_nodes : Prims.nat) :
  Prims.nat=
  (((xp_expr_size e) + Prims.int_one) *
     ((doc_nodes + Prims.int_one) * (Prims.of_int (24))))
    + (Prims.of_int (4096))
let rec eval_expr (fuel : Prims.nat) (env : xp_env)
  (e : Parser_XPath.xp_expr) : xp_value=
  if fuel = Prims.int_zero
  then XV_Str ""
  else
    (match e with
     | Parser_XPath.XE_Number (v, s) -> XV_Num (XN_Finite (v, s))
     | Parser_XPath.XE_Literal s -> XV_Str s
     | Parser_XPath.XE_VarRef name ->
         (match lookup_var env.env_vars name with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None -> XV_Str "")
     | Parser_XPath.XE_Neg e1 ->
         XV_Num
           (xn_neg (to_number_val (eval_expr (fuel - Prims.int_one) env e1)))
     | Parser_XPath.XE_Arith (op, a, b) ->
         XV_Num
           (xn_arith op
              (to_number_val (eval_expr (fuel - Prims.int_one) env a))
              (to_number_val (eval_expr (fuel - Prims.int_one) env b)))
     | Parser_XPath.XE_Compare (op, a, b) ->
         XV_Bool
           (xp_compare op (eval_expr (fuel - Prims.int_one) env a)
              (eval_expr (fuel - Prims.int_one) env b))
     | Parser_XPath.XE_And (a, b) ->
         XV_Bool
           ((to_bool_val (eval_expr (fuel - Prims.int_one) env a)) &&
              (to_bool_val (eval_expr (fuel - Prims.int_one) env b)))
     | Parser_XPath.XE_Or (a, b) ->
         XV_Bool
           ((to_bool_val (eval_expr (fuel - Prims.int_one) env a)) ||
              (to_bool_val (eval_expr (fuel - Prims.int_one) env b)))
     | Parser_XPath.XE_Union (a, b) ->
         (match ((eval_expr (fuel - Prims.int_one) env a),
                  (eval_expr (fuel - Prims.int_one) env b))
          with
          | (XV_Nodes na, XV_Nodes nb) ->
              XV_Nodes (doc_sort_dedup (FStar_List_Tot_Base.op_At na nb))
          | (XV_Nodes na, uu___1) -> XV_Nodes (doc_sort_dedup na)
          | (uu___1, XV_Nodes nb) -> XV_Nodes (doc_sort_dedup nb)
          | (uu___1, uu___2) -> XV_Nodes [])
     | Parser_XPath.XE_FunCall (name, args) ->
         eval_funcall (fuel - Prims.int_one) env name args
     | Parser_XPath.XE_Path (absolute, steps) ->
         if absolute
         then
           XV_Nodes
             (eval_absolute_steps (fuel - Prims.int_one) env.env_vars
                (root_of_item env.env_item) steps)
         else
           XV_Nodes
             (eval_steps (fuel - Prims.int_one) env.env_vars [env.env_item]
                steps)
     | Parser_XPath.XE_FilterPath (primary, preds, steps) ->
         let pv = eval_expr (fuel - Prims.int_one) env primary in
         (match pv with
          | XV_Nodes items0 ->
              let items1 =
                filter_items_by_preds (fuel - Prims.int_one) env.env_vars
                  items0 preds in
              XV_Nodes
                (eval_steps (fuel - Prims.int_one) env.env_vars items1 steps)
          | other ->
              if (Prims.uu___is_Nil preds) && (Prims.uu___is_Nil steps)
              then other
              else XV_Nodes []))
and eval_absolute_steps (fuel : Prims.nat)
  (vars : (Prims.string * xp_value) Prims.list)
  (root_node : Parser_XML.xml_node) (steps : Parser_XPath.xp_step Prims.list)
  : xctx_item Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (let root_item = CI_Elem ([], [], root_node) in
     match steps with
     | [] -> [root_item]
     | s::rest ->
         let expansion =
           match s.Parser_XPath.step_axis with
           | Parser_XPath.Ax_Child ->
               filter_by_node_test s.Parser_XPath.step_test [root_item]
           | Parser_XPath.Ax_Self ->
               filter_by_node_test s.Parser_XPath.step_test [root_item]
           | Parser_XPath.Ax_DescendantOrSelf ->
               filter_by_node_test s.Parser_XPath.step_test (root_item ::
                 (descendant_items [] [] root_node))
           | uu___1 -> [] in
         let kept =
           filter_items_by_preds (fuel - Prims.int_one) vars expansion
             s.Parser_XPath.step_preds in
         eval_steps (fuel - Prims.int_one) vars kept rest)
and eval_steps (fuel : Prims.nat)
  (vars : (Prims.string * xp_value) Prims.list)
  (items : xctx_item Prims.list) (steps : Parser_XPath.xp_step Prims.list) :
  xctx_item Prims.list=
  if fuel = Prims.int_zero
  then items
  else
    (match steps with
     | [] -> items
     | s::rest ->
         let expanded =
           expand_step_over_items (fuel - Prims.int_one) vars s items in
         eval_steps (fuel - Prims.int_one) vars expanded rest)
and expand_step_over_items (fuel : Prims.nat)
  (vars : (Prims.string * xp_value) Prims.list) (s : Parser_XPath.xp_step)
  (items : xctx_item Prims.list) : xctx_item Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match items with
     | [] -> []
     | it::rest ->
         let raw = apply_axis s.Parser_XPath.step_axis it in
         let tested = filter_by_node_test s.Parser_XPath.step_test raw in
         let kept =
           filter_items_by_preds (fuel - Prims.int_one) vars tested
             s.Parser_XPath.step_preds in
         FStar_List_Tot_Base.op_At kept
           (expand_step_over_items (fuel - Prims.int_one) vars s rest))
and filter_items_by_preds (fuel : Prims.nat)
  (vars : (Prims.string * xp_value) Prims.list)
  (items : xctx_item Prims.list) (preds : Parser_XPath.xp_expr Prims.list) :
  xctx_item Prims.list=
  if fuel = Prims.int_zero
  then items
  else
    (match preds with
     | [] -> items
     | p::rest ->
         let size = FStar_List_Tot_Base.length items in
         let kept =
           filter_one_pred (fuel - Prims.int_one) vars p items size
             Prims.int_one in
         filter_items_by_preds (fuel - Prims.int_one) vars kept rest)
and filter_one_pred (fuel : Prims.nat)
  (vars : (Prims.string * xp_value) Prims.list) (p : Parser_XPath.xp_expr)
  (items : xctx_item Prims.list) (size : Prims.nat) (pos : Prims.nat) :
  xctx_item Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match items with
     | [] -> []
     | it::rest ->
         let e =
           { env_item = it; env_pos = pos; env_size = size; env_vars = vars } in
         let v = eval_expr (fuel - Prims.int_one) e p in
         let keep =
           match v with
           | XV_Num n ->
               (match xn_finite_int (xn_round n) with
                | FStar_Pervasives_Native.Some k -> k = pos
                | FStar_Pervasives_Native.None -> false)
           | uu___1 -> to_bool_val v in
         let tail =
           filter_one_pred (fuel - Prims.int_one) vars p rest size
             (pos + Prims.int_one) in
         if keep then it :: tail else tail)
and eval_concat_args (fuel : Prims.nat) (env : xp_env)
  (args : Parser_XPath.xp_expr Prims.list) : Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    (match args with
     | [] -> ""
     | a::rest ->
         Prims.strcat
           (to_string_val (eval_expr (fuel - Prims.int_one) env a))
           (eval_concat_args (fuel - Prims.int_one) env rest))
and eval_funcall (fuel : Prims.nat) (env : xp_env) (name : Prims.string)
  (args : Parser_XPath.xp_expr Prims.list) : xp_value=
  if fuel = Prims.int_zero
  then XV_Str ""
  else
    if name = "position"
    then XV_Num (XN_Finite ((env.env_pos), Prims.int_zero))
    else
      if name = "last"
      then XV_Num (XN_Finite ((env.env_size), Prims.int_zero))
      else
        if name = "count"
        then
          (match args with
           | a::[] ->
               (match eval_expr (fuel - Prims.int_one) env a with
                | XV_Nodes items ->
                    XV_Num
                      (XN_Finite
                         ((FStar_List_Tot_Base.length items), Prims.int_zero))
                | uu___3 ->
                    XV_Num (XN_Finite (Prims.int_zero, Prims.int_zero)))
           | uu___3 -> XV_Num (XN_Finite (Prims.int_zero, Prims.int_zero)))
        else
          if (name = "name") || (name = "local-name")
          then
            (let items =
               match args with
               | [] -> [env.env_item]
               | a::uu___4 ->
                   (match eval_expr (fuel - Prims.int_one) env a with
                    | XV_Nodes its -> its
                    | uu___5 -> []) in
             match items with
             | [] -> XV_Str ""
             | it::uu___4 ->
                 let qn = item_qname it in
                 XV_Str
                   (if name = "local-name" then local_name_of qn else qn))
          else
            if name = "current"
            then XV_Nodes [env.env_item]
            else
              if name = "string"
              then
                (match args with
                 | [] -> XV_Str (item_string_value env.env_item)
                 | a::uu___6 ->
                     XV_Str
                       (to_string_val
                          (eval_expr (fuel - Prims.int_one) env a)))
              else
                if name = "concat"
                then
                  XV_Str (eval_concat_args (fuel - Prims.int_one) env args)
                else
                  if name = "contains"
                  then
                    (match args with
                     | a::b::[] ->
                         let s =
                           to_string_val
                             (eval_expr (fuel - Prims.int_one) env a) in
                         let sub =
                           to_string_val
                             (eval_expr (fuel - Prims.int_one) env b) in
                         XV_Bool
                           (FStar_Pervasives_Native.uu___is_Some
                              (str_find s sub))
                     | uu___8 -> XV_Bool false)
                  else
                    if name = "starts-with"
                    then
                      (match args with
                       | a::b::[] ->
                           XV_Bool
                             (string_starts_with2
                                (to_string_val
                                   (eval_expr (fuel - Prims.int_one) env a))
                                (to_string_val
                                   (eval_expr (fuel - Prims.int_one) env b)))
                       | uu___9 -> XV_Bool false)
                    else
                      if name = "substring-before"
                      then
                        (match args with
                         | a::b::[] ->
                             let s =
                               to_string_val
                                 (eval_expr (fuel - Prims.int_one) env a) in
                             let sub =
                               to_string_val
                                 (eval_expr (fuel - Prims.int_one) env b) in
                             (match str_find s sub with
                              | FStar_Pervasives_Native.Some i ->
                                  XV_Str
                                    (FStar_String.sub s Prims.int_zero i)
                              | FStar_Pervasives_Native.None -> XV_Str "")
                         | uu___10 -> XV_Str "")
                      else
                        if name = "substring-after"
                        then
                          (match args with
                           | a::b::[] ->
                               let s =
                                 to_string_val
                                   (eval_expr (fuel - Prims.int_one) env a) in
                               let sub =
                                 to_string_val
                                   (eval_expr (fuel - Prims.int_one) env b) in
                               (match str_find s sub with
                                | FStar_Pervasives_Native.Some i ->
                                    let sl = FStar_String.strlen sub in
                                    XV_Str
                                      (FStar_String.sub s (i + sl)
                                         (((FStar_String.strlen s) - i) - sl))
                                | FStar_Pervasives_Native.None -> XV_Str "")
                           | uu___11 -> XV_Str "")
                        else
                          if name = "substring"
                          then
                            (match args with
                             | a::b::[] ->
                                 let s =
                                   to_string_val
                                     (eval_expr (fuel - Prims.int_one) env a) in
                                 let sv =
                                   to_number_val
                                     (eval_expr (fuel - Prims.int_one) env b) in
                                 XV_Str (substring_impl s sv XN_PosInf)
                             | a::b::c::[] ->
                                 let s =
                                   to_string_val
                                     (eval_expr (fuel - Prims.int_one) env a) in
                                 let sv =
                                   to_number_val
                                     (eval_expr (fuel - Prims.int_one) env b) in
                                 let lv =
                                   to_number_val
                                     (eval_expr (fuel - Prims.int_one) env c) in
                                 XV_Str (substring_impl s sv lv)
                             | uu___12 -> XV_Str "")
                          else
                            if name = "string-length"
                            then
                              (let s =
                                 match args with
                                 | [] -> item_string_value env.env_item
                                 | a::uu___13 ->
                                     to_string_val
                                       (eval_expr (fuel - Prims.int_one) env
                                          a) in
                               XV_Num
                                 (XN_Finite
                                    ((FStar_String.strlen s), Prims.int_zero)))
                            else
                              if name = "normalize-space"
                              then
                                (let s =
                                   match args with
                                   | [] -> item_string_value env.env_item
                                   | a::uu___14 ->
                                       to_string_val
                                         (eval_expr (fuel - Prims.int_one)
                                            env a) in
                                 XV_Str (normalize_space s))
                              else
                                if name = "not"
                                then
                                  (match args with
                                   | a::[] ->
                                       XV_Bool
                                         (Prims.op_Negation
                                            (to_bool_val
                                               (eval_expr
                                                  (fuel - Prims.int_one) env
                                                  a)))
                                   | uu___15 -> XV_Bool true)
                                else
                                  if name = "true"
                                  then XV_Bool true
                                  else
                                    if name = "false"
                                    then XV_Bool false
                                    else
                                      if name = "boolean"
                                      then
                                        (match args with
                                         | a::[] ->
                                             XV_Bool
                                               (to_bool_val
                                                  (eval_expr
                                                     (fuel - Prims.int_one)
                                                     env a))
                                         | uu___18 -> XV_Bool false)
                                      else
                                        if name = "number"
                                        then
                                          (match args with
                                           | [] ->
                                               XV_Num
                                                 (to_number_val
                                                    (XV_Str
                                                       (item_string_value
                                                          env.env_item)))
                                           | a::uu___19 ->
                                               XV_Num
                                                 (to_number_val
                                                    (eval_expr
                                                       (fuel - Prims.int_one)
                                                       env a)))
                                        else
                                          if name = "sum"
                                          then
                                            (match args with
                                             | a::[] ->
                                                 (match eval_expr
                                                          (fuel -
                                                             Prims.int_one)
                                                          env a
                                                  with
                                                  | XV_Nodes items ->
                                                      XV_Num
                                                        (sum_items items)
                                                  | uu___20 ->
                                                      XV_Num
                                                        (XN_Finite
                                                           (Prims.int_zero,
                                                             Prims.int_zero)))
                                             | uu___20 ->
                                                 XV_Num
                                                   (XN_Finite
                                                      (Prims.int_zero,
                                                        Prims.int_zero)))
                                          else
                                            if name = "floor"
                                            then
                                              (match args with
                                               | a::[] ->
                                                   XV_Num
                                                     (xn_floor
                                                        (to_number_val
                                                           (eval_expr
                                                              (fuel -
                                                                 Prims.int_one)
                                                              env a)))
                                               | uu___21 -> XV_Num XN_NaN)
                                            else
                                              if name = "ceiling"
                                              then
                                                (match args with
                                                 | a::[] ->
                                                     XV_Num
                                                       (xn_ceiling
                                                          (to_number_val
                                                             (eval_expr
                                                                (fuel -
                                                                   Prims.int_one)
                                                                env a)))
                                                 | uu___22 -> XV_Num XN_NaN)
                                              else
                                                if name = "round"
                                                then
                                                  (match args with
                                                   | a::[] ->
                                                       XV_Num
                                                         (xn_round
                                                            (to_number_val
                                                               (eval_expr
                                                                  (fuel -
                                                                    Prims.int_one)
                                                                  env a)))
                                                   | uu___23 -> XV_Num XN_NaN)
                                                else XV_Str ""
let rec find_child_index (nodes : Parser_XML.xml_node Prims.list)
  (target : Parser_XML.xml_node) (i : Prims.nat) : Prims.nat=
  match nodes with
  | [] -> Prims.int_zero
  | x::rest ->
      if x = target
      then i
      else find_child_index rest target (i + Prims.int_one)
let rec path_of_chain (chain : Parser_XML.xml_node Prims.list) :
  Prims.int Prims.list=
  match chain with
  | [] -> []
  | uu___::[] -> []
  | parent::rest ->
      (match rest with
       | [] -> []
       | child::uu___ ->
           let i =
             find_child_index (Parser_XML.element_children parent) child
               Prims.int_zero in
           i :: (path_of_chain rest))
let compute_ctx_path (ancestors : Parser_XML.xml_node Prims.list)
  (ctx : Parser_XML.xml_node) : Prims.int Prims.list=
  path_of_chain
    (FStar_List_Tot_Base.append (FStar_List_Tot_Base.rev ancestors) [ctx])
let eval_xpath_from_root (root_node : Parser_XML.xml_node)
  (vars : (Prims.string * xp_value) Prims.list) (expr_text : Prims.string) :
  xp_value FStar_Pervasives_Native.option=
  match Parser_XPath.parse_xpath expr_text with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some e ->
      let fuel = initial_eval_fuel e (xml_node_count root_node) in
      let env =
        {
          env_item = (CI_Elem ([], [], root_node));
          env_pos = Prims.int_one;
          env_size = Prims.int_one;
          env_vars = vars
        } in
      FStar_Pervasives_Native.Some (eval_expr fuel env e)
let eval_xpath_from_item (ancestors : Parser_XML.xml_node Prims.list)
  (context_node : Parser_XML.xml_node)
  (vars : (Prims.string * xp_value) Prims.list) (expr_text : Prims.string) :
  xp_value FStar_Pervasives_Native.option=
  match Parser_XPath.parse_xpath expr_text with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some e ->
      let doc_nodes =
        (xml_node_count context_node) + (xml_nodes_count ancestors) in
      let fuel = initial_eval_fuel e doc_nodes in
      let env =
        {
          env_item =
            (CI_Elem
               ((compute_ctx_path ancestors context_node), ancestors,
                 context_node));
          env_pos = Prims.int_one;
          env_size = Prims.int_one;
          env_vars = vars
        } in
      FStar_Pervasives_Native.Some (eval_expr fuel env e)
