open Prims
type xp_axis =
  | Ax_Child 
  | Ax_Descendant 
  | Ax_DescendantOrSelf 
  | Ax_Parent 
  | Ax_Self 
  | Ax_Attribute 
  | Ax_Ancestor 
  | Ax_AncestorOrSelf 
  | Ax_Following 
  | Ax_Preceding 
  | Ax_FollowingSibling 
  | Ax_PrecedingSibling 
let uu___is_Ax_Child (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Child -> true | uu___ -> false
let uu___is_Ax_Descendant (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Descendant -> true | uu___ -> false
let uu___is_Ax_DescendantOrSelf (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_DescendantOrSelf -> true | uu___ -> false
let uu___is_Ax_Parent (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Parent -> true | uu___ -> false
let uu___is_Ax_Self (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Self -> true | uu___ -> false
let uu___is_Ax_Attribute (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Attribute -> true | uu___ -> false
let uu___is_Ax_Ancestor (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Ancestor -> true | uu___ -> false
let uu___is_Ax_AncestorOrSelf (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_AncestorOrSelf -> true | uu___ -> false
let uu___is_Ax_Following (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Following -> true | uu___ -> false
let uu___is_Ax_Preceding (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_Preceding -> true | uu___ -> false
let uu___is_Ax_FollowingSibling (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_FollowingSibling -> true | uu___ -> false
let uu___is_Ax_PrecedingSibling (projectee : xp_axis) : Prims.bool=
  match projectee with | Ax_PrecedingSibling -> true | uu___ -> false
type xp_nodetest =
  | NT_Name of Prims.string 
  | NT_Prefix of Prims.string 
  | NT_Any 
  | NT_Text 
  | NT_Comment 
  | NT_Node 
  | NT_PI of Prims.string FStar_Pervasives_Native.option 
let uu___is_NT_Name (projectee : xp_nodetest) : Prims.bool=
  match projectee with | NT_Name _0 -> true | uu___ -> false
let __proj__NT_Name__item___0 (projectee : xp_nodetest) : Prims.string=
  match projectee with | NT_Name _0 -> _0
let uu___is_NT_Prefix (projectee : xp_nodetest) : Prims.bool=
  match projectee with | NT_Prefix _0 -> true | uu___ -> false
let __proj__NT_Prefix__item___0 (projectee : xp_nodetest) : Prims.string=
  match projectee with | NT_Prefix _0 -> _0
let uu___is_NT_Any (projectee : xp_nodetest) : Prims.bool=
  match projectee with | NT_Any -> true | uu___ -> false
let uu___is_NT_Text (projectee : xp_nodetest) : Prims.bool=
  match projectee with | NT_Text -> true | uu___ -> false
let uu___is_NT_Comment (projectee : xp_nodetest) : Prims.bool=
  match projectee with | NT_Comment -> true | uu___ -> false
let uu___is_NT_Node (projectee : xp_nodetest) : Prims.bool=
  match projectee with | NT_Node -> true | uu___ -> false
let uu___is_NT_PI (projectee : xp_nodetest) : Prims.bool=
  match projectee with | NT_PI _0 -> true | uu___ -> false
let __proj__NT_PI__item___0 (projectee : xp_nodetest) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | NT_PI _0 -> _0
type xp_comp_op =
  | Cmp_Eq 
  | Cmp_Ne 
  | Cmp_Lt 
  | Cmp_Le 
  | Cmp_Gt 
  | Cmp_Ge 
let uu___is_Cmp_Eq (projectee : xp_comp_op) : Prims.bool=
  match projectee with | Cmp_Eq -> true | uu___ -> false
let uu___is_Cmp_Ne (projectee : xp_comp_op) : Prims.bool=
  match projectee with | Cmp_Ne -> true | uu___ -> false
let uu___is_Cmp_Lt (projectee : xp_comp_op) : Prims.bool=
  match projectee with | Cmp_Lt -> true | uu___ -> false
let uu___is_Cmp_Le (projectee : xp_comp_op) : Prims.bool=
  match projectee with | Cmp_Le -> true | uu___ -> false
let uu___is_Cmp_Gt (projectee : xp_comp_op) : Prims.bool=
  match projectee with | Cmp_Gt -> true | uu___ -> false
let uu___is_Cmp_Ge (projectee : xp_comp_op) : Prims.bool=
  match projectee with | Cmp_Ge -> true | uu___ -> false
type xp_arith_op =
  | Ar_Add 
  | Ar_Sub 
  | Ar_Mul 
  | Ar_Div 
  | Ar_Mod 
let uu___is_Ar_Add (projectee : xp_arith_op) : Prims.bool=
  match projectee with | Ar_Add -> true | uu___ -> false
let uu___is_Ar_Sub (projectee : xp_arith_op) : Prims.bool=
  match projectee with | Ar_Sub -> true | uu___ -> false
let uu___is_Ar_Mul (projectee : xp_arith_op) : Prims.bool=
  match projectee with | Ar_Mul -> true | uu___ -> false
let uu___is_Ar_Div (projectee : xp_arith_op) : Prims.bool=
  match projectee with | Ar_Div -> true | uu___ -> false
let uu___is_Ar_Mod (projectee : xp_arith_op) : Prims.bool=
  match projectee with | Ar_Mod -> true | uu___ -> false
type xp_step =
  {
  step_axis: xp_axis ;
  step_test: xp_nodetest ;
  step_preds: xp_expr Prims.list }
and xp_expr =
  | XE_Path of Prims.bool * xp_step Prims.list 
  | XE_FilterPath of xp_expr * xp_expr Prims.list * xp_step Prims.list 
  | XE_Union of xp_expr * xp_expr 
  | XE_Or of xp_expr * xp_expr 
  | XE_And of xp_expr * xp_expr 
  | XE_Compare of xp_comp_op * xp_expr * xp_expr 
  | XE_Arith of xp_arith_op * xp_expr * xp_expr 
  | XE_Neg of xp_expr 
  | XE_Number of Prims.int * Prims.nat 
  | XE_Literal of Prims.string 
  | XE_VarRef of Prims.string 
  | XE_FunCall of Prims.string * xp_expr Prims.list 
let __proj__Mkxp_step__item__step_axis (projectee : xp_step) : xp_axis=
  match projectee with | { step_axis; step_test; step_preds;_} -> step_axis
let __proj__Mkxp_step__item__step_test (projectee : xp_step) : xp_nodetest=
  match projectee with | { step_axis; step_test; step_preds;_} -> step_test
let __proj__Mkxp_step__item__step_preds (projectee : xp_step) :
  xp_expr Prims.list=
  match projectee with | { step_axis; step_test; step_preds;_} -> step_preds
let uu___is_XE_Path (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Path (absolute, steps) -> true | uu___ -> false
let __proj__XE_Path__item__absolute (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Path (absolute, steps) -> absolute
let __proj__XE_Path__item__steps (projectee : xp_expr) : xp_step Prims.list=
  match projectee with | XE_Path (absolute, steps) -> steps
let uu___is_XE_FilterPath (projectee : xp_expr) : Prims.bool=
  match projectee with
  | XE_FilterPath (primary, preds, steps) -> true
  | uu___ -> false
let __proj__XE_FilterPath__item__primary (projectee : xp_expr) : xp_expr=
  match projectee with | XE_FilterPath (primary, preds, steps) -> primary
let __proj__XE_FilterPath__item__preds (projectee : xp_expr) :
  xp_expr Prims.list=
  match projectee with | XE_FilterPath (primary, preds, steps) -> preds
let __proj__XE_FilterPath__item__steps (projectee : xp_expr) :
  xp_step Prims.list=
  match projectee with | XE_FilterPath (primary, preds, steps) -> steps
let uu___is_XE_Union (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Union (_0, _1) -> true | uu___ -> false
let __proj__XE_Union__item___0 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Union (_0, _1) -> _0
let __proj__XE_Union__item___1 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Union (_0, _1) -> _1
let uu___is_XE_Or (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Or (_0, _1) -> true | uu___ -> false
let __proj__XE_Or__item___0 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Or (_0, _1) -> _0
let __proj__XE_Or__item___1 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Or (_0, _1) -> _1
let uu___is_XE_And (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_And (_0, _1) -> true | uu___ -> false
let __proj__XE_And__item___0 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_And (_0, _1) -> _0
let __proj__XE_And__item___1 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_And (_0, _1) -> _1
let uu___is_XE_Compare (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Compare (_0, _1, _2) -> true | uu___ -> false
let __proj__XE_Compare__item___0 (projectee : xp_expr) : xp_comp_op=
  match projectee with | XE_Compare (_0, _1, _2) -> _0
let __proj__XE_Compare__item___1 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Compare (_0, _1, _2) -> _1
let __proj__XE_Compare__item___2 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Compare (_0, _1, _2) -> _2
let uu___is_XE_Arith (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Arith (_0, _1, _2) -> true | uu___ -> false
let __proj__XE_Arith__item___0 (projectee : xp_expr) : xp_arith_op=
  match projectee with | XE_Arith (_0, _1, _2) -> _0
let __proj__XE_Arith__item___1 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Arith (_0, _1, _2) -> _1
let __proj__XE_Arith__item___2 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Arith (_0, _1, _2) -> _2
let uu___is_XE_Neg (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Neg _0 -> true | uu___ -> false
let __proj__XE_Neg__item___0 (projectee : xp_expr) : xp_expr=
  match projectee with | XE_Neg _0 -> _0
let uu___is_XE_Number (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Number (_0, _1) -> true | uu___ -> false
let __proj__XE_Number__item___0 (projectee : xp_expr) : Prims.int=
  match projectee with | XE_Number (_0, _1) -> _0
let __proj__XE_Number__item___1 (projectee : xp_expr) : Prims.nat=
  match projectee with | XE_Number (_0, _1) -> _1
let uu___is_XE_Literal (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_Literal _0 -> true | uu___ -> false
let __proj__XE_Literal__item___0 (projectee : xp_expr) : Prims.string=
  match projectee with | XE_Literal _0 -> _0
let uu___is_XE_VarRef (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_VarRef _0 -> true | uu___ -> false
let __proj__XE_VarRef__item___0 (projectee : xp_expr) : Prims.string=
  match projectee with | XE_VarRef _0 -> _0
let uu___is_XE_FunCall (projectee : xp_expr) : Prims.bool=
  match projectee with | XE_FunCall (_0, _1) -> true | uu___ -> false
let __proj__XE_FunCall__item___0 (projectee : xp_expr) : Prims.string=
  match projectee with | XE_FunCall (_0, _1) -> _0
let __proj__XE_FunCall__item___1 (projectee : xp_expr) : xp_expr Prims.list=
  match projectee with | XE_FunCall (_0, _1) -> _1
let is_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let is_digit_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let is_name_start_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  if code < (Prims.of_int (0x80))
  then
    (((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
       ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
      || (code = (Prims.of_int (0x5F)))
  else code >= (Prims.of_int (0xC0))
let is_name_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  if code < (Prims.of_int (0x80))
  then
    ((((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A))))
          ||
          ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
         ||
         ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
        || (code = (Prims.of_int (0x5F))))
       || (code = (Prims.of_int (0x2D))))
      || (code = (Prims.of_int (0x2E)))
  else code >= (Prims.of_int (0xC0))
let skip_ws (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  match Parser_Combinators.ptake_while_pos is_ws input pos with
  | Parser_Combinators.ParseOk (uu___, pos') -> pos'
  | Parser_Combinators.ParseFail (uu___, fpos) -> fpos
let peek_char (input : Prims.string) (pos : Prims.nat) :
  FStar_Char.char FStar_Pervasives_Native.option=
  if pos < (Parser_FastString.fs_byte_length input)
  then
    FStar_Pervasives_Native.Some (Parser_FastString.fs_byte_index input pos)
  else FStar_Pervasives_Native.None
let word_boundary_after (input : Prims.string) (pos : Prims.nat) :
  Prims.bool=
  match peek_char input pos with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some c -> Prims.op_Negation (is_name_char c)
let match_keyword (kw : Prims.string) (input : Prims.string)
  (pos : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match Parser_Combinators.pstring kw input pos with
  | Parser_Combinators.ParseOk (uu___, pos') ->
      if word_boundary_after input pos'
      then FStar_Pervasives_Native.Some pos'
      else FStar_Pervasives_Native.None
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let parse_ncname (input : Prims.string) (pos : Prims.nat) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  match peek_char input pos with
  | FStar_Pervasives_Native.Some c ->
      if is_name_start_char c
      then
        (match Parser_Combinators.ptake_while_pos is_name_char input
                 (pos + Prims.int_one)
         with
         | Parser_Combinators.ParseOk (rest, pos') ->
             FStar_Pervasives_Native.Some
               ((FStar_String.concat "" [FStar_String.string_of_char c; rest]),
                 pos')
         | Parser_Combinators.ParseFail (uu___, uu___1) ->
             FStar_Pervasives_Native.Some
               ((FStar_String.string_of_char c), (pos + Prims.int_one)))
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec pow10_nat (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10_nat (n - Prims.int_one))
let rec digits_to_nat (input : Prims.string) (pos : Prims.nat)
  (endpos : Prims.nat) (acc : Prims.nat) : Prims.nat=
  if pos >= endpos
  then acc
  else
    (let c = Parser_FastString.fs_byte_index input pos in
     let d = (FStar_Char.int_of_char c) - (Prims.of_int (0x30)) in
     let d' = if d < Prims.int_zero then Prims.int_zero else d in
     digits_to_nat input (pos + Prims.int_one) endpos
       ((acc * (Prims.of_int (10))) + d'))
let initial_parse_fuel (input : Prims.string) : Prims.nat=
  ((Prims.of_int (4)) *
     ((Parser_FastString.fs_byte_length input) + Prims.int_one))
    + (Prims.of_int (64))
let parse_number_lit (input : Prims.string) (pos : Prims.nat) :
  (Prims.int * Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  let has_int_digit =
    match peek_char input pos with
    | FStar_Pervasives_Native.Some c -> is_digit_char c
    | FStar_Pervasives_Native.None -> false in
  let starts_dot =
    match peek_char input pos with
    | FStar_Pervasives_Native.Some c -> c = 46
    | FStar_Pervasives_Native.None -> false in
  if (Prims.op_Negation has_int_digit) && (Prims.op_Negation starts_dot)
  then FStar_Pervasives_Native.None
  else
    (let int_end =
       Parser_Combinators.ptake_while_scan is_digit_char input pos
         ((len - pos) + Prims.int_one) in
     let int_val = digits_to_nat input pos int_end Prims.int_zero in
     if
       (int_end < len) &&
         ((Parser_FastString.fs_byte_index input int_end) = 46)
     then
       let frac_start = int_end + Prims.int_one in
       let frac_end =
         Parser_Combinators.ptake_while_scan is_digit_char input frac_start
           ((len - frac_start) + Prims.int_one) in
       let scale = frac_end - frac_start in
       (if scale = Prims.int_zero
        then FStar_Pervasives_Native.Some (int_val, Prims.int_zero, frac_end)
        else
          (let frac_val =
             digits_to_nat input frac_start frac_end Prims.int_zero in
           FStar_Pervasives_Native.Some
             (((int_val * (pow10_nat scale)) + frac_val), scale, frac_end)))
     else
       if int_end = pos
       then FStar_Pervasives_Native.None
       else FStar_Pervasives_Native.Some (int_val, Prims.int_zero, int_end))
let parse_string_lit (input : Prims.string) (pos : Prims.nat) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  match peek_char input pos with
  | FStar_Pervasives_Native.Some q ->
      if (q = 34) || (q = 39)
      then
        let len = Parser_FastString.fs_byte_length input in
        let body_end =
          Parser_FastString.fs_find_byte input (FStar_Char.int_of_char q)
            (pos + Prims.int_one) in
        (if (body_end < len) && (body_end >= (pos + Prims.int_one))
         then
           FStar_Pervasives_Native.Some
             ((Parser_FastString.fs_byte_sub input (pos + Prims.int_one)
                 ((body_end - pos) - Prims.int_one)),
               (body_end + Prims.int_one))
         else FStar_Pervasives_Native.None)
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let axis_of_name (name : Prims.string) :
  xp_axis FStar_Pervasives_Native.option=
  if name = "child"
  then FStar_Pervasives_Native.Some Ax_Child
  else
    if name = "descendant"
    then FStar_Pervasives_Native.Some Ax_Descendant
    else
      if name = "descendant-or-self"
      then FStar_Pervasives_Native.Some Ax_DescendantOrSelf
      else
        if name = "parent"
        then FStar_Pervasives_Native.Some Ax_Parent
        else
          if name = "self"
          then FStar_Pervasives_Native.Some Ax_Self
          else
            if name = "attribute"
            then FStar_Pervasives_Native.Some Ax_Attribute
            else
              if name = "ancestor"
              then FStar_Pervasives_Native.Some Ax_Ancestor
              else
                if name = "ancestor-or-self"
                then FStar_Pervasives_Native.Some Ax_AncestorOrSelf
                else
                  if name = "following"
                  then FStar_Pervasives_Native.Some Ax_Following
                  else
                    if name = "preceding"
                    then FStar_Pervasives_Native.Some Ax_Preceding
                    else
                      if name = "following-sibling"
                      then FStar_Pervasives_Native.Some Ax_FollowingSibling
                      else
                        if name = "preceding-sibling"
                        then FStar_Pervasives_Native.Some Ax_PrecedingSibling
                        else FStar_Pervasives_Native.None
let is_nodetype_keyword (name : Prims.string) : Prims.bool=
  (((name = "text") || (name = "comment")) || (name = "node")) ||
    (name = "processing-instruction")
let parse_node_test (input : Prims.string) (pos : Prims.nat) :
  (xp_nodetest * Prims.nat) FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  match peek_char input pos with
  | FStar_Pervasives_Native.Some 42 ->
      FStar_Pervasives_Native.Some (NT_Any, (pos + Prims.int_one))
  | uu___ ->
      (match parse_ncname input pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (nm, pos1) ->
           if
             (((pos1 < len) &&
                 ((Parser_FastString.fs_byte_index input pos1) = 58))
                && ((pos1 + Prims.int_one) < len))
               &&
               ((Parser_FastString.fs_byte_index input (pos1 + Prims.int_one))
                  = 42)
           then
             FStar_Pervasives_Native.Some
               ((NT_Prefix nm), (pos1 + (Prims.of_int (2))))
           else
             if
               (((pos1 < len) &&
                   ((Parser_FastString.fs_byte_index input pos1) = 58))
                  && ((pos1 + Prims.int_one) < len))
                 &&
                 (is_name_start_char
                    (Parser_FastString.fs_byte_index input
                       (pos1 + Prims.int_one)))
             then
               (match parse_ncname input (pos1 + Prims.int_one) with
                | FStar_Pervasives_Native.Some (local, pos2) ->
                    FStar_Pervasives_Native.Some
                      ((NT_Name (FStar_String.concat "" [nm; ":"; local])),
                        pos2)
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               (let posws = skip_ws input pos1 in
                if
                  ((posws < len) &&
                     ((Parser_FastString.fs_byte_index input posws) = 40))
                    && (is_nodetype_keyword nm)
                then
                  (if nm = "processing-instruction"
                   then
                     let posws2 = skip_ws input (posws + Prims.int_one) in
                     (if
                        (posws2 < len) &&
                          ((Parser_FastString.fs_byte_index input posws2) =
                             41)
                      then
                        FStar_Pervasives_Native.Some
                          ((NT_PI FStar_Pervasives_Native.None),
                            (posws2 + Prims.int_one))
                      else
                        (match parse_string_lit input posws2 with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some (lit, p) ->
                             let p2 = skip_ws input p in
                             if
                               (p2 < len) &&
                                 ((Parser_FastString.fs_byte_index input p2)
                                    = 41)
                             then
                               FStar_Pervasives_Native.Some
                                 ((NT_PI (FStar_Pervasives_Native.Some lit)),
                                   (p2 + Prims.int_one))
                             else FStar_Pervasives_Native.None))
                   else
                     (let posws2 = skip_ws input (posws + Prims.int_one) in
                      if
                        (posws2 < len) &&
                          ((Parser_FastString.fs_byte_index input posws2) =
                             41)
                      then
                        let test =
                          if nm = "text"
                          then NT_Text
                          else if nm = "comment" then NT_Comment else NT_Node in
                        FStar_Pervasives_Native.Some
                          (test, (posws2 + Prims.int_one))
                      else FStar_Pervasives_Native.None))
                else FStar_Pervasives_Native.Some ((NT_Name nm), pos1)))
let rec parse_or_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_and_expr input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (lhs, pos1) ->
         parse_or_rest input lhs pos1 (fuel - Prims.int_one))
and parse_or_rest (input : Prims.string) (lhs : xp_expr) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (lhs, pos)
  else
    (let pos1 = skip_ws input pos in
     match match_keyword "or" input pos1 with
     | FStar_Pervasives_Native.Some pos2 ->
         (match parse_and_expr input (skip_ws input pos2)
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (rhs, pos3) ->
              parse_or_rest input (XE_Or (lhs, rhs)) pos3
                (fuel - Prims.int_one))
     | FStar_Pervasives_Native.None -> Parser_Combinators.ParseOk (lhs, pos1))
and parse_and_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_equality_expr input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (lhs, pos1) ->
         parse_and_rest input lhs pos1 (fuel - Prims.int_one))
and parse_and_rest (input : Prims.string) (lhs : xp_expr) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (lhs, pos)
  else
    (let pos1 = skip_ws input pos in
     match match_keyword "and" input pos1 with
     | FStar_Pervasives_Native.Some pos2 ->
         (match parse_equality_expr input (skip_ws input pos2)
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (rhs, pos3) ->
              parse_and_rest input (XE_And (lhs, rhs)) pos3
                (fuel - Prims.int_one))
     | FStar_Pervasives_Native.None -> Parser_Combinators.ParseOk (lhs, pos1))
and parse_equality_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_relational_expr input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (lhs, pos1) ->
         parse_equality_rest input lhs pos1 (fuel - Prims.int_one))
and parse_equality_rest (input : Prims.string) (lhs : xp_expr)
  (pos : Prims.nat) (fuel : Prims.nat) :
  xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (lhs, pos)
  else
    (let pos1 = skip_ws input pos in
     let len = Parser_FastString.fs_byte_length input in
     if
       (((pos1 + Prims.int_one) < len) &&
          ((Parser_FastString.fs_byte_index input pos1) = 33))
         &&
         ((Parser_FastString.fs_byte_index input (pos1 + Prims.int_one)) = 61)
     then
       match parse_relational_expr input
               (skip_ws input (pos1 + (Prims.of_int (2))))
               (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (rhs, pos2) ->
           parse_equality_rest input (XE_Compare (Cmp_Ne, lhs, rhs)) pos2
             (fuel - Prims.int_one)
     else
       if (pos1 < len) && ((Parser_FastString.fs_byte_index input pos1) = 61)
       then
         (match parse_relational_expr input
                  (skip_ws input (pos1 + Prims.int_one))
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (rhs, pos2) ->
              parse_equality_rest input (XE_Compare (Cmp_Eq, lhs, rhs)) pos2
                (fuel - Prims.int_one))
       else Parser_Combinators.ParseOk (lhs, pos1))
and parse_relational_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_additive_expr input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (lhs, pos1) ->
         parse_relational_rest input lhs pos1 (fuel - Prims.int_one))
and parse_relational_rest (input : Prims.string) (lhs : xp_expr)
  (pos : Prims.nat) (fuel : Prims.nat) :
  xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (lhs, pos)
  else
    (let pos1 = skip_ws input pos in
     let len = Parser_FastString.fs_byte_length input in
     if
       (((pos1 + Prims.int_one) < len) &&
          ((Parser_FastString.fs_byte_index input pos1) = 60))
         &&
         ((Parser_FastString.fs_byte_index input (pos1 + Prims.int_one)) = 61)
     then
       match parse_additive_expr input
               (skip_ws input (pos1 + (Prims.of_int (2))))
               (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (rhs, pos2) ->
           parse_relational_rest input (XE_Compare (Cmp_Le, lhs, rhs)) pos2
             (fuel - Prims.int_one)
     else
       if
         (((pos1 + Prims.int_one) < len) &&
            ((Parser_FastString.fs_byte_index input pos1) = 62))
           &&
           ((Parser_FastString.fs_byte_index input (pos1 + Prims.int_one)) =
              61)
       then
         (match parse_additive_expr input
                  (skip_ws input (pos1 + (Prims.of_int (2))))
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (rhs, pos2) ->
              parse_relational_rest input (XE_Compare (Cmp_Ge, lhs, rhs))
                pos2 (fuel - Prims.int_one))
       else
         if
           (pos1 < len) &&
             ((Parser_FastString.fs_byte_index input pos1) = 60)
         then
           (match parse_additive_expr input
                    (skip_ws input (pos1 + Prims.int_one))
                    (fuel - Prims.int_one)
            with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (rhs, pos2) ->
                parse_relational_rest input (XE_Compare (Cmp_Lt, lhs, rhs))
                  pos2 (fuel - Prims.int_one))
         else
           if
             (pos1 < len) &&
               ((Parser_FastString.fs_byte_index input pos1) = 62)
           then
             (match parse_additive_expr input
                      (skip_ws input (pos1 + Prims.int_one))
                      (fuel - Prims.int_one)
              with
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos)
              | Parser_Combinators.ParseOk (rhs, pos2) ->
                  parse_relational_rest input (XE_Compare (Cmp_Gt, lhs, rhs))
                    pos2 (fuel - Prims.int_one))
           else Parser_Combinators.ParseOk (lhs, pos1))
and parse_additive_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_multiplicative_expr input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (lhs, pos1) ->
         parse_additive_rest input lhs pos1 (fuel - Prims.int_one))
and parse_additive_rest (input : Prims.string) (lhs : xp_expr)
  (pos : Prims.nat) (fuel : Prims.nat) :
  xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (lhs, pos)
  else
    (let pos1 = skip_ws input pos in
     let len = Parser_FastString.fs_byte_length input in
     if (pos1 < len) && ((Parser_FastString.fs_byte_index input pos1) = 43)
     then
       match parse_multiplicative_expr input
               (skip_ws input (pos1 + Prims.int_one)) (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (rhs, pos2) ->
           parse_additive_rest input (XE_Arith (Ar_Add, lhs, rhs)) pos2
             (fuel - Prims.int_one)
     else
       if (pos1 < len) && ((Parser_FastString.fs_byte_index input pos1) = 45)
       then
         (match parse_multiplicative_expr input
                  (skip_ws input (pos1 + Prims.int_one))
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (rhs, pos2) ->
              parse_additive_rest input (XE_Arith (Ar_Sub, lhs, rhs)) pos2
                (fuel - Prims.int_one))
       else Parser_Combinators.ParseOk (lhs, pos1))
and parse_multiplicative_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_unary_expr input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (lhs, pos1) ->
         parse_multiplicative_rest input lhs pos1 (fuel - Prims.int_one))
and parse_multiplicative_rest (input : Prims.string) (lhs : xp_expr)
  (pos : Prims.nat) (fuel : Prims.nat) :
  xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (lhs, pos)
  else
    (let pos1 = skip_ws input pos in
     let len = Parser_FastString.fs_byte_length input in
     if (pos1 < len) && ((Parser_FastString.fs_byte_index input pos1) = 42)
     then
       match parse_unary_expr input (skip_ws input (pos1 + Prims.int_one))
               (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (rhs, pos2) ->
           parse_multiplicative_rest input (XE_Arith (Ar_Mul, lhs, rhs)) pos2
             (fuel - Prims.int_one)
     else
       (match match_keyword "div" input pos1 with
        | FStar_Pervasives_Native.Some pos2 ->
            (match parse_unary_expr input (skip_ws input pos2)
                     (fuel - Prims.int_one)
             with
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos)
             | Parser_Combinators.ParseOk (rhs, pos3) ->
                 parse_multiplicative_rest input
                   (XE_Arith (Ar_Div, lhs, rhs)) pos3 (fuel - Prims.int_one))
        | FStar_Pervasives_Native.None ->
            (match match_keyword "mod" input pos1 with
             | FStar_Pervasives_Native.Some pos2 ->
                 (match parse_unary_expr input (skip_ws input pos2)
                          (fuel - Prims.int_one)
                  with
                  | Parser_Combinators.ParseFail (msg, fpos) ->
                      Parser_Combinators.ParseFail (msg, fpos)
                  | Parser_Combinators.ParseOk (rhs, pos3) ->
                      parse_multiplicative_rest input
                        (XE_Arith (Ar_Mod, lhs, rhs)) pos3
                        (fuel - Prims.int_one))
             | FStar_Pervasives_Native.None ->
                 Parser_Combinators.ParseOk (lhs, pos1))))
and parse_unary_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (let pos1 = skip_ws input pos in
     if
       (pos1 < (Parser_FastString.fs_byte_length input)) &&
         ((Parser_FastString.fs_byte_index input pos1) = 45)
     then
       match parse_unary_expr input (pos1 + Prims.int_one)
               (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (e, pos2) ->
           Parser_Combinators.ParseOk ((XE_Neg e), pos2)
     else parse_union_expr input pos1 (fuel - Prims.int_one))
and parse_union_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_path_expr input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (lhs, pos1) ->
         parse_union_rest input lhs pos1 (fuel - Prims.int_one))
and parse_union_rest (input : Prims.string) (lhs : xp_expr) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (lhs, pos)
  else
    (let pos1 = skip_ws input pos in
     if
       (pos1 < (Parser_FastString.fs_byte_length input)) &&
         ((Parser_FastString.fs_byte_index input pos1) = 124)
     then
       match parse_path_expr input (pos1 + Prims.int_one)
               (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (rhs, pos2) ->
           parse_union_rest input (XE_Union (lhs, rhs)) pos2
             (fuel - Prims.int_one)
     else Parser_Combinators.ParseOk (lhs, pos1))
and parse_path_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (let pos1 = skip_ws input pos in
     let len = Parser_FastString.fs_byte_length input in
     match peek_char input pos1 with
     | FStar_Pervasives_Native.None ->
         Parser_Combinators.ParseFail ("expected an expression", pos1)
     | FStar_Pervasives_Native.Some 47 ->
         parse_absolute_location_path input pos1 (fuel - Prims.int_one)
     | FStar_Pervasives_Native.Some 64 ->
         (match parse_node_test input (pos1 + Prims.int_one) with
          | FStar_Pervasives_Native.None ->
              Parser_Combinators.ParseFail
                ("expected node test after '@'", (pos1 + Prims.int_one))
          | FStar_Pervasives_Native.Some (test, pos2) ->
              (match parse_predicates input pos2 (fuel - Prims.int_one) with
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)
               | Parser_Combinators.ParseOk (preds, pos3) ->
                   let first =
                     {
                       step_axis = Ax_Attribute;
                       step_test = test;
                       step_preds = preds
                     } in
                   (match parse_location_path_rest input [first] pos3
                            (fuel - Prims.int_one)
                    with
                    | Parser_Combinators.ParseFail (msg, fpos) ->
                        Parser_Combinators.ParseFail (msg, fpos)
                    | Parser_Combinators.ParseOk (steps, pos4) ->
                        Parser_Combinators.ParseOk
                          ((XE_Path (false, steps)), pos4))))
     | FStar_Pervasives_Native.Some 42 ->
         (match parse_predicates input (pos1 + Prims.int_one)
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (preds, pos2) ->
              let first =
                {
                  step_axis = Ax_Child;
                  step_test = NT_Any;
                  step_preds = preds
                } in
              (match parse_location_path_rest input [first] pos2
                       (fuel - Prims.int_one)
               with
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)
               | Parser_Combinators.ParseOk (steps, pos3) ->
                   Parser_Combinators.ParseOk
                     ((XE_Path (false, steps)), pos3)))
     | FStar_Pervasives_Native.Some 46 ->
         if
           ((pos1 + Prims.int_one) < len) &&
             ((Parser_FastString.fs_byte_index input (pos1 + Prims.int_one))
                = 46)
         then
           (match parse_location_path_rest input
                    [{
                       step_axis = Ax_Parent;
                       step_test = NT_Node;
                       step_preds = []
                     }] (pos1 + (Prims.of_int (2))) (fuel - Prims.int_one)
            with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (steps, pos2) ->
                Parser_Combinators.ParseOk ((XE_Path (false, steps)), pos2))
         else
           if
             ((pos1 + Prims.int_one) < len) &&
               (is_digit_char
                  (Parser_FastString.fs_byte_index input
                     (pos1 + Prims.int_one)))
           then
             (match parse_primary_expr input pos1 (fuel - Prims.int_one) with
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos)
              | Parser_Combinators.ParseOk (e, pos2) ->
                  parse_filter_suffix input e pos2 (fuel - Prims.int_one))
           else
             (match parse_location_path_rest input
                      [{
                         step_axis = Ax_Self;
                         step_test = NT_Node;
                         step_preds = []
                       }] (pos1 + Prims.int_one) (fuel - Prims.int_one)
              with
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos)
              | Parser_Combinators.ParseOk (steps, pos2) ->
                  Parser_Combinators.ParseOk ((XE_Path (false, steps)), pos2))
     | FStar_Pervasives_Native.Some c ->
         if is_name_start_char c
         then parse_name_lead input pos1 (fuel - Prims.int_one)
         else
           (match parse_primary_expr input pos1 (fuel - Prims.int_one) with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (e, pos2) ->
                parse_filter_suffix input e pos2 (fuel - Prims.int_one)))
and parse_name_lead (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_ncname input pos with
     | FStar_Pervasives_Native.None ->
         Parser_Combinators.ParseFail ("expected a name", pos)
     | FStar_Pervasives_Native.Some (nm, pos1) ->
         let len = Parser_FastString.fs_byte_length input in
         if
           (((pos1 + Prims.int_one) < len) &&
              ((Parser_FastString.fs_byte_index input pos1) = 58))
             &&
             ((Parser_FastString.fs_byte_index input (pos1 + Prims.int_one))
                = 58)
         then
           (match axis_of_name nm with
            | FStar_Pervasives_Native.None ->
                Parser_Combinators.ParseFail
                  ((FStar_String.concat ""
                      ["axis '"; nm; "' not supported (see Stage 1.5)"]),
                    pos)
            | FStar_Pervasives_Native.Some ax ->
                (match parse_node_test input (pos1 + (Prims.of_int (2))) with
                 | FStar_Pervasives_Native.None ->
                     Parser_Combinators.ParseFail
                       ("expected node test after axis '::'",
                         (pos1 + (Prims.of_int (2))))
                 | FStar_Pervasives_Native.Some (test, pos2) ->
                     (match parse_predicates input pos2
                              (fuel - Prims.int_one)
                      with
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos)
                      | Parser_Combinators.ParseOk (preds, pos3) ->
                          let first =
                            {
                              step_axis = ax;
                              step_test = test;
                              step_preds = preds
                            } in
                          (match parse_location_path_rest input [first] pos3
                                   (fuel - Prims.int_one)
                           with
                           | Parser_Combinators.ParseFail (msg, fpos) ->
                               Parser_Combinators.ParseFail (msg, fpos)
                           | Parser_Combinators.ParseOk (steps, pos4) ->
                               Parser_Combinators.ParseOk
                                 ((XE_Path (false, steps)), pos4)))))
         else
           (let has_qname_local =
              (((pos1 < len) &&
                  ((Parser_FastString.fs_byte_index input pos1) = 58))
                 && ((pos1 + Prims.int_one) < len))
                &&
                (((Parser_FastString.fs_byte_index input
                     (pos1 + Prims.int_one))
                    = 42)
                   ||
                   (is_name_start_char
                      (Parser_FastString.fs_byte_index input
                         (pos1 + Prims.int_one)))) in
            if has_qname_local
            then
              match parse_node_test input pos with
              | FStar_Pervasives_Native.None ->
                  Parser_Combinators.ParseFail ("expected a node test", pos)
              | FStar_Pervasives_Native.Some (test, pos1') ->
                  (match parse_predicates input pos1' (fuel - Prims.int_one)
                   with
                   | Parser_Combinators.ParseFail (msg, fpos) ->
                       Parser_Combinators.ParseFail (msg, fpos)
                   | Parser_Combinators.ParseOk (preds, pos2) ->
                       let first =
                         {
                           step_axis = Ax_Child;
                           step_test = test;
                           step_preds = preds
                         } in
                       (match parse_location_path_rest input [first] pos2
                                (fuel - Prims.int_one)
                        with
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos)
                        | Parser_Combinators.ParseOk (steps, pos3) ->
                            Parser_Combinators.ParseOk
                              ((XE_Path (false, steps)), pos3)))
            else
              (let posws = skip_ws input pos1 in
               if
                 (posws < len) &&
                   ((Parser_FastString.fs_byte_index input posws) = 40)
               then
                 (if is_nodetype_keyword nm
                  then
                    match parse_node_test input pos with
                    | FStar_Pervasives_Native.None ->
                        Parser_Combinators.ParseFail
                          ("malformed node-type test", pos)
                    | FStar_Pervasives_Native.Some (test, pos1') ->
                        (match parse_predicates input pos1'
                                 (fuel - Prims.int_one)
                         with
                         | Parser_Combinators.ParseFail (msg, fpos) ->
                             Parser_Combinators.ParseFail (msg, fpos)
                         | Parser_Combinators.ParseOk (preds, pos2) ->
                             let first =
                               {
                                 step_axis = Ax_Child;
                                 step_test = test;
                                 step_preds = preds
                               } in
                             (match parse_location_path_rest input [first]
                                      pos2 (fuel - Prims.int_one)
                              with
                              | Parser_Combinators.ParseFail (msg, fpos) ->
                                  Parser_Combinators.ParseFail (msg, fpos)
                              | Parser_Combinators.ParseOk (steps, pos3) ->
                                  Parser_Combinators.ParseOk
                                    ((XE_Path (false, steps)), pos3)))
                  else
                    (match parse_function_args input
                             (skip_ws input (posws + Prims.int_one))
                             (fuel - Prims.int_one)
                     with
                     | Parser_Combinators.ParseFail (msg, fpos) ->
                         Parser_Combinators.ParseFail (msg, fpos)
                     | Parser_Combinators.ParseOk (args, pos2) ->
                         parse_filter_suffix input (XE_FunCall (nm, args))
                           pos2 (fuel - Prims.int_one)))
               else
                 (match parse_predicates input pos1 (fuel - Prims.int_one)
                  with
                  | Parser_Combinators.ParseFail (msg, fpos) ->
                      Parser_Combinators.ParseFail (msg, fpos)
                  | Parser_Combinators.ParseOk (preds, pos2) ->
                      let first =
                        {
                          step_axis = Ax_Child;
                          step_test = (NT_Name nm);
                          step_preds = preds
                        } in
                      (match parse_location_path_rest input [first] pos2
                               (fuel - Prims.int_one)
                       with
                       | Parser_Combinators.ParseFail (msg, fpos) ->
                           Parser_Combinators.ParseFail (msg, fpos)
                       | Parser_Combinators.ParseOk (steps, pos3) ->
                           Parser_Combinators.ParseOk
                             ((XE_Path (false, steps)), pos3))))))
and parse_primary_expr (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     match peek_char input pos with
     | FStar_Pervasives_Native.Some 36 ->
         (match parse_ncname input (pos + Prims.int_one) with
          | FStar_Pervasives_Native.None ->
              Parser_Combinators.ParseFail
                ("expected variable name after '$'", (pos + Prims.int_one))
          | FStar_Pervasives_Native.Some (nm, pos1) ->
              if
                (((pos1 < len) &&
                    ((Parser_FastString.fs_byte_index input pos1) = 58))
                   && ((pos1 + Prims.int_one) < len))
                  &&
                  (is_name_start_char
                     (Parser_FastString.fs_byte_index input
                        (pos1 + Prims.int_one)))
              then
                (match parse_ncname input (pos1 + Prims.int_one) with
                 | FStar_Pervasives_Native.Some (local, pos2) ->
                     Parser_Combinators.ParseOk
                       ((XE_VarRef (FStar_String.concat "" [nm; ":"; local])),
                         pos2)
                 | FStar_Pervasives_Native.None ->
                     Parser_Combinators.ParseOk ((XE_VarRef nm), pos1))
              else Parser_Combinators.ParseOk ((XE_VarRef nm), pos1))
     | FStar_Pervasives_Native.Some 40 ->
         (match parse_or_expr input (skip_ws input (pos + Prims.int_one))
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (e, pos1) ->
              let pos2 = skip_ws input pos1 in
              if
                (pos2 < len) &&
                  ((Parser_FastString.fs_byte_index input pos2) = 41)
              then Parser_Combinators.ParseOk (e, (pos2 + Prims.int_one))
              else Parser_Combinators.ParseFail ("expected ')'", pos2))
     | FStar_Pervasives_Native.Some c ->
         if (c = 34) || (c = 39)
         then
           (match parse_string_lit input pos with
            | FStar_Pervasives_Native.Some (s, pos1) ->
                Parser_Combinators.ParseOk ((XE_Literal s), pos1)
            | FStar_Pervasives_Native.None ->
                Parser_Combinators.ParseFail
                  ("unterminated string literal", pos))
         else
           (match parse_number_lit input pos with
            | FStar_Pervasives_Native.Some (v, scale, pos1) ->
                Parser_Combinators.ParseOk ((XE_Number (v, scale)), pos1)
            | FStar_Pervasives_Native.None ->
                Parser_Combinators.ParseFail ("expected an expression", pos))
     | uu___1 ->
         (match parse_number_lit input pos with
          | FStar_Pervasives_Native.Some (v, scale, pos1) ->
              Parser_Combinators.ParseOk ((XE_Number (v, scale)), pos1)
          | FStar_Pervasives_Native.None ->
              Parser_Combinators.ParseFail ("expected an expression", pos)))
and parse_filter_suffix (input : Prims.string) (primary : xp_expr)
  (pos : Prims.nat) (fuel : Prims.nat) :
  xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk (primary, pos)
  else
    (match parse_predicates input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (preds, pos1) ->
         let len = Parser_FastString.fs_byte_length input in
         let pos2 = skip_ws input pos1 in
         if
           (pos2 < len) &&
             ((Parser_FastString.fs_byte_index input pos2) = 47)
         then
           (if
              ((pos2 + Prims.int_one) < len) &&
                ((Parser_FastString.fs_byte_index input
                    (pos2 + Prims.int_one))
                   = 47)
            then
              let dstep =
                {
                  step_axis = Ax_DescendantOrSelf;
                  step_test = NT_Node;
                  step_preds = []
                } in
              match parse_relative_location_path input
                      (pos2 + (Prims.of_int (2))) (fuel - Prims.int_one)
              with
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos)
              | Parser_Combinators.ParseOk (steps, pos3) ->
                  Parser_Combinators.ParseOk
                    ((XE_FilterPath (primary, preds, (dstep :: steps))),
                      pos3)
            else
              (match parse_relative_location_path input
                       (pos2 + Prims.int_one) (fuel - Prims.int_one)
               with
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)
               | Parser_Combinators.ParseOk (steps, pos3) ->
                   Parser_Combinators.ParseOk
                     ((XE_FilterPath (primary, preds, steps)), pos3)))
         else
           if Prims.uu___is_Nil preds
           then Parser_Combinators.ParseOk (primary, pos1)
           else
             Parser_Combinators.ParseOk
               ((XE_FilterPath (primary, preds, [])), pos1))
and parse_absolute_location_path (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if
       ((pos + Prims.int_one) < len) &&
         ((Parser_FastString.fs_byte_index input (pos + Prims.int_one)) = 47)
     then
       let dstep =
         {
           step_axis = Ax_DescendantOrSelf;
           step_test = NT_Node;
           step_preds = []
         } in
       match parse_relative_location_path input (pos + (Prims.of_int (2)))
               (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (steps, pos1) ->
           Parser_Combinators.ParseOk
             ((XE_Path (true, (dstep :: steps))), pos1)
     else
       (let pos1 = pos + Prims.int_one in
        let looks_like_step =
          match peek_char input pos1 with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some c ->
              (((c = 64) || (c = 46)) || (c = 42)) || (is_name_start_char c) in
        if looks_like_step
        then
          match parse_relative_location_path input pos1
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (steps, pos2) ->
              Parser_Combinators.ParseOk ((XE_Path (true, steps)), pos2)
        else Parser_Combinators.ParseOk ((XE_Path (true, [])), pos1)))
and parse_relative_location_path (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_step Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (match parse_step input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (s, pos1) ->
         parse_location_path_rest input [s] pos1 (fuel - Prims.int_one))
and parse_location_path_rest (input : Prims.string)
  (acc : xp_step Prims.list) (pos : Prims.nat) (fuel : Prims.nat) :
  xp_step Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     let pos1 = skip_ws input pos in
     if (pos1 < len) && ((Parser_FastString.fs_byte_index input pos1) = 47)
     then
       (if
          ((pos1 + Prims.int_one) < len) &&
            ((Parser_FastString.fs_byte_index input (pos1 + Prims.int_one)) =
               47)
        then
          let dstep =
            {
              step_axis = Ax_DescendantOrSelf;
              step_test = NT_Node;
              step_preds = []
            } in
          match parse_step input (pos1 + (Prims.of_int (2)))
                  (fuel - Prims.int_one)
          with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (s, pos2) ->
              parse_location_path_rest input (s :: dstep :: acc) pos2
                (fuel - Prims.int_one)
        else
          (match parse_step input (pos1 + Prims.int_one)
                   (fuel - Prims.int_one)
           with
           | Parser_Combinators.ParseFail (msg, fpos) ->
               Parser_Combinators.ParseFail (msg, fpos)
           | Parser_Combinators.ParseOk (s, pos2) ->
               parse_location_path_rest input (s :: acc) pos2
                 (fuel - Prims.int_one)))
     else Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos1))
and parse_step (input : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) :
  xp_step Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     match peek_char input pos with
     | FStar_Pervasives_Native.Some 46 ->
         if
           ((pos + Prims.int_one) < len) &&
             ((Parser_FastString.fs_byte_index input (pos + Prims.int_one)) =
                46)
         then
           Parser_Combinators.ParseOk
             ({ step_axis = Ax_Parent; step_test = NT_Node; step_preds = [] },
               (pos + (Prims.of_int (2))))
         else
           Parser_Combinators.ParseOk
             ({ step_axis = Ax_Self; step_test = NT_Node; step_preds = [] },
               (pos + Prims.int_one))
     | FStar_Pervasives_Native.Some 64 ->
         (match parse_node_test input (pos + Prims.int_one) with
          | FStar_Pervasives_Native.None ->
              Parser_Combinators.ParseFail
                ("expected node test after '@'", (pos + Prims.int_one))
          | FStar_Pervasives_Native.Some (test, pos1) ->
              (match parse_predicates input pos1 (fuel - Prims.int_one) with
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)
               | Parser_Combinators.ParseOk (preds, pos2) ->
                   Parser_Combinators.ParseOk
                     ({
                        step_axis = Ax_Attribute;
                        step_test = test;
                        step_preds = preds
                      }, pos2)))
     | uu___1 ->
         let is_axis_lead =
           match parse_ncname input pos with
           | FStar_Pervasives_Native.Some (uu___2, pos1) ->
               (((pos1 + Prims.int_one) < len) &&
                  ((Parser_FastString.fs_byte_index input pos1) = 58))
                 &&
                 ((Parser_FastString.fs_byte_index input
                     (pos1 + Prims.int_one))
                    = 58)
           | FStar_Pervasives_Native.None -> false in
         if is_axis_lead
         then
           (match parse_ncname input pos with
            | FStar_Pervasives_Native.None ->
                Parser_Combinators.ParseFail ("expected a step", pos)
            | FStar_Pervasives_Native.Some (nm, pos1) ->
                (match axis_of_name nm with
                 | FStar_Pervasives_Native.None ->
                     Parser_Combinators.ParseFail
                       ((FStar_String.concat ""
                           ["axis '"; nm; "' not supported (see Stage 1.5)"]),
                         pos)
                 | FStar_Pervasives_Native.Some ax ->
                     (match parse_node_test input (pos1 + (Prims.of_int (2)))
                      with
                      | FStar_Pervasives_Native.None ->
                          Parser_Combinators.ParseFail
                            ("expected node test after axis '::'",
                              (pos1 + (Prims.of_int (2))))
                      | FStar_Pervasives_Native.Some (test, pos2) ->
                          (match parse_predicates input pos2
                                   (fuel - Prims.int_one)
                           with
                           | Parser_Combinators.ParseFail (msg, fpos) ->
                               Parser_Combinators.ParseFail (msg, fpos)
                           | Parser_Combinators.ParseOk (preds, pos3) ->
                               Parser_Combinators.ParseOk
                                 ({
                                    step_axis = ax;
                                    step_test = test;
                                    step_preds = preds
                                  }, pos3)))))
         else
           (match parse_node_test input pos with
            | FStar_Pervasives_Native.None ->
                Parser_Combinators.ParseFail ("expected a step", pos)
            | FStar_Pervasives_Native.Some (test, pos1) ->
                (match parse_predicates input pos1 (fuel - Prims.int_one)
                 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk (preds, pos2) ->
                     Parser_Combinators.ParseOk
                       ({
                          step_axis = Ax_Child;
                          step_test = test;
                          step_preds = preds
                        }, pos2))))
and parse_predicates (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ([], pos)
  else
    (let pos1 = skip_ws input pos in
     if
       (pos1 < (Parser_FastString.fs_byte_length input)) &&
         ((Parser_FastString.fs_byte_index input pos1) = 91)
     then
       match parse_or_expr input (skip_ws input (pos1 + Prims.int_one))
               (fuel - Prims.int_one)
       with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (pred, pos2) ->
           let pos3 = skip_ws input pos2 in
           (if
              (pos3 < (Parser_FastString.fs_byte_length input)) &&
                ((Parser_FastString.fs_byte_index input pos3) = 93)
            then
              match parse_predicates input (pos3 + Prims.int_one)
                      (fuel - Prims.int_one)
              with
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos)
              | Parser_Combinators.ParseOk (rest, pos4) ->
                  Parser_Combinators.ParseOk ((pred :: rest), pos4)
            else Parser_Combinators.ParseFail ("expected ']'", pos3))
     else Parser_Combinators.ParseOk ([], pos1))
and parse_function_args (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xp_expr Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("expression too complex (out of fuel)", pos)
  else
    (let pos1 = skip_ws input pos in
     if
       (pos1 < (Parser_FastString.fs_byte_length input)) &&
         ((Parser_FastString.fs_byte_index input pos1) = 41)
     then Parser_Combinators.ParseOk ([], (pos1 + Prims.int_one))
     else
       (match parse_or_expr input pos1 (fuel - Prims.int_one) with
        | Parser_Combinators.ParseFail (msg, fpos) ->
            Parser_Combinators.ParseFail (msg, fpos)
        | Parser_Combinators.ParseOk (a, pos2) ->
            let pos3 = skip_ws input pos2 in
            if
              (pos3 < (Parser_FastString.fs_byte_length input)) &&
                ((Parser_FastString.fs_byte_index input pos3) = 44)
            then
              (match parse_function_args input
                       (skip_ws input (pos3 + Prims.int_one))
                       (fuel - Prims.int_one)
               with
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)
               | Parser_Combinators.ParseOk (rest, pos4) ->
                   Parser_Combinators.ParseOk ((a :: rest), pos4))
            else
              if
                (pos3 < (Parser_FastString.fs_byte_length input)) &&
                  ((Parser_FastString.fs_byte_index input pos3) = 41)
              then Parser_Combinators.ParseOk ([a], (pos3 + Prims.int_one))
              else Parser_Combinators.ParseFail ("expected ',' or ')'", pos3)))
let parse_xpath (input : Prims.string) :
  xp_expr FStar_Pervasives_Native.option=
  let fuel = initial_parse_fuel input in
  match parse_or_expr input Prims.int_zero fuel with
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
  | Parser_Combinators.ParseOk (e, pos) ->
      let pos' = skip_ws input pos in
      if pos' = (Parser_FastString.fs_byte_length input)
      then FStar_Pervasives_Native.Some e
      else FStar_Pervasives_Native.None
