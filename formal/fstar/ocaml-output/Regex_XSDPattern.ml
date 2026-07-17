open Prims
let cp_lparen : Prims.nat= (Prims.of_int (0x28))
let cp_rparen : Prims.nat= (Prims.of_int (0x29))
let cp_lbracket : Prims.nat= (Prims.of_int (0x5B))
let cp_rbracket : Prims.nat= (Prims.of_int (0x5D))
let cp_lbrace : Prims.nat= (Prims.of_int (0x7B))
let cp_rbrace : Prims.nat= (Prims.of_int (0x7D))
let cp_pipe : Prims.nat= (Prims.of_int (0x7C))
let cp_star : Prims.nat= (Prims.of_int (0x2A))
let cp_plus : Prims.nat= (Prims.of_int (0x2B))
let cp_question : Prims.nat= (Prims.of_int (0x3F))
let cp_dot : Prims.nat= (Prims.of_int (0x2E))
let cp_caret : Prims.nat= (Prims.of_int (0x5E))
let cp_dollar : Prims.nat= (Prims.of_int (0x24))
let cp_backslash : Prims.nat= (Prims.of_int (0x5C))
let cp_hyphen : Prims.nat= (Prims.of_int (0x2D))
let cp_comma : Prims.nat= (Prims.of_int (0x2C))
let cp_colon : Prims.nat= (Prims.of_int (0x3A))
let cp_0 : Prims.nat= (Prims.of_int (0x30))
let cp_9 : Prims.nat= (Prims.of_int (0x39))
let cp_u : Prims.nat= (Prims.of_int (0x75))
let cp_U : Prims.nat= (Prims.of_int (0x55))
let single (c : Prims.nat) : Regex_Syntax.regex=
  Regex_Syntax.R_Ranges [(c, c)]
let dot_regex : Regex_Syntax.regex=
  Regex_Syntax.R_Ranges
    (Regex_Syntax.complement_ranges
       [((Prims.of_int (0x0A)), (Prims.of_int (0x0A)));
       ((Prims.of_int (0x0D)), (Prims.of_int (0x0D)))])
let hex_val (c : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if (c >= (Prims.of_int (0x30))) && (c <= (Prims.of_int (0x39)))
  then FStar_Pervasives_Native.Some (c - (Prims.of_int (0x30)))
  else
    if (c >= (Prims.of_int (0x61))) && (c <= (Prims.of_int (0x66)))
    then
      FStar_Pervasives_Native.Some
        ((c - (Prims.of_int (0x61))) + (Prims.of_int (10)))
    else
      if (c >= (Prims.of_int (0x41))) && (c <= (Prims.of_int (0x46)))
      then
        FStar_Pervasives_Native.Some
          ((c - (Prims.of_int (0x41))) + (Prims.of_int (10)))
      else FStar_Pervasives_Native.None
let rec read_hex_n (n : Prims.nat) (input : Prims.nat Prims.list)
  (acc : Prims.nat) :
  (Prims.nat * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  if n = Prims.int_zero
  then FStar_Pervasives_Native.Some (acc, input)
  else
    (match input with
     | [] -> FStar_Pervasives_Native.None
     | c::t ->
         (match hex_val c with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some v ->
              (match read_hex_n (n - Prims.int_one) t
                       ((acc * (Prims.of_int (16))) + v)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (res, rest) ->
                   FStar_Pervasives_Native.Some (res, rest))))
let char_escape (letter : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if letter = (Prims.of_int (0x6E))
  then FStar_Pervasives_Native.Some (Prims.of_int (0x0A))
  else
    if letter = (Prims.of_int (0x72))
    then FStar_Pervasives_Native.Some (Prims.of_int (0x0D))
    else
      if letter = (Prims.of_int (0x74))
      then FStar_Pervasives_Native.Some (Prims.of_int (0x09))
      else
        if letter = (Prims.of_int (0x66))
        then FStar_Pervasives_Native.Some (Prims.of_int (0x0C))
        else
          if letter = cp_backslash
          then FStar_Pervasives_Native.Some (Prims.of_int (0x5C))
          else
            if letter = cp_dot
            then FStar_Pervasives_Native.Some (Prims.of_int (0x2E))
            else
              if letter = cp_hyphen
              then FStar_Pervasives_Native.Some (Prims.of_int (0x2D))
              else
                if letter = (Prims.of_int (0x2F))
                then FStar_Pervasives_Native.Some (Prims.of_int (0x2F))
                else
                  if letter = cp_caret
                  then FStar_Pervasives_Native.Some (Prims.of_int (0x5E))
                  else
                    if letter = cp_dollar
                    then FStar_Pervasives_Native.Some (Prims.of_int (0x24))
                    else
                      if letter = cp_lparen
                      then FStar_Pervasives_Native.Some (Prims.of_int (0x28))
                      else
                        if letter = cp_rparen
                        then
                          FStar_Pervasives_Native.Some (Prims.of_int (0x29))
                        else
                          if letter = cp_lbracket
                          then
                            FStar_Pervasives_Native.Some
                              (Prims.of_int (0x5B))
                          else
                            if letter = cp_rbracket
                            then
                              FStar_Pervasives_Native.Some
                                (Prims.of_int (0x5D))
                            else
                              if letter = cp_lbrace
                              then
                                FStar_Pervasives_Native.Some
                                  (Prims.of_int (0x7B))
                              else
                                if letter = cp_rbrace
                                then
                                  FStar_Pervasives_Native.Some
                                    (Prims.of_int (0x7D))
                                else
                                  if letter = cp_pipe
                                  then
                                    FStar_Pervasives_Native.Some
                                      (Prims.of_int (0x7C))
                                  else
                                    if letter = cp_star
                                    then
                                      FStar_Pervasives_Native.Some
                                        (Prims.of_int (0x2A))
                                    else
                                      if letter = cp_plus
                                      then
                                        FStar_Pervasives_Native.Some
                                          (Prims.of_int (0x2B))
                                      else
                                        if letter = cp_question
                                        then
                                          FStar_Pervasives_Native.Some
                                            (Prims.of_int (0x3F))
                                        else FStar_Pervasives_Native.None
let class_escape_ranges (letter : Prims.nat) :
  (Prims.nat * Prims.nat) Prims.list FStar_Pervasives_Native.option=
  if letter = (Prims.of_int (0x64))
  then
    FStar_Pervasives_Native.Some
      [((Prims.of_int (0x30)), (Prims.of_int (0x39)))]
  else
    if letter = (Prims.of_int (0x44))
    then
      FStar_Pervasives_Native.Some
        (Regex_Syntax.complement_ranges
           [((Prims.of_int (0x30)), (Prims.of_int (0x39)))])
    else
      if letter = (Prims.of_int (0x73))
      then
        FStar_Pervasives_Native.Some
          [((Prims.of_int (0x09)), (Prims.of_int (0x0A)));
          ((Prims.of_int (0x0D)), (Prims.of_int (0x0D)));
          ((Prims.of_int (0x20)), (Prims.of_int (0x20)))]
      else
        if letter = (Prims.of_int (0x53))
        then
          FStar_Pervasives_Native.Some
            (Regex_Syntax.complement_ranges
               [((Prims.of_int (0x09)), (Prims.of_int (0x0A)));
               ((Prims.of_int (0x0D)), (Prims.of_int (0x0D)));
               ((Prims.of_int (0x20)), (Prims.of_int (0x20)))])
        else
          if letter = (Prims.of_int (0x77))
          then
            FStar_Pervasives_Native.Some
              [((Prims.of_int (0x30)), (Prims.of_int (0x39)));
              ((Prims.of_int (0x41)), (Prims.of_int (0x5A)));
              ((Prims.of_int (0x5F)), (Prims.of_int (0x5F)));
              ((Prims.of_int (0x61)), (Prims.of_int (0x7A)))]
          else
            if letter = (Prims.of_int (0x57))
            then
              FStar_Pervasives_Native.Some
                (Regex_Syntax.complement_ranges
                   [((Prims.of_int (0x30)), (Prims.of_int (0x39)));
                   ((Prims.of_int (0x41)), (Prims.of_int (0x5A)));
                   ((Prims.of_int (0x5F)), (Prims.of_int (0x5F)));
                   ((Prims.of_int (0x61)), (Prims.of_int (0x7A)))])
            else FStar_Pervasives_Native.None
let parse_escape_atom (letter : Prims.nat) (t2 : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  match class_escape_ranges letter with
  | FStar_Pervasives_Native.Some rs ->
      FStar_Pervasives_Native.Some ((Regex_Syntax.R_Ranges rs), t2)
  | FStar_Pervasives_Native.None ->
      if letter = cp_u
      then
        (match read_hex_n (Prims.of_int (4)) t2 Prims.int_zero with
         | FStar_Pervasives_Native.Some (cp, rest) ->
             if cp <= Regex_Syntax.max_codepoint
             then FStar_Pervasives_Native.Some ((single cp), rest)
             else FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        if letter = cp_U
        then
          (match read_hex_n (Prims.of_int (8)) t2 Prims.int_zero with
           | FStar_Pervasives_Native.Some (cp, rest) ->
               if cp <= Regex_Syntax.max_codepoint
               then FStar_Pervasives_Native.Some ((single cp), rest)
               else FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else
          (match char_escape letter with
           | FStar_Pervasives_Native.Some cp ->
               FStar_Pervasives_Native.Some ((single cp), t2)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let class_escape_item (letter : Prims.nat) (t2 : Prims.nat Prims.list) :
  ((Prims.nat * Prims.nat) Prims.list * Prims.nat Prims.list)
    FStar_Pervasives_Native.option=
  match class_escape_ranges letter with
  | FStar_Pervasives_Native.Some rs -> FStar_Pervasives_Native.Some (rs, t2)
  | FStar_Pervasives_Native.None ->
      if letter = cp_u
      then
        (match read_hex_n (Prims.of_int (4)) t2 Prims.int_zero with
         | FStar_Pervasives_Native.Some (cp, rest) ->
             if cp <= Regex_Syntax.max_codepoint
             then FStar_Pervasives_Native.Some ([(cp, cp)], rest)
             else FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        if letter = cp_U
        then
          (match read_hex_n (Prims.of_int (8)) t2 Prims.int_zero with
           | FStar_Pervasives_Native.Some (cp, rest) ->
               if cp <= Regex_Syntax.max_codepoint
               then FStar_Pervasives_Native.Some ([(cp, cp)], rest)
               else FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else
          (match char_escape letter with
           | FStar_Pervasives_Native.Some cp ->
               FStar_Pervasives_Native.Some ([(cp, cp)], t2)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec parse_class_items (input : Prims.nat Prims.list)
  (acc : (Prims.nat * Prims.nat) Prims.list) :
  ((Prims.nat * Prims.nat) Prims.list * Prims.nat Prims.list)
    FStar_Pervasives_Native.option=
  match input with
  | [] -> FStar_Pervasives_Native.None
  | h::t ->
      if h = cp_rbracket
      then FStar_Pervasives_Native.Some (acc, t)
      else
        if h = cp_backslash
        then
          (match t with
           | [] -> FStar_Pervasives_Native.None
           | letter::t2 ->
               (match class_escape_item letter t2 with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (rs, t3) ->
                    parse_class_items t3 (FStar_List_Tot_Base.append acc rs)))
        else
          (match t with
           | d::c2::t2 ->
               if
                 (((d = cp_hyphen) && (c2 <> cp_rbracket)) &&
                    (c2 <> cp_backslash))
                   && (h <= c2)
               then
                 parse_class_items t2
                   (FStar_List_Tot_Base.append acc [(h, c2)])
               else
                 parse_class_items t
                   (FStar_List_Tot_Base.append acc [(h, h)])
           | uu___2 ->
               parse_class_items t (FStar_List_Tot_Base.append acc [(h, h)]))
let rec insert_range (x : (Prims.nat * Prims.nat))
  (xs : (Prims.nat * Prims.nat) Prims.list) :
  (Prims.nat * Prims.nat) Prims.list=
  match xs with
  | [] -> [x]
  | y::t ->
      if (FStar_Pervasives_Native.fst x) <= (FStar_Pervasives_Native.fst y)
      then x :: xs
      else y :: (insert_range x t)
let rec sort_ranges (xs : (Prims.nat * Prims.nat) Prims.list) :
  (Prims.nat * Prims.nat) Prims.list=
  match xs with | [] -> [] | y::t -> insert_range y (sort_ranges t)
let parse_class (input : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  match input with
  | [] -> FStar_Pervasives_Native.None
  | h::t ->
      if h = cp_caret
      then
        (match parse_class_items t [] with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (ranges, rest) ->
             FStar_Pervasives_Native.Some
               ((Regex_Syntax.R_Ranges
                   (Regex_Syntax.complement_ranges (sort_ranges ranges))),
                 rest))
      else
        (match parse_class_items input [] with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (ranges, rest) ->
             FStar_Pervasives_Native.Some
               ((Regex_Syntax.R_Ranges ranges), rest))
let rec repeat_exact (r : Regex_Syntax.regex) (n : Prims.nat) :
  Regex_Syntax.regex=
  if n = Prims.int_zero
  then Regex_Syntax.R_Eps
  else Regex_Syntax.R_Cat (r, (repeat_exact r (n - Prims.int_one)))
let rec repeat_opt (r : Regex_Syntax.regex) (k : Prims.nat) :
  Regex_Syntax.regex=
  if k = Prims.int_zero
  then Regex_Syntax.R_Eps
  else
    Regex_Syntax.R_Cat
      ((Regex_Syntax.R_Alt (r, Regex_Syntax.R_Eps)),
        (repeat_opt r (k - Prims.int_one)))
let rec read_digits_acc (input : Prims.nat Prims.list) (acc : Prims.nat)
  (seen : Prims.bool) : (Prims.nat * Prims.nat Prims.list * Prims.bool)=
  match input with
  | c::t ->
      if (c >= cp_0) && (c <= cp_9)
      then read_digits_acc t ((acc * (Prims.of_int (10))) + (c - cp_0)) true
      else (acc, input, seen)
  | [] -> (acc, input, seen)
let read_uint (input : Prims.nat Prims.list) :
  (Prims.nat * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  let uu___ = read_digits_acc input Prims.int_zero false in
  match uu___ with
  | (v, rest, seen) ->
      if seen
      then FStar_Pervasives_Native.Some (v, rest)
      else FStar_Pervasives_Native.None
let parse_brace (r : Regex_Syntax.regex) (t : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  match read_uint t with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (n, t1) ->
      (match t1 with
       | c::t2 ->
           if c = cp_rbrace
           then FStar_Pervasives_Native.Some ((repeat_exact r n), t2)
           else
             if c = cp_comma
             then
               (match t2 with
                | c2::t3 ->
                    if c2 = cp_rbrace
                    then
                      FStar_Pervasives_Native.Some
                        ((Regex_Syntax.R_Cat
                            ((repeat_exact r n), (Regex_Syntax.R_Star r))),
                          t3)
                    else
                      (match read_uint t2 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some (m, t3') ->
                           (match t3' with
                            | c3::t4 ->
                                if (c3 = cp_rbrace) && (m >= n)
                                then
                                  FStar_Pervasives_Native.Some
                                    ((Regex_Syntax.R_Cat
                                        ((repeat_exact r n),
                                          (repeat_opt r (m - n)))), t4)
                                else FStar_Pervasives_Native.None
                            | [] -> FStar_Pervasives_Native.None))
                | [] -> FStar_Pervasives_Native.None)
             else FStar_Pervasives_Native.None
       | [] -> FStar_Pervasives_Native.None)
let skip_lazy (t : Prims.nat Prims.list) : Prims.nat Prims.list=
  match t with | c::t2 -> if c = cp_question then t2 else t | [] -> t
let parse_quant (r : Regex_Syntax.regex) (rest : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  match rest with
  | [] -> FStar_Pervasives_Native.Some (r, rest)
  | q::t ->
      if q = cp_star
      then
        FStar_Pervasives_Native.Some ((Regex_Syntax.R_Star r), (skip_lazy t))
      else
        if q = cp_plus
        then
          FStar_Pervasives_Native.Some
            ((Regex_Syntax.R_Cat (r, (Regex_Syntax.R_Star r))),
              (skip_lazy t))
        else
          if q = cp_question
          then
            FStar_Pervasives_Native.Some
              ((Regex_Syntax.R_Alt (r, Regex_Syntax.R_Eps)), (skip_lazy t))
          else
            if q = cp_lbrace
            then
              (match parse_brace r t with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (r', t') ->
                   FStar_Pervasives_Native.Some (r', (skip_lazy t')))
            else FStar_Pervasives_Native.Some (r, rest)
let is_atom_meta (h : Prims.nat) : Prims.bool=
  (((((((h = cp_star) || (h = cp_plus)) || (h = cp_question)) ||
        (h = cp_lbrace))
       || (h = cp_rbrace))
      || (h = cp_rbracket))
     || (h = cp_pipe))
    || (h = cp_rparen)
let rec parse_alt (fuel : Prims.nat) (input : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match parse_seq (fuel - Prims.int_one) input with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (r1, rest) ->
         (match rest with
          | c::t ->
              if c = cp_pipe
              then
                (match parse_alt (fuel - Prims.int_one) t with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (r2, rest2) ->
                     FStar_Pervasives_Native.Some
                       ((Regex_Syntax.R_Alt (r1, r2)), rest2))
              else FStar_Pervasives_Native.Some (r1, rest)
          | [] -> FStar_Pervasives_Native.Some (r1, rest)))
and parse_seq (fuel : Prims.nat) (input : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match input with
     | [] -> FStar_Pervasives_Native.Some (Regex_Syntax.R_Eps, [])
     | h::uu___1 ->
         if (h = cp_pipe) || (h = cp_rparen)
         then FStar_Pervasives_Native.Some (Regex_Syntax.R_Eps, input)
         else
           (match parse_rep (fuel - Prims.int_one) input with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (r1, rest) ->
                (match rest with
                 | [] -> FStar_Pervasives_Native.Some (r1, [])
                 | h2::uu___3 ->
                     if (h2 = cp_pipe) || (h2 = cp_rparen)
                     then FStar_Pervasives_Native.Some (r1, rest)
                     else
                       (match parse_seq (fuel - Prims.int_one) rest with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (r2, rest2) ->
                            FStar_Pervasives_Native.Some
                              ((Regex_Syntax.R_Cat (r1, r2)), rest2)))))
and parse_rep (fuel : Prims.nat) (input : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match parse_atom (fuel - Prims.int_one) input with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (r, rest) -> parse_quant r rest)
and parse_atom (fuel : Prims.nat) (input : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match input with
     | [] -> FStar_Pervasives_Native.None
     | h::t ->
         if h = cp_lparen
         then parse_group (fuel - Prims.int_one) t
         else
           if h = cp_lbracket
           then parse_class t
           else
             if h = cp_dot
             then FStar_Pervasives_Native.Some (dot_regex, t)
             else
               if h = cp_caret
               then FStar_Pervasives_Native.Some (Regex_Syntax.R_Eps, t)
               else
                 if h = cp_dollar
                 then FStar_Pervasives_Native.Some (Regex_Syntax.R_Eps, t)
                 else
                   if h = cp_backslash
                   then
                     (match t with
                      | [] -> FStar_Pervasives_Native.None
                      | letter::t2 -> parse_escape_atom letter t2)
                   else
                     if is_atom_meta h
                     then FStar_Pervasives_Native.None
                     else FStar_Pervasives_Native.Some ((single h), t))
and parse_group (fuel : Prims.nat) (t : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match t with
     | q::c::t2 ->
         if (q = cp_question) && (c = cp_colon)
         then parse_group_close (fuel - Prims.int_one) t2
         else
           if q = cp_question
           then FStar_Pervasives_Native.None
           else parse_group_close (fuel - Prims.int_one) t
     | q::uu___1 ->
         if q = cp_question
         then FStar_Pervasives_Native.None
         else parse_group_close (fuel - Prims.int_one) t
     | [] -> parse_group_close (fuel - Prims.int_one) t)
and parse_group_close (fuel : Prims.nat) (t : Prims.nat Prims.list) :
  (Regex_Syntax.regex * Prims.nat Prims.list) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match parse_alt (fuel - Prims.int_one) t with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (r, rest) ->
         (match rest with
          | c::t2 ->
              if c = cp_rparen
              then FStar_Pervasives_Native.Some (r, t2)
              else FStar_Pervasives_Native.None
          | [] -> FStar_Pervasives_Native.None))
let parse_cps (cps : Prims.nat Prims.list) :
  Regex_Syntax.regex FStar_Pervasives_Native.option=
  let fuel =
    (Prims.of_int (16)) *
      ((FStar_List_Tot_Base.length cps) + (Prims.of_int (4))) in
  match parse_alt fuel cps with
  | FStar_Pervasives_Native.Some (r, []) -> FStar_Pervasives_Native.Some r
  | uu___ -> FStar_Pervasives_Native.None
let cps_of_string (s : Prims.string) : Prims.nat Prims.list=
  FStar_List_Tot_Base.map (fun c -> FStar_Char.int_of_char c)
    (FStar_String.list_of_string s)
let parse_xsd_pattern (s : Prims.string) :
  Regex_Syntax.regex FStar_Pervasives_Native.option=
  parse_cps (cps_of_string s)
