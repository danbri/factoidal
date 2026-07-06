open Prims
let wkt_dot : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (0x2E))
let wkt_minus : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (0x2D))
let wkt_plus : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (0x2B))
let wkt_lparen : FStar_Char.char=
  FStar_Char.char_of_int (Prims.of_int (0x28))
let wkt_rparen : FStar_Char.char=
  FStar_Char.char_of_int (Prims.of_int (0x29))
let wkt_comma : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (0x2C))
let wkt_lt : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (0x3C))
let wkt_gt : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (0x3E))
let is_wkt_digit (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let is_wkt_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let wkt_upper_char (c : FStar_Char.char) : FStar_Char.char=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))
  then FStar_Char.char_of_int (code - (Prims.of_int (0x20)))
  else c
let rec wkt_upper_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest -> (wkt_upper_char c) :: (wkt_upper_chars rest)
let wkt_upper (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (wkt_upper_chars (FStar_String.list_of_string s))
let wkt_fuel_of (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  if (Parser_FastString.fs_byte_length input) >= pos
  then ((Parser_FastString.fs_byte_length input) - pos) + Prims.int_one
  else Prims.int_zero
let skip_ws (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  match Parser_Combinators.ptake_while is_wkt_ws input pos with
  | Parser_Combinators.ParseOk (uu___, pos') -> pos'
  | Parser_Combinators.ParseFail (uu___, uu___1) -> pos
let wkt_digit_val (c : FStar_Char.char) : Prims.nat=
  let v = (FStar_Char.int_of_char c) - (Prims.of_int (0x30)) in
  if v < Prims.int_zero then Prims.int_zero else v
let rec wkt_digits_to_nat (cs : FStar_Char.char Prims.list) (acc : Prims.nat)
  : Prims.nat=
  match cs with
  | [] -> acc
  | c::rest ->
      wkt_digits_to_nat rest
        ((acc * (Prims.of_int (10))) + (wkt_digit_val c))
let rec wkt_scan_number_end (input : Prims.string) (pos : Prims.nat)
  (seen_dot : Prims.bool) (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    if pos >= (Parser_FastString.fs_byte_length input)
    then pos
    else
      (let c = Parser_FastString.fs_byte_index input pos in
       if is_wkt_digit c
       then
         wkt_scan_number_end input (pos + Prims.int_one) seen_dot
           (fuel - Prims.int_one)
       else
         if (c = wkt_dot) && (Prims.op_Negation seen_dot)
         then
           wkt_scan_number_end input (pos + Prims.int_one) true
             (fuel - Prims.int_one)
         else pos)
let rec wkt_list_take_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then x :: (wkt_list_take_while f xs) else []
let rec wkt_list_drop_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then wkt_list_drop_while f xs else x :: xs
let wkt_split_number_token (tok : Prims.string) :
  (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  let chars = FStar_String.list_of_string tok in
  let before = wkt_list_take_while (fun c -> c <> wkt_dot) chars in
  let after_with_dot = wkt_list_drop_while (fun c -> c <> wkt_dot) chars in
  let has_dot = Prims.op_Negation (Prims.uu___is_Nil after_with_dot) in
  let frac = if has_dot then FStar_List_Tot_Base.tl after_with_dot else [] in
  if (Prims.uu___is_Nil before) && (Prims.uu___is_Nil frac)
  then FStar_Pervasives_Native.None
  else
    (let scale = FStar_List_Tot_Base.length frac in
     let mant =
       ((wkt_digits_to_nat before Prims.int_zero) *
          (RDF_Geo_Types.geo_pow10 scale))
         + (wkt_digits_to_nat frac Prims.int_zero) in
     FStar_Pervasives_Native.Some (mant, scale))
let parse_wkt_number (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_scaled Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected a number", pos)
  else
    (let c0 = Parser_FastString.fs_byte_index input pos in
     let uu___1 =
       if c0 = wkt_minus
       then (true, (pos + Prims.int_one))
       else
         if c0 = wkt_plus
         then (false, (pos + Prims.int_one))
         else (false, pos) in
     match uu___1 with
     | (is_neg, start) ->
         if start >= len
         then
           Parser_Combinators.ParseFail ("expected digits after sign", pos)
         else
           (let fuel = (len - start) + Prims.int_one in
            let end_pos = wkt_scan_number_end input start false fuel in
            if end_pos = start
            then Parser_Combinators.ParseFail ("expected digits", pos)
            else
              (let tok =
                 Parser_FastString.fs_byte_sub input start (end_pos - start) in
               match wkt_split_number_token tok with
               | FStar_Pervasives_Native.None ->
                   Parser_Combinators.ParseFail
                     ("malformed number token", pos)
               | FStar_Pervasives_Native.Some (mant, scale) ->
                   Parser_Combinators.ParseOk
                     ({
                        RDF_Geo_Types.gs_mantissa =
                          (if is_neg then Prims.int_zero - mant else mant);
                        RDF_Geo_Types.gs_scale = scale
                      }, end_pos))))
let match_keyword (kw : Prims.string) (input : Prims.string)
  (pos : Prims.nat) : unit Parser_Combinators.parse_result=
  let klen = Parser_FastString.fs_byte_length kw in
  let ilen = Parser_FastString.fs_byte_length input in
  if (pos + klen) <= ilen
  then
    let candidate = Parser_FastString.fs_byte_sub input pos klen in
    (if (wkt_upper candidate) = kw
     then Parser_Combinators.ParseOk ((), (pos + klen))
     else
       Parser_Combinators.ParseFail
         ((FStar_String.concat "" ["expected "; kw]), pos))
  else
    Parser_Combinators.ParseFail
      ((FStar_String.concat "" ["expected "; kw]), pos)
let parse_char_tok (c : FStar_Char.char) (input : Prims.string)
  (pos : Prims.nat) : unit Parser_Combinators.parse_result=
  let pos1 = skip_ws input pos in
  match Parser_Combinators.pchar c input pos1 with
  | Parser_Combinators.ParseOk (uu___, pos2) ->
      Parser_Combinators.ParseOk ((), pos2)
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let try_empty (input : Prims.string) (pos : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  let pos1 = skip_ws input pos in
  match match_keyword "EMPTY" input pos1 with
  | Parser_Combinators.ParseOk ((), pos2) ->
      FStar_Pervasives_Native.Some pos2
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let parse_coordinate (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_point Parser_Combinators.parse_result=
  let pos1 = skip_ws input pos in
  match parse_wkt_number input pos1 with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk (x, pos2) ->
      let pos3 = skip_ws input pos2 in
      (match parse_wkt_number input pos3 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (y, pos4) ->
           let pos5 = skip_ws input pos4 in
           let has_more_num =
             (pos5 < (Parser_FastString.fs_byte_length input)) &&
               (let c = Parser_FastString.fs_byte_index input pos5 in
                (((is_wkt_digit c) || (c = wkt_minus)) || (c = wkt_plus)) ||
                  (c = wkt_dot)) in
           if has_more_num
           then
             Parser_Combinators.ParseFail
               ("3D/M coordinates are out of scope for v0", pos5)
           else
             Parser_Combinators.ParseOk
               ({ RDF_Geo_Types.gp_x = x; RDF_Geo_Types.gp_y = y }, pos4))
let rec parse_point_list_rest (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Geo_Types.geo_point Prims.list) (fuel : Prims.nat) :
  RDF_Geo_Types.geo_point Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("point list too long", pos)
  else
    (let pos1 = skip_ws input pos in
     match Parser_Combinators.pchar wkt_comma input pos1 with
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos1)
     | Parser_Combinators.ParseOk (uu___1, pos2) ->
         (match parse_coordinate input pos2 with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (p, pos3) ->
              parse_point_list_rest input pos3 (p :: acc)
                (fuel - Prims.int_one)))
let parse_point_list (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_point Prims.list Parser_Combinators.parse_result=
  match parse_char_tok wkt_lparen input pos with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk ((), pos1) ->
      (match parse_coordinate input pos1 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (p, pos2) ->
           let fuel = wkt_fuel_of input pos2 in
           (match parse_point_list_rest input pos2 [p] fuel with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (pts, pos3) ->
                (match parse_char_tok wkt_rparen input pos3 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     Parser_Combinators.ParseOk (pts, pos4))))
let rec parse_ring_list_rest (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Geo_Types.geo_ring Prims.list) (fuel : Prims.nat) :
  RDF_Geo_Types.geo_ring Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("ring list too long", pos)
  else
    (let pos1 = skip_ws input pos in
     match Parser_Combinators.pchar wkt_comma input pos1 with
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos1)
     | Parser_Combinators.ParseOk (uu___1, pos2) ->
         (match parse_point_list input pos2 with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (r, pos3) ->
              parse_ring_list_rest input pos3 (r :: acc)
                (fuel - Prims.int_one)))
let parse_polygon_body (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_polygon Parser_Combinators.parse_result=
  match parse_char_tok wkt_lparen input pos with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk ((), pos1) ->
      (match parse_point_list input pos1 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (ext, pos2) ->
           let fuel = wkt_fuel_of input pos2 in
           (match parse_ring_list_rest input pos2 [] fuel with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (holes, pos3) ->
                (match parse_char_tok wkt_rparen input pos3 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     Parser_Combinators.ParseOk
                       ({
                          RDF_Geo_Types.gpoly_ext = ext;
                          RDF_Geo_Types.gpoly_holes = holes
                        }, pos4))))
let rec parse_polygon_list_rest (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Geo_Types.geo_polygon Prims.list) (fuel : Prims.nat) :
  RDF_Geo_Types.geo_polygon Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("polygon list too long", pos)
  else
    (let pos1 = skip_ws input pos in
     match Parser_Combinators.pchar wkt_comma input pos1 with
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos1)
     | Parser_Combinators.ParseOk (uu___1, pos2) ->
         (match parse_polygon_body input pos2 with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (p, pos3) ->
              parse_polygon_list_rest input pos3 (p :: acc)
                (fuel - Prims.int_one)))
let parse_multipolygon_body (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_polygon Prims.list Parser_Combinators.parse_result=
  match parse_char_tok wkt_lparen input pos with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk ((), pos1) ->
      (match parse_polygon_body input pos1 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (p, pos2) ->
           let fuel = wkt_fuel_of input pos2 in
           (match parse_polygon_list_rest input pos2 [p] fuel with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (ps, pos3) ->
                (match parse_char_tok wkt_rparen input pos3 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     Parser_Combinators.ParseOk (ps, pos4))))
let rec parse_linestring_list_rest (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Geo_Types.geo_point Prims.list Prims.list) (fuel : Prims.nat) :
  RDF_Geo_Types.geo_point Prims.list Prims.list
    Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("linestring list too long", pos)
  else
    (let pos1 = skip_ws input pos in
     match Parser_Combinators.pchar wkt_comma input pos1 with
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos1)
     | Parser_Combinators.ParseOk (uu___1, pos2) ->
         (match parse_point_list input pos2 with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (l, pos3) ->
              parse_linestring_list_rest input pos3 (l :: acc)
                (fuel - Prims.int_one)))
let parse_multilinestring_body (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_point Prims.list Prims.list
    Parser_Combinators.parse_result=
  match parse_char_tok wkt_lparen input pos with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk ((), pos1) ->
      (match parse_point_list input pos1 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (l, pos2) ->
           let fuel = wkt_fuel_of input pos2 in
           (match parse_linestring_list_rest input pos2 [l] fuel with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (ls, pos3) ->
                (match parse_char_tok wkt_rparen input pos3 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     Parser_Combinators.ParseOk (ls, pos4))))
let parse_multipoint_component (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_point Parser_Combinators.parse_result=
  let pos1 = skip_ws input pos in
  match Parser_Combinators.pchar wkt_lparen input pos1 with
  | Parser_Combinators.ParseOk (uu___, pos2) ->
      (match parse_coordinate input pos2 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (p, pos3) ->
           (match parse_char_tok wkt_rparen input pos3 with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk ((), pos4) ->
                Parser_Combinators.ParseOk (p, pos4)))
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      parse_coordinate input pos1
let rec parse_multipoint_rest (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Geo_Types.geo_point Prims.list) (fuel : Prims.nat) :
  RDF_Geo_Types.geo_point Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("multipoint list too long", pos)
  else
    (let pos1 = skip_ws input pos in
     match Parser_Combinators.pchar wkt_comma input pos1 with
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos1)
     | Parser_Combinators.ParseOk (uu___1, pos2) ->
         (match parse_multipoint_component input pos2 with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (p, pos3) ->
              parse_multipoint_rest input pos3 (p :: acc)
                (fuel - Prims.int_one)))
let parse_multipoint_body (input : Prims.string) (pos : Prims.nat) :
  RDF_Geo_Types.geo_point Prims.list Parser_Combinators.parse_result=
  match parse_char_tok wkt_lparen input pos with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk ((), pos1) ->
      (match parse_multipoint_component input pos1 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (p, pos2) ->
           let fuel = wkt_fuel_of input pos2 in
           (match parse_multipoint_rest input pos2 [p] fuel with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (pts, pos3) ->
                (match parse_char_tok wkt_rparen input pos3 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     Parser_Combinators.ParseOk (pts, pos4))))
let rec parse_tagged_geometry (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) :
  RDF_Geo_Types.geo_geometry Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("geometry nesting exceeds available input", pos)
  else
    (let pos0 = skip_ws input pos in
     match match_keyword "GEOMETRYCOLLECTION" input pos0 with
     | Parser_Combinators.ParseOk ((), pos1) ->
         (match try_empty input pos1 with
          | FStar_Pervasives_Native.Some pos2 ->
              Parser_Combinators.ParseOk
                ((RDF_Geo_Types.G_Empty RDF_Geo_Types.GK_GeometryCollection),
                  pos2)
          | FStar_Pervasives_Native.None ->
              (match parse_char_tok wkt_lparen input pos1 with
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)
               | Parser_Combinators.ParseOk ((), pos2) ->
                   (match parse_tagged_geometry input pos2
                            (fuel - Prims.int_one)
                    with
                    | Parser_Combinators.ParseFail (msg, fpos) ->
                        Parser_Combinators.ParseFail (msg, fpos)
                    | Parser_Combinators.ParseOk (g, pos3) ->
                        (match parse_geometry_list_rest input pos3 [g]
                                 (fuel - Prims.int_one)
                         with
                         | Parser_Combinators.ParseFail (msg, fpos) ->
                             Parser_Combinators.ParseFail (msg, fpos)
                         | Parser_Combinators.ParseOk (gs, pos4) ->
                             (match parse_char_tok wkt_rparen input pos4 with
                              | Parser_Combinators.ParseFail (msg, fpos) ->
                                  Parser_Combinators.ParseFail (msg, fpos)
                              | Parser_Combinators.ParseOk ((), pos5) ->
                                  Parser_Combinators.ParseOk
                                    ((RDF_Geo_Types.G_GeometryCollection gs),
                                      pos5))))))
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         (match match_keyword "MULTIPOLYGON" input pos0 with
          | Parser_Combinators.ParseOk ((), pos1) ->
              (match try_empty input pos1 with
               | FStar_Pervasives_Native.Some pos2 ->
                   Parser_Combinators.ParseOk
                     ((RDF_Geo_Types.G_Empty RDF_Geo_Types.GK_MultiPolygon),
                       pos2)
               | FStar_Pervasives_Native.None ->
                   (match parse_multipolygon_body input pos1 with
                    | Parser_Combinators.ParseFail (msg, fpos) ->
                        Parser_Combinators.ParseFail (msg, fpos)
                    | Parser_Combinators.ParseOk (ps, pos2) ->
                        Parser_Combinators.ParseOk
                          ((RDF_Geo_Types.G_MultiPolygon ps), pos2)))
          | Parser_Combinators.ParseFail (uu___3, uu___4) ->
              (match match_keyword "MULTILINESTRING" input pos0 with
               | Parser_Combinators.ParseOk ((), pos1) ->
                   (match try_empty input pos1 with
                    | FStar_Pervasives_Native.Some pos2 ->
                        Parser_Combinators.ParseOk
                          ((RDF_Geo_Types.G_Empty
                              RDF_Geo_Types.GK_MultiLineString), pos2)
                    | FStar_Pervasives_Native.None ->
                        (match parse_multilinestring_body input pos1 with
                         | Parser_Combinators.ParseFail (msg, fpos) ->
                             Parser_Combinators.ParseFail (msg, fpos)
                         | Parser_Combinators.ParseOk (ls, pos2) ->
                             Parser_Combinators.ParseOk
                               ((RDF_Geo_Types.G_MultiLineString ls), pos2)))
               | Parser_Combinators.ParseFail (uu___5, uu___6) ->
                   (match match_keyword "MULTIPOINT" input pos0 with
                    | Parser_Combinators.ParseOk ((), pos1) ->
                        (match try_empty input pos1 with
                         | FStar_Pervasives_Native.Some pos2 ->
                             Parser_Combinators.ParseOk
                               ((RDF_Geo_Types.G_Empty
                                   RDF_Geo_Types.GK_MultiPoint), pos2)
                         | FStar_Pervasives_Native.None ->
                             (match parse_multipoint_body input pos1 with
                              | Parser_Combinators.ParseFail (msg, fpos) ->
                                  Parser_Combinators.ParseFail (msg, fpos)
                              | Parser_Combinators.ParseOk (pts, pos2) ->
                                  Parser_Combinators.ParseOk
                                    ((RDF_Geo_Types.G_MultiPoint pts), pos2)))
                    | Parser_Combinators.ParseFail (uu___7, uu___8) ->
                        (match match_keyword "LINESTRING" input pos0 with
                         | Parser_Combinators.ParseOk ((), pos1) ->
                             (match try_empty input pos1 with
                              | FStar_Pervasives_Native.Some pos2 ->
                                  Parser_Combinators.ParseOk
                                    ((RDF_Geo_Types.G_Empty
                                        RDF_Geo_Types.GK_LineString), pos2)
                              | FStar_Pervasives_Native.None ->
                                  (match parse_point_list input pos1 with
                                   | Parser_Combinators.ParseFail (msg, fpos)
                                       ->
                                       Parser_Combinators.ParseFail
                                         (msg, fpos)
                                   | Parser_Combinators.ParseOk (l, pos2) ->
                                       Parser_Combinators.ParseOk
                                         ((RDF_Geo_Types.G_LineString l),
                                           pos2)))
                         | Parser_Combinators.ParseFail (uu___9, uu___10) ->
                             (match match_keyword "POLYGON" input pos0 with
                              | Parser_Combinators.ParseOk ((), pos1) ->
                                  (match try_empty input pos1 with
                                   | FStar_Pervasives_Native.Some pos2 ->
                                       Parser_Combinators.ParseOk
                                         ((RDF_Geo_Types.G_Empty
                                             RDF_Geo_Types.GK_Polygon), pos2)
                                   | FStar_Pervasives_Native.None ->
                                       (match parse_polygon_body input pos1
                                        with
                                        | Parser_Combinators.ParseFail
                                            (msg, fpos) ->
                                            Parser_Combinators.ParseFail
                                              (msg, fpos)
                                        | Parser_Combinators.ParseOk
                                            (p, pos2) ->
                                            Parser_Combinators.ParseOk
                                              ((RDF_Geo_Types.G_Polygon p),
                                                pos2)))
                              | Parser_Combinators.ParseFail
                                  (uu___11, uu___12) ->
                                  (match match_keyword "POINT" input pos0
                                   with
                                   | Parser_Combinators.ParseOk ((), pos1) ->
                                       (match try_empty input pos1 with
                                        | FStar_Pervasives_Native.Some pos2
                                            ->
                                            Parser_Combinators.ParseOk
                                              ((RDF_Geo_Types.G_Empty
                                                  RDF_Geo_Types.GK_Point),
                                                pos2)
                                        | FStar_Pervasives_Native.None ->
                                            (match parse_char_tok wkt_lparen
                                                     input pos1
                                             with
                                             | Parser_Combinators.ParseFail
                                                 (msg, fpos) ->
                                                 Parser_Combinators.ParseFail
                                                   (msg, fpos)
                                             | Parser_Combinators.ParseOk
                                                 ((), pos2) ->
                                                 (match parse_coordinate
                                                          input pos2
                                                  with
                                                  | Parser_Combinators.ParseFail
                                                      (msg, fpos) ->
                                                      Parser_Combinators.ParseFail
                                                        (msg, fpos)
                                                  | Parser_Combinators.ParseOk
                                                      (p, pos3) ->
                                                      (match parse_char_tok
                                                               wkt_rparen
                                                               input pos3
                                                       with
                                                       | Parser_Combinators.ParseFail
                                                           (msg, fpos) ->
                                                           Parser_Combinators.ParseFail
                                                             (msg, fpos)
                                                       | Parser_Combinators.ParseOk
                                                           ((), pos4) ->
                                                           Parser_Combinators.ParseOk
                                                             ((RDF_Geo_Types.G_Point
                                                                 p), pos4)))))
                                   | Parser_Combinators.ParseFail
                                       (uu___13, uu___14) ->
                                       Parser_Combinators.ParseFail
                                         ("expected a WKT geometry tag",
                                           pos0))))))))
and parse_geometry_list_rest (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Geo_Types.geo_geometry Prims.list) (fuel : Prims.nat) :
  RDF_Geo_Types.geo_geometry Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos)
  else
    (let pos1 = skip_ws input pos in
     match Parser_Combinators.pchar wkt_comma input pos1 with
     | Parser_Combinators.ParseFail (uu___1, uu___2) ->
         Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos1)
     | Parser_Combinators.ParseOk (uu___1, pos2) ->
         (match parse_tagged_geometry input pos2 (fuel - Prims.int_one) with
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)
          | Parser_Combinators.ParseOk (g, pos3) ->
              parse_geometry_list_rest input pos3 (g :: acc)
                (fuel - Prims.int_one)))
let rec scan_crs_end (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    if pos >= (Parser_FastString.fs_byte_length input)
    then pos
    else
      if (Parser_FastString.fs_byte_index input pos) = wkt_gt
      then pos
      else scan_crs_end input (pos + Prims.int_one) (fuel - Prims.int_one)
let try_parse_crs_prefix (input : Prims.string) (pos : Prims.nat) :
  (Prims.string FStar_Pervasives_Native.option * Prims.nat)=
  let pos0 = skip_ws input pos in
  if
    (pos0 < (Parser_FastString.fs_byte_length input)) &&
      ((Parser_FastString.fs_byte_index input pos0) = wkt_lt)
  then
    let fuel = wkt_fuel_of input pos0 in
    let end_pos = scan_crs_end input (pos0 + Prims.int_one) fuel in
    (if
       (end_pos < (Parser_FastString.fs_byte_length input)) &&
         ((Parser_FastString.fs_byte_index input end_pos) = wkt_gt)
     then
       let iri =
         Parser_FastString.fs_byte_sub input (pos0 + Prims.int_one)
           ((end_pos - pos0) - Prims.int_one) in
       ((FStar_Pervasives_Native.Some iri), (end_pos + Prims.int_one))
     else (FStar_Pervasives_Native.None, pos))
  else (FStar_Pervasives_Native.None, pos)
let parse_wkt_literal (input : Prims.string) :
  RDF_Geo_Types.geo_wkt_value FStar_Pervasives_Native.option=
  let uu___ = try_parse_crs_prefix input Prims.int_zero in
  match uu___ with
  | (crs, pos1) ->
      let fuel = wkt_fuel_of input pos1 in
      (match parse_tagged_geometry input pos1 fuel with
       | Parser_Combinators.ParseFail (uu___1, uu___2) ->
           FStar_Pervasives_Native.None
       | Parser_Combinators.ParseOk (g, pos2) ->
           let pos3 = skip_ws input pos2 in
           if pos3 = (Parser_FastString.fs_byte_length input)
           then
             FStar_Pervasives_Native.Some
               { RDF_Geo_Types.gw_crs = crs; RDF_Geo_Types.gw_geom = g }
           else FStar_Pervasives_Native.None)
let rec serialize_points (pts : RDF_Geo_Types.geo_point Prims.list) :
  Prims.string=
  match pts with
  | [] -> ""
  | p::[] ->
      Prims.strcat (RDF_Geo_Types.gs_to_string p.RDF_Geo_Types.gp_x)
        (Prims.strcat " " (RDF_Geo_Types.gs_to_string p.RDF_Geo_Types.gp_y))
  | p::rest ->
      Prims.strcat (RDF_Geo_Types.gs_to_string p.RDF_Geo_Types.gp_x)
        (Prims.strcat " "
           (Prims.strcat (RDF_Geo_Types.gs_to_string p.RDF_Geo_Types.gp_y)
              (Prims.strcat ", " (serialize_points rest))))
let serialize_ring (r : RDF_Geo_Types.geo_ring) : Prims.string=
  Prims.strcat "(" (Prims.strcat (serialize_points r) ")")
let rec serialize_rings (rs : RDF_Geo_Types.geo_ring Prims.list) :
  Prims.string=
  match rs with
  | [] -> ""
  | r::[] -> serialize_ring r
  | r::rest ->
      Prims.strcat (serialize_ring r)
        (Prims.strcat ", " (serialize_rings rest))
let serialize_polygon_body (p : RDF_Geo_Types.geo_polygon) : Prims.string=
  Prims.strcat "("
    (Prims.strcat
       (serialize_rings ((p.RDF_Geo_Types.gpoly_ext) ::
          (p.RDF_Geo_Types.gpoly_holes))) ")")
let rec serialize_polygons (ps : RDF_Geo_Types.geo_polygon Prims.list) :
  Prims.string=
  match ps with
  | [] -> ""
  | p::[] -> serialize_polygon_body p
  | p::rest ->
      Prims.strcat (serialize_polygon_body p)
        (Prims.strcat ", " (serialize_polygons rest))
let rec serialize_linestrings
  (ls : RDF_Geo_Types.geo_point Prims.list Prims.list) : Prims.string=
  match ls with
  | [] -> ""
  | l::[] -> Prims.strcat "(" (Prims.strcat (serialize_points l) ")")
  | l::rest ->
      Prims.strcat "("
        (Prims.strcat (serialize_points l)
           (Prims.strcat ")" (Prims.strcat ", " (serialize_linestrings rest))))
let geo_kind_tag (k : RDF_Geo_Types.geo_kind) : Prims.string=
  match k with
  | RDF_Geo_Types.GK_Point -> "POINT"
  | RDF_Geo_Types.GK_LineString -> "LINESTRING"
  | RDF_Geo_Types.GK_Polygon -> "POLYGON"
  | RDF_Geo_Types.GK_MultiPoint -> "MULTIPOINT"
  | RDF_Geo_Types.GK_MultiLineString -> "MULTILINESTRING"
  | RDF_Geo_Types.GK_MultiPolygon -> "MULTIPOLYGON"
  | RDF_Geo_Types.GK_GeometryCollection -> "GEOMETRYCOLLECTION"
let rec serialize_geometry (g : RDF_Geo_Types.geo_geometry) : Prims.string=
  match g with
  | RDF_Geo_Types.G_Point p ->
      Prims.strcat "POINT("
        (Prims.strcat (RDF_Geo_Types.gs_to_string p.RDF_Geo_Types.gp_x)
           (Prims.strcat " "
              (Prims.strcat (RDF_Geo_Types.gs_to_string p.RDF_Geo_Types.gp_y)
                 ")")))
  | RDF_Geo_Types.G_LineString l ->
      Prims.strcat "LINESTRING(" (Prims.strcat (serialize_points l) ")")
  | RDF_Geo_Types.G_Polygon p ->
      Prims.strcat "POLYGON" (serialize_polygon_body p)
  | RDF_Geo_Types.G_MultiPoint pts ->
      Prims.strcat "MULTIPOINT(" (Prims.strcat (serialize_points pts) ")")
  | RDF_Geo_Types.G_MultiLineString ls ->
      Prims.strcat "MULTILINESTRING("
        (Prims.strcat (serialize_linestrings ls) ")")
  | RDF_Geo_Types.G_MultiPolygon ps ->
      Prims.strcat "MULTIPOLYGON(" (Prims.strcat (serialize_polygons ps) ")")
  | RDF_Geo_Types.G_GeometryCollection gs ->
      Prims.strcat "GEOMETRYCOLLECTION("
        (Prims.strcat (serialize_geometry_list gs) ")")
  | RDF_Geo_Types.G_Empty k -> Prims.strcat (geo_kind_tag k) " EMPTY"
and serialize_geometry_list (gs : RDF_Geo_Types.geo_geometry Prims.list) :
  Prims.string=
  match gs with
  | [] -> ""
  | g::[] -> serialize_geometry g
  | g::rest ->
      Prims.strcat (serialize_geometry g)
        (Prims.strcat ", " (serialize_geometry_list rest))
let serialize_wkt_value (v : RDF_Geo_Types.geo_wkt_value) : Prims.string=
  match v.RDF_Geo_Types.gw_crs with
  | FStar_Pervasives_Native.None ->
      serialize_geometry v.RDF_Geo_Types.gw_geom
  | FStar_Pervasives_Native.Some crs ->
      Prims.strcat "<"
        (Prims.strcat crs
           (Prims.strcat "> " (serialize_geometry v.RDF_Geo_Types.gw_geom)))
