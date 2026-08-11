open Prims
type byte = Prims.nat
let is_continuation (b : byte) : Prims.bool=
  (b >= (Prims.of_int (0x80))) && (b < (Prims.of_int (0xC0)))
let utf8_enc_char (c : FStar_Char.char) : byte Prims.list=
  let cp = FStar_Char.int_of_char c in
  if
    ((cp < Prims.int_zero) || (cp > (Prims.parse_int "0x10FFFF"))) ||
      ((cp >= (Prims.of_int (0xD800))) && (cp < (Prims.of_int (0xE000))))
  then [(Prims.of_int (0xEF)); (Prims.of_int (0xBF)); (Prims.of_int (0xBD))]
  else
    if cp < (Prims.of_int (0x80))
    then [cp]
    else
      if cp < (Prims.of_int (0x800))
      then
        [(Prims.of_int (0xC0)) + (cp / (Prims.of_int (0x40)));
        (Prims.of_int (0x80)) + ((mod) cp (Prims.of_int (0x40)))]
      else
        if cp < (Prims.parse_int "0x10000")
        then
          [(Prims.of_int (0xE0)) + (cp / (Prims.of_int (0x1000)));
          (Prims.of_int (0x80)) +
            ((mod) (cp / (Prims.of_int (0x40))) (Prims.of_int (0x40)));
          (Prims.of_int (0x80)) + ((mod) cp (Prims.of_int (0x40)))]
        else
          [(Prims.of_int (0xF0)) + (cp / (Prims.parse_int "0x40000"));
          (Prims.of_int (0x80)) +
            ((mod) (cp / (Prims.of_int (0x1000))) (Prims.of_int (0x40)));
          (Prims.of_int (0x80)) +
            ((mod) (cp / (Prims.of_int (0x40))) (Prims.of_int (0x40)));
          (Prims.of_int (0x80)) + ((mod) cp (Prims.of_int (0x40)))]
let utf8_bytes (s : Prims.string) : byte Prims.list=
  FStar_List_Tot_Base.concatMap utf8_enc_char (FStar_String.list_of_string s)
let rec nth_byte (bs : byte Prims.list) (i : Prims.nat) :
  byte FStar_Pervasives_Native.option=
  match bs with
  | [] -> FStar_Pervasives_Native.None
  | hd::tl ->
      if i = Prims.int_zero
      then FStar_Pervasives_Native.Some hd
      else nth_byte tl (i - Prims.int_one)
let utf8_decode_at (bs : byte Prims.list) (p : Prims.nat) :
  (Prims.nat * Prims.pos)=
  match nth_byte bs p with
  | FStar_Pervasives_Native.None -> ((Prims.of_int (0xFFFD)), Prims.int_one)
  | FStar_Pervasives_Native.Some b0 ->
      if b0 < (Prims.of_int (0x80))
      then (b0, Prims.int_one)
      else
        if b0 < (Prims.of_int (0xC2))
        then ((Prims.of_int (0xFFFD)), Prims.int_one)
        else
          if b0 < (Prims.of_int (0xE0))
          then
            (match nth_byte bs (p + Prims.int_one) with
             | FStar_Pervasives_Native.None ->
                 ((Prims.of_int (0xFFFD)), Prims.int_one)
             | FStar_Pervasives_Native.Some b1 ->
                 if Prims.op_Negation (is_continuation b1)
                 then ((Prims.of_int (0xFFFD)), Prims.int_one)
                 else
                   (let cp =
                      (((mod) b0 (Prims.of_int (0x20))) *
                         (Prims.of_int (0x40)))
                        + ((mod) b1 (Prims.of_int (0x40))) in
                    (cp, (Prims.of_int (2)))))
          else
            if b0 < (Prims.of_int (0xF0))
            then
              (match ((nth_byte bs (p + Prims.int_one)),
                       (nth_byte bs (p + (Prims.of_int (2)))))
               with
               | (FStar_Pervasives_Native.Some b1,
                  FStar_Pervasives_Native.Some b2) ->
                   if
                     (Prims.op_Negation (is_continuation b1)) ||
                       (Prims.op_Negation (is_continuation b2))
                   then ((Prims.of_int (0xFFFD)), Prims.int_one)
                   else
                     (let cp =
                        ((((mod) b0 (Prims.of_int (0x10))) *
                            (Prims.of_int (0x1000)))
                           +
                           (((mod) b1 (Prims.of_int (0x40))) *
                              (Prims.of_int (0x40))))
                          + ((mod) b2 (Prims.of_int (0x40))) in
                      if
                        (cp < (Prims.of_int (0x800))) ||
                          ((cp >= (Prims.of_int (0xD800))) &&
                             (cp <= (Prims.of_int (0xDFFF))))
                      then ((Prims.of_int (0xFFFD)), Prims.int_one)
                      else (cp, (Prims.of_int (3))))
               | uu___3 -> ((Prims.of_int (0xFFFD)), Prims.int_one))
            else
              if b0 < (Prims.of_int (0xF5))
              then
                (match ((nth_byte bs (p + Prims.int_one)),
                         (nth_byte bs (p + (Prims.of_int (2)))),
                         (nth_byte bs (p + (Prims.of_int (3)))))
                 with
                 | (FStar_Pervasives_Native.Some b1,
                    FStar_Pervasives_Native.Some b2,
                    FStar_Pervasives_Native.Some b3) ->
                     if
                       ((Prims.op_Negation (is_continuation b1)) ||
                          (Prims.op_Negation (is_continuation b2)))
                         || (Prims.op_Negation (is_continuation b3))
                     then ((Prims.of_int (0xFFFD)), Prims.int_one)
                     else
                       (let cp =
                          (((((mod) b0 (Prims.of_int (0x08))) *
                               (Prims.parse_int "0x40000"))
                              +
                              (((mod) b1 (Prims.of_int (0x40))) *
                                 (Prims.of_int (0x1000))))
                             +
                             (((mod) b2 (Prims.of_int (0x40))) *
                                (Prims.of_int (0x40))))
                            + ((mod) b3 (Prims.of_int (0x40))) in
                        if
                          (cp < (Prims.parse_int "0x10000")) ||
                            (cp > (Prims.parse_int "0x10FFFF"))
                        then ((Prims.of_int (0xFFFD)), Prims.int_one)
                        else (cp, (Prims.of_int (4))))
                 | uu___4 -> ((Prims.of_int (0xFFFD)), Prims.int_one))
              else ((Prims.of_int (0xFFFD)), Prims.int_one)
let rec drop_bytes (bs : byte Prims.list) (n : Prims.nat) : byte Prims.list=
  match bs with
  | [] -> []
  | hd::tl ->
      if n = Prims.int_zero then bs else drop_bytes tl (n - Prims.int_one)
let rec take_bytes (bs : byte Prims.list) (n : Prims.nat) : byte Prims.list=
  match bs with
  | [] -> []
  | hd::tl ->
      if n = Prims.int_zero
      then []
      else hd :: (take_bytes tl (n - Prims.int_one))
let slice_bytes (bs : byte Prims.list) (start : Prims.nat) (len : Prims.nat)
  : byte Prims.list= take_bytes (drop_bytes bs start) len
let rec find_byte_scan (bs : byte Prims.list) (b : Prims.nat)
  (idx : Prims.nat) (start : Prims.nat) : Prims.nat=
  match bs with
  | [] -> idx
  | hd::tl ->
      if (idx >= start) && (hd = b)
      then idx
      else find_byte_scan tl b (idx + Prims.int_one) start
let find_byte (bs : byte Prims.list) (b : Prims.nat) (start : Prims.nat) :
  Prims.nat= find_byte_scan bs b Prims.int_zero start
let rec utf8_decode_all_aux (bs : byte Prims.list) (blen : Prims.nat)
  (pos : Prims.nat) (acc : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  if pos >= blen
  then FStar_List_Tot_Base.rev acc
  else
    (let uu___1 = utf8_decode_at bs pos in
     match uu___1 with
     | (cp, adv) ->
         let advn = if adv = Prims.int_zero then Prims.int_one else adv in
         let next = pos + advn in
         if next > blen
         then FStar_List_Tot_Base.rev acc
         else
           (let c =
              if (cp >= Prims.int_zero) && (cp < (Prims.of_int (0xd7ff)))
              then FStar_Char.char_of_int cp
              else
                if
                  (cp >= (Prims.of_int (0xe000))) &&
                    (cp <= (Prims.parse_int "0x10ffff"))
                then FStar_Char.char_of_int cp
                else FStar_Char.char_of_int (Prims.of_int (0xFFFD)) in
            utf8_decode_all_aux bs blen next (c :: acc)))
let utf8_decode_all (bs : byte Prims.list) : FStar_Char.char Prims.list=
  utf8_decode_all_aux bs (FStar_List_Tot_Base.length bs) Prims.int_zero []
let is_cp_boundary (bs : byte Prims.list) (p : Prims.nat) : Prims.bool=
  ((p = Prims.int_zero) || (p >= (FStar_List_Tot_Base.length bs))) ||
    (match nth_byte bs p with
     | FStar_Pervasives_Native.Some b ->
         Prims.op_Negation (is_continuation b)
     | FStar_Pervasives_Native.None -> true)
let rec take_chars (cs : FStar_Char.char Prims.list) (n : Prims.nat) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | hd::tl ->
      if n = Prims.int_zero
      then []
      else hd :: (take_chars tl (n - Prims.int_one))
let rec drop_chars (cs : FStar_Char.char Prims.list) (n : Prims.nat) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | hd::tl ->
      if n = Prims.int_zero then cs else drop_chars tl (n - Prims.int_one)
let slice_chars (cs : FStar_Char.char Prims.list) (start : Prims.nat)
  (len : Prims.nat) : FStar_Char.char Prims.list=
  take_chars (drop_chars cs start) len
