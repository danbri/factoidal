open Prims
let rec nat_xor (a : Prims.nat) (b : Prims.nat) (fuel : Prims.nat) :
  Prims.nat=
  if fuel = Prims.int_zero
  then Prims.int_zero
  else
    (let low =
       if ((mod) a (Prims.of_int (2))) = ((mod) b (Prims.of_int (2)))
       then Prims.int_zero
       else Prims.int_one in
     low +
       ((Prims.of_int (2)) *
          (nat_xor (a / (Prims.of_int (2))) (b / (Prims.of_int (2)))
             (fuel - Prims.int_one))))
let hex_byte (s : Prims.string) (i : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if (((Prims.of_int (2)) * i) + Prims.int_one) < (FStar_String.strlen s)
  then Parquet_Footer.byte_at_hex s ((Prims.of_int (2)) * i)
  else FStar_Pervasives_Native.None
let hex_len_bytes (s : Prims.string) : Prims.nat=
  (FStar_String.strlen s) / (Prims.of_int (2))
let crc16_step (c : Prims.nat) : Prims.nat=
  if ((mod) c (Prims.of_int (2))) = Prims.int_one
  then
    nat_xor (c / (Prims.of_int (2))) (Prims.of_int (0xA001))
      (Prims.of_int (32))
  else c / (Prims.of_int (2))
let crc16_byte (crc : Prims.nat) (b : Prims.nat) : Prims.nat=
  let c0 =
    (mod) (nat_xor crc b (Prims.of_int (32))) (Prims.parse_int "65536") in
  crc16_step
    (crc16_step
       (crc16_step
          (crc16_step (crc16_step (crc16_step (crc16_step (crc16_step c0)))))))
let rec crc16_range (s : Prims.string) (pos : Prims.nat) (count : Prims.nat)
  (crc : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then FStar_Pervasives_Native.Some crc
  else
    (match hex_byte s pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         crc16_range s (pos + Prims.int_one) (count - Prims.int_one)
           (crc16_byte crc b))
let rec vbyte_decode_acc (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (mult : Prims.pos) (acc : Prims.nat) :
  (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match hex_byte s pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         if b >= (Prims.of_int (128))
         then
           FStar_Pervasives_Native.Some
             ((acc + ((b - (Prims.of_int (128))) * mult)),
               (pos + Prims.int_one))
         else
           vbyte_decode_acc s (pos + Prims.int_one) (fuel - Prims.int_one)
             (mult * (Prims.of_int (128))) (acc + (b * mult)))
let vbyte_decode (s : Prims.string) (pos : Prims.nat) :
  (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  vbyte_decode_acc s pos (Prims.of_int (10)) Prims.int_one Prims.int_zero
let rec scan_nul (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match hex_byte s pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some uu___1 when uu___1 = Prims.int_zero ->
         FStar_Pervasives_Native.Some pos
     | FStar_Pervasives_Native.Some uu___1 ->
         (match scan_nul s (pos + Prims.int_one) (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some n -> FStar_Pervasives_Native.Some n))
let rec bytes_to_string_acc (s : Prims.string) (pos : Prims.nat)
  (count : Prims.nat) (acc : FStar_Char.char Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then
    FStar_Pervasives_Native.Some
      (FStar_String.string_of_list (FStar_List_Tot_Base.rev acc))
  else
    (match hex_byte s pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         bytes_to_string_acc s (pos + Prims.int_one) (count - Prims.int_one)
           ((Parser_NTriples.safe_char_of_int b) :: acc))
let bytes_to_string (s : Prims.string) (pos : Prims.nat) (count : Prims.nat)
  : Prims.string FStar_Pervasives_Native.option=
  bytes_to_string_acc s pos count []
let rec split_on_semi (cs : FStar_Char.char Prims.list)
  (cur : FStar_Char.char Prims.list) : FStar_Char.char Prims.list Prims.list=
  match cs with
  | [] ->
      (match cur with | [] -> [] | uu___ -> [FStar_List_Tot_Base.rev cur])
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (59))
      then (FStar_List_Tot_Base.rev cur) :: (split_on_semi rest [])
      else split_on_semi rest (c :: cur)
let rec split_on_eq (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (61))
      then ((FStar_List_Tot_Base.rev acc), rest)
      else split_on_eq rest (c :: acc)
let kv_of_chars (p : FStar_Char.char Prims.list) :
  (Prims.string * Prims.string)=
  let uu___ = split_on_eq p [] in
  match uu___ with
  | (k, v) ->
      ((FStar_String.string_of_list k), (FStar_String.string_of_list v))
let parse_properties (raw : Prims.string) :
  (Prims.string * Prims.string) Prims.list=
  FStar_List_Tot_Base.map kv_of_chars
    (split_on_semi (FStar_String.list_of_string raw) [])
let rec prop_lookup (props : (Prims.string * Prims.string) Prims.list)
  (key : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  match props with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = key
      then FStar_Pervasives_Native.Some v
      else prop_lookup rest key
let rec nat_of_digits (cs : FStar_Char.char Prims.list) (acc : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      let d = FStar_Char.int_of_char c in
      if (d >= (Prims.of_int (48))) && (d <= (Prims.of_int (57)))
      then
        nat_of_digits rest
          ((acc * (Prims.of_int (10))) + (d - (Prims.of_int (48))))
      else FStar_Pervasives_Native.None
let nat_of_string (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match FStar_String.list_of_string s with
  | [] -> FStar_Pervasives_Native.None
  | cs -> nat_of_digits cs Prims.int_zero
let prop_nat (props : (Prims.string * Prims.string) Prims.list)
  (key : Prims.string) : Prims.nat FStar_Pervasives_Native.option=
  match prop_lookup props key with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> nat_of_string v
type hdt_ci_type =
  | CI_Unknown 
  | CI_Global 
  | CI_Header 
  | CI_Dictionary 
  | CI_Triples 
  | CI_Index 
let uu___is_CI_Unknown (projectee : hdt_ci_type) : Prims.bool=
  match projectee with | CI_Unknown -> true | uu___ -> false
let uu___is_CI_Global (projectee : hdt_ci_type) : Prims.bool=
  match projectee with | CI_Global -> true | uu___ -> false
let uu___is_CI_Header (projectee : hdt_ci_type) : Prims.bool=
  match projectee with | CI_Header -> true | uu___ -> false
let uu___is_CI_Dictionary (projectee : hdt_ci_type) : Prims.bool=
  match projectee with | CI_Dictionary -> true | uu___ -> false
let uu___is_CI_Triples (projectee : hdt_ci_type) : Prims.bool=
  match projectee with | CI_Triples -> true | uu___ -> false
let uu___is_CI_Index (projectee : hdt_ci_type) : Prims.bool=
  match projectee with | CI_Index -> true | uu___ -> false
let ci_type_of_byte (b : Prims.nat) : hdt_ci_type=
  if b = Prims.int_one
  then CI_Global
  else
    if b = (Prims.of_int (2))
    then CI_Header
    else
      if b = (Prims.of_int (3))
      then CI_Dictionary
      else
        if b = (Prims.of_int (4))
        then CI_Triples
        else if b = (Prims.of_int (5)) then CI_Index else CI_Unknown
type hdt_control_info =
  {
  hci_start: Prims.nat ;
  hci_type: hdt_ci_type ;
  hci_format: Prims.string ;
  hci_props: (Prims.string * Prims.string) Prims.list ;
  hci_props_raw: Prims.string ;
  hci_crc_stored: Prims.nat ;
  hci_crc_computed: Prims.nat ;
  hci_crc_ok: Prims.bool ;
  hci_end: Prims.nat }
let __proj__Mkhdt_control_info__item__hci_start
  (projectee : hdt_control_info) : Prims.nat=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} -> hci_start
let __proj__Mkhdt_control_info__item__hci_type (projectee : hdt_control_info)
  : hdt_ci_type=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} -> hci_type
let __proj__Mkhdt_control_info__item__hci_format
  (projectee : hdt_control_info) : Prims.string=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} -> hci_format
let __proj__Mkhdt_control_info__item__hci_props
  (projectee : hdt_control_info) : (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} -> hci_props
let __proj__Mkhdt_control_info__item__hci_props_raw
  (projectee : hdt_control_info) : Prims.string=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} ->
      hci_props_raw
let __proj__Mkhdt_control_info__item__hci_crc_stored
  (projectee : hdt_control_info) : Prims.nat=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} ->
      hci_crc_stored
let __proj__Mkhdt_control_info__item__hci_crc_computed
  (projectee : hdt_control_info) : Prims.nat=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} ->
      hci_crc_computed
let __proj__Mkhdt_control_info__item__hci_crc_ok
  (projectee : hdt_control_info) : Prims.bool=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} -> hci_crc_ok
let __proj__Mkhdt_control_info__item__hci_end (projectee : hdt_control_info)
  : Prims.nat=
  match projectee with
  | { hci_start; hci_type; hci_format; hci_props; hci_props_raw;
      hci_crc_stored; hci_crc_computed; hci_crc_ok; hci_end;_} -> hci_end
let parse_control_info (s : Prims.string) (pos : Prims.nat) :
  hdt_control_info FStar_Pervasives_Native.option=
  match ((hex_byte s pos), (hex_byte s (pos + Prims.int_one)),
          (hex_byte s (pos + (Prims.of_int (2)))),
          (hex_byte s (pos + (Prims.of_int (3)))))
  with
  | (FStar_Pervasives_Native.Some b0, FStar_Pervasives_Native.Some b1,
     FStar_Pervasives_Native.Some b2, FStar_Pervasives_Native.Some b3) ->
      if
        Prims.op_Negation
          ((((b0 = (Prims.of_int (0x24))) && (b1 = (Prims.of_int (0x48)))) &&
              (b2 = (Prims.of_int (0x44))))
             && (b3 = (Prims.of_int (0x54))))
      then FStar_Pervasives_Native.None
      else
        (match hex_byte s (pos + (Prims.of_int (4))) with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some ty ->
             (match scan_nul s (pos + (Prims.of_int (5)))
                      (FStar_String.strlen s)
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some fmt_nul ->
                  (match scan_nul s (fmt_nul + Prims.int_one)
                           (FStar_String.strlen s)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some props_nul ->
                       (match ((bytes_to_string s (pos + (Prims.of_int (5)))
                                  (fmt_nul - (pos + (Prims.of_int (5))))),
                                (bytes_to_string s (fmt_nul + Prims.int_one)
                                   (props_nul - (fmt_nul + Prims.int_one))))
                        with
                        | (FStar_Pervasives_Native.Some fmt,
                           FStar_Pervasives_Native.Some raw) ->
                            (match crc16_range s pos
                                     ((props_nul + Prims.int_one) - pos)
                                     Prims.int_zero
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some crc ->
                                 (match ((hex_byte s
                                            (props_nul + Prims.int_one)),
                                          (hex_byte s
                                             (props_nul + (Prims.of_int (2)))))
                                  with
                                  | (FStar_Pervasives_Native.Some lo,
                                     FStar_Pervasives_Native.Some hi) ->
                                      let stored =
                                        lo + ((Prims.of_int (256)) * hi) in
                                      FStar_Pervasives_Native.Some
                                        {
                                          hci_start = pos;
                                          hci_type = (ci_type_of_byte ty);
                                          hci_format = fmt;
                                          hci_props = (parse_properties raw);
                                          hci_props_raw = raw;
                                          hci_crc_stored = stored;
                                          hci_crc_computed = crc;
                                          hci_crc_ok = (crc = stored);
                                          hci_end =
                                            (props_nul + (Prims.of_int (3)))
                                        }
                                  | (uu___1, uu___2) ->
                                      FStar_Pervasives_Native.None))
                        | (uu___1, uu___2) -> FStar_Pervasives_Native.None))))
  | (uu___, uu___1, uu___2, uu___3) -> FStar_Pervasives_Native.None
type hdt_log_array_info =
  {
  la_start: Prims.nat ;
  la_numbits: Prims.nat ;
  la_numentries: Prims.nat ;
  la_data_start: Prims.nat ;
  la_data_bytes: Prims.nat ;
  la_end: Prims.nat }
let __proj__Mkhdt_log_array_info__item__la_start
  (projectee : hdt_log_array_info) : Prims.nat=
  match projectee with
  | { la_start; la_numbits; la_numentries; la_data_start; la_data_bytes;
      la_end;_} -> la_start
let __proj__Mkhdt_log_array_info__item__la_numbits
  (projectee : hdt_log_array_info) : Prims.nat=
  match projectee with
  | { la_start; la_numbits; la_numentries; la_data_start; la_data_bytes;
      la_end;_} -> la_numbits
let __proj__Mkhdt_log_array_info__item__la_numentries
  (projectee : hdt_log_array_info) : Prims.nat=
  match projectee with
  | { la_start; la_numbits; la_numentries; la_data_start; la_data_bytes;
      la_end;_} -> la_numentries
let __proj__Mkhdt_log_array_info__item__la_data_start
  (projectee : hdt_log_array_info) : Prims.nat=
  match projectee with
  | { la_start; la_numbits; la_numentries; la_data_start; la_data_bytes;
      la_end;_} -> la_data_start
let __proj__Mkhdt_log_array_info__item__la_data_bytes
  (projectee : hdt_log_array_info) : Prims.nat=
  match projectee with
  | { la_start; la_numbits; la_numentries; la_data_start; la_data_bytes;
      la_end;_} -> la_data_bytes
let __proj__Mkhdt_log_array_info__item__la_end
  (projectee : hdt_log_array_info) : Prims.nat=
  match projectee with
  | { la_start; la_numbits; la_numentries; la_data_start; la_data_bytes;
      la_end;_} -> la_end
let parse_log_array_info (s : Prims.string) (pos : Prims.nat) :
  hdt_log_array_info FStar_Pervasives_Native.option=
  match hex_byte s pos with
  | FStar_Pervasives_Native.Some uu___ when uu___ = Prims.int_one ->
      (match hex_byte s (pos + Prims.int_one) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some numbits ->
           (match vbyte_decode s (pos + (Prims.of_int (2))) with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (numentries, p_crc8) ->
                let data_start = p_crc8 + Prims.int_one in
                let data_bytes =
                  ((numbits * numentries) + (Prims.of_int (7))) /
                    (Prims.of_int (8)) in
                FStar_Pervasives_Native.Some
                  {
                    la_start = pos;
                    la_numbits = numbits;
                    la_numentries = numentries;
                    la_data_start = data_start;
                    la_data_bytes = data_bytes;
                    la_end = ((data_start + data_bytes) + (Prims.of_int (4)))
                  }))
  | uu___ -> FStar_Pervasives_Native.None
type hdt_bitmap_info =
  {
  bm_start: Prims.nat ;
  bm_numbits: Prims.nat ;
  bm_data_start: Prims.nat ;
  bm_data_bytes: Prims.nat ;
  bm_end: Prims.nat }
let __proj__Mkhdt_bitmap_info__item__bm_start (projectee : hdt_bitmap_info) :
  Prims.nat=
  match projectee with
  | { bm_start; bm_numbits; bm_data_start; bm_data_bytes; bm_end;_} ->
      bm_start
let __proj__Mkhdt_bitmap_info__item__bm_numbits (projectee : hdt_bitmap_info)
  : Prims.nat=
  match projectee with
  | { bm_start; bm_numbits; bm_data_start; bm_data_bytes; bm_end;_} ->
      bm_numbits
let __proj__Mkhdt_bitmap_info__item__bm_data_start
  (projectee : hdt_bitmap_info) : Prims.nat=
  match projectee with
  | { bm_start; bm_numbits; bm_data_start; bm_data_bytes; bm_end;_} ->
      bm_data_start
let __proj__Mkhdt_bitmap_info__item__bm_data_bytes
  (projectee : hdt_bitmap_info) : Prims.nat=
  match projectee with
  | { bm_start; bm_numbits; bm_data_start; bm_data_bytes; bm_end;_} ->
      bm_data_bytes
let __proj__Mkhdt_bitmap_info__item__bm_end (projectee : hdt_bitmap_info) :
  Prims.nat=
  match projectee with
  | { bm_start; bm_numbits; bm_data_start; bm_data_bytes; bm_end;_} -> bm_end
let parse_bitmap_info (s : Prims.string) (pos : Prims.nat) :
  hdt_bitmap_info FStar_Pervasives_Native.option=
  match hex_byte s pos with
  | FStar_Pervasives_Native.Some uu___ when uu___ = Prims.int_one ->
      (match vbyte_decode s (pos + Prims.int_one) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (numbits, p_crc8) ->
           let data_start = p_crc8 + Prims.int_one in
           let data_bytes =
             if numbits = Prims.int_zero
             then Prims.int_one
             else
               ((numbits - Prims.int_one) / (Prims.of_int (8))) +
                 Prims.int_one in
           FStar_Pervasives_Native.Some
             {
               bm_start = pos;
               bm_numbits = numbits;
               bm_data_start = data_start;
               bm_data_bytes = data_bytes;
               bm_end = ((data_start + data_bytes) + (Prims.of_int (4)))
             })
  | uu___ -> FStar_Pervasives_Native.None
type hdt_pfc_section =
  {
  pfc_start: Prims.nat ;
  pfc_type: Prims.nat ;
  pfc_numstrings: Prims.nat ;
  pfc_packed_bytes: Prims.nat ;
  pfc_blocksize: Prims.nat ;
  pfc_blocks: hdt_log_array_info ;
  pfc_packed_start: Prims.nat ;
  pfc_end: Prims.nat }
let __proj__Mkhdt_pfc_section__item__pfc_start (projectee : hdt_pfc_section)
  : Prims.nat=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_start
let __proj__Mkhdt_pfc_section__item__pfc_type (projectee : hdt_pfc_section) :
  Prims.nat=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_type
let __proj__Mkhdt_pfc_section__item__pfc_numstrings
  (projectee : hdt_pfc_section) : Prims.nat=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_numstrings
let __proj__Mkhdt_pfc_section__item__pfc_packed_bytes
  (projectee : hdt_pfc_section) : Prims.nat=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_packed_bytes
let __proj__Mkhdt_pfc_section__item__pfc_blocksize
  (projectee : hdt_pfc_section) : Prims.nat=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_blocksize
let __proj__Mkhdt_pfc_section__item__pfc_blocks (projectee : hdt_pfc_section)
  : hdt_log_array_info=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_blocks
let __proj__Mkhdt_pfc_section__item__pfc_packed_start
  (projectee : hdt_pfc_section) : Prims.nat=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_packed_start
let __proj__Mkhdt_pfc_section__item__pfc_end (projectee : hdt_pfc_section) :
  Prims.nat=
  match projectee with
  | { pfc_start; pfc_type; pfc_numstrings; pfc_packed_bytes; pfc_blocksize;
      pfc_blocks; pfc_packed_start; pfc_end;_} -> pfc_end
let parse_pfc_section (s : Prims.string) (pos : Prims.nat) :
  hdt_pfc_section FStar_Pervasives_Native.option=
  match hex_byte s pos with
  | FStar_Pervasives_Native.Some uu___ when uu___ = (Prims.of_int (2)) ->
      (match vbyte_decode s (pos + Prims.int_one) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (numstrings, p1) ->
           (match vbyte_decode s p1 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (packed_bytes, p2) ->
                (match vbyte_decode s p2 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (blocksize, p3) ->
                     (match parse_log_array_info s (p3 + Prims.int_one) with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some la ->
                          FStar_Pervasives_Native.Some
                            {
                              pfc_start = pos;
                              pfc_type = (Prims.of_int (2));
                              pfc_numstrings = numstrings;
                              pfc_packed_bytes = packed_bytes;
                              pfc_blocksize = blocksize;
                              pfc_blocks = la;
                              pfc_packed_start = (la.la_end);
                              pfc_end =
                                ((la.la_end + packed_bytes) +
                                   (Prims.of_int (4)))
                            }))))
  | uu___ -> FStar_Pervasives_Native.None
type hdt_inventory =
  {
  inv_global: hdt_control_info ;
  inv_header_ci: hdt_control_info ;
  inv_header_data_start: Prims.nat ;
  inv_header_data_len: Prims.nat ;
  inv_dict_ci: hdt_control_info ;
  inv_dict_shared: hdt_pfc_section ;
  inv_dict_subjects: hdt_pfc_section ;
  inv_dict_predicates: hdt_pfc_section ;
  inv_dict_objects: hdt_pfc_section ;
  inv_triples_ci: hdt_control_info ;
  inv_triples_data_start: Prims.nat }
let __proj__Mkhdt_inventory__item__inv_global (projectee : hdt_inventory) :
  hdt_control_info=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_global
let __proj__Mkhdt_inventory__item__inv_header_ci (projectee : hdt_inventory)
  : hdt_control_info=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_header_ci
let __proj__Mkhdt_inventory__item__inv_header_data_start
  (projectee : hdt_inventory) : Prims.nat=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_header_data_start
let __proj__Mkhdt_inventory__item__inv_header_data_len
  (projectee : hdt_inventory) : Prims.nat=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_header_data_len
let __proj__Mkhdt_inventory__item__inv_dict_ci (projectee : hdt_inventory) :
  hdt_control_info=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_dict_ci
let __proj__Mkhdt_inventory__item__inv_dict_shared
  (projectee : hdt_inventory) : hdt_pfc_section=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_dict_shared
let __proj__Mkhdt_inventory__item__inv_dict_subjects
  (projectee : hdt_inventory) : hdt_pfc_section=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_dict_subjects
let __proj__Mkhdt_inventory__item__inv_dict_predicates
  (projectee : hdt_inventory) : hdt_pfc_section=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_dict_predicates
let __proj__Mkhdt_inventory__item__inv_dict_objects
  (projectee : hdt_inventory) : hdt_pfc_section=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_dict_objects
let __proj__Mkhdt_inventory__item__inv_triples_ci (projectee : hdt_inventory)
  : hdt_control_info=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_triples_ci
let __proj__Mkhdt_inventory__item__inv_triples_data_start
  (projectee : hdt_inventory) : Prims.nat=
  match projectee with
  | { inv_global; inv_header_ci; inv_header_data_start; inv_header_data_len;
      inv_dict_ci; inv_dict_shared; inv_dict_subjects; inv_dict_predicates;
      inv_dict_objects; inv_triples_ci; inv_triples_data_start;_} ->
      inv_triples_data_start
let hdt_parse_inventory_hex (s : Prims.string) :
  hdt_inventory FStar_Pervasives_Native.option=
  match parse_control_info s Prims.int_zero with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some g ->
      if Prims.op_Negation ((uu___is_CI_Global g.hci_type) && g.hci_crc_ok)
      then FStar_Pervasives_Native.None
      else
        (match parse_control_info s g.hci_end with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some h ->
             if
               Prims.op_Negation
                 ((uu___is_CI_Header h.hci_type) && h.hci_crc_ok)
             then FStar_Pervasives_Native.None
             else
               (match prop_nat h.hci_props "length" with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some hlen ->
                    let hdata = h.hci_end in
                    (match parse_control_info s (hdata + hlen) with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some d ->
                         if
                           Prims.op_Negation
                             ((uu___is_CI_Dictionary d.hci_type) &&
                                d.hci_crc_ok)
                         then FStar_Pervasives_Native.None
                         else
                           (match parse_pfc_section s d.hci_end with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some sec_sh ->
                                (match parse_pfc_section s sec_sh.pfc_end
                                 with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some sec_su ->
                                     (match parse_pfc_section s
                                              sec_su.pfc_end
                                      with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some sec_pr
                                          ->
                                          (match parse_pfc_section s
                                                   sec_pr.pfc_end
                                           with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some
                                               sec_ob ->
                                               (match parse_control_info s
                                                        sec_ob.pfc_end
                                                with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t ->
                                                    if
                                                      Prims.op_Negation
                                                        ((uu___is_CI_Triples
                                                            t.hci_type)
                                                           && t.hci_crc_ok)
                                                    then
                                                      FStar_Pervasives_Native.None
                                                    else
                                                      FStar_Pervasives_Native.Some
                                                        {
                                                          inv_global = g;
                                                          inv_header_ci = h;
                                                          inv_header_data_start
                                                            = hdata;
                                                          inv_header_data_len
                                                            = hlen;
                                                          inv_dict_ci = d;
                                                          inv_dict_shared =
                                                            sec_sh;
                                                          inv_dict_subjects =
                                                            sec_su;
                                                          inv_dict_predicates
                                                            = sec_pr;
                                                          inv_dict_objects =
                                                            sec_ob;
                                                          inv_triples_ci = t;
                                                          inv_triples_data_start
                                                            = (t.hci_end)
                                                        }))))))))
let hdt_header_text_hex (s : Prims.string) (inv : hdt_inventory) :
  Prims.string FStar_Pervasives_Native.option=
  bytes_to_string s inv.inv_header_data_start inv.inv_header_data_len
let hdt_header_triples_hex (s : Prims.string) (inv : hdt_inventory) :
  RDF_Triple.triple Prims.list FStar_Pervasives_Native.option=
  match hdt_header_text_hex s inv with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some text ->
      FStar_Pervasives_Native.Some (Parser_NTriples.parse_ntriples text)
let hdt_triples_order (inv : hdt_inventory) :
  Prims.nat FStar_Pervasives_Native.option=
  prop_nat (inv.inv_triples_ci).hci_props "order"
let rec hdt_probe_fail_pow (path : Prims.string) (n : Prims.pos)
  (fuel : Prims.nat) :
  (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match Parquet_Footer.parquet_read_range_hex path Prims.int_zero n with
     | FStar_Pervasives_Native.None ->
         FStar_Pervasives_Native.Some ((n / (Prims.of_int (2))), n)
     | FStar_Pervasives_Native.Some uu___1 ->
         hdt_probe_fail_pow path (n * (Prims.of_int (2)))
           (fuel - Prims.int_one))
let rec hdt_size_bsearch (path : Prims.string) (lo : Prims.nat)
  (hi : Prims.nat) (fuel : Prims.nat) : Prims.nat=
  if (fuel = Prims.int_zero) || ((hi - lo) <= Prims.int_one)
  then lo
  else
    (let mid = (lo + hi) / (Prims.of_int (2)) in
     match Parquet_Footer.parquet_read_range_hex path Prims.int_zero mid with
     | FStar_Pervasives_Native.Some uu___1 ->
         hdt_size_bsearch path mid hi (fuel - Prims.int_one)
     | FStar_Pervasives_Native.None ->
         hdt_size_bsearch path lo mid (fuel - Prims.int_one))
let hdt_file_size (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match Parquet_Footer.parquet_read_range_hex path Prims.int_zero
          Prims.int_zero
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some uu___ ->
      (match hdt_probe_fail_pow path Prims.int_one (Prims.of_int (64)) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (lo, hi) ->
           FStar_Pervasives_Native.Some
             (hdt_size_bsearch path lo hi (Prims.of_int (64))))
let hdt_read_file_hex (path : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match hdt_file_size path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some sz ->
      Parquet_Footer.parquet_read_range_hex path Prims.int_zero sz
let hdt_read_inventory (path : Prims.string) :
  (Prims.string * hdt_inventory) FStar_Pervasives_Native.option=
  match hdt_read_file_hex path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some hex ->
      (match hdt_parse_inventory_hex hex with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some inv ->
           FStar_Pervasives_Native.Some (hex, inv))
