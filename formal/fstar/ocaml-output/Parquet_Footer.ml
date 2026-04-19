open Prims
type parquet_footer =
  {
  pf_metadata_len: Prims.nat ;
  pf_footer_len: Prims.nat ;
  pf_magic: Prims.string }
let __proj__Mkparquet_footer__item__pf_metadata_len
  (projectee : parquet_footer) : Prims.nat=
  match projectee with
  | { pf_metadata_len; pf_footer_len; pf_magic;_} -> pf_metadata_len
let __proj__Mkparquet_footer__item__pf_footer_len
  (projectee : parquet_footer) : Prims.nat=
  match projectee with
  | { pf_metadata_len; pf_footer_len; pf_magic;_} -> pf_footer_len
let __proj__Mkparquet_footer__item__pf_magic (projectee : parquet_footer) :
  Prims.string=
  match projectee with
  | { pf_metadata_len; pf_footer_len; pf_magic;_} -> pf_magic
type compact_field =
  {
  cf_id: Prims.nat ;
  cf_type: Prims.nat ;
  cf_value_start: Prims.nat ;
  cf_next: Prims.nat }
let __proj__Mkcompact_field__item__cf_id (projectee : compact_field) :
  Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_id
let __proj__Mkcompact_field__item__cf_type (projectee : compact_field) :
  Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_type
let __proj__Mkcompact_field__item__cf_value_start (projectee : compact_field)
  : Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_value_start
let __proj__Mkcompact_field__item__cf_next (projectee : compact_field) :
  Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_next
type compact_list_info =
  {
  cli_count: Prims.nat ;
  cli_etype: Prims.nat ;
  cli_payload_start: Prims.nat }
let __proj__Mkcompact_list_info__item__cli_count
  (projectee : compact_list_info) : Prims.nat=
  match projectee with
  | { cli_count; cli_etype; cli_payload_start;_} -> cli_count
let __proj__Mkcompact_list_info__item__cli_etype
  (projectee : compact_list_info) : Prims.nat=
  match projectee with
  | { cli_count; cli_etype; cli_payload_start;_} -> cli_etype
let __proj__Mkcompact_list_info__item__cli_payload_start
  (projectee : compact_list_info) : Prims.nat=
  match projectee with
  | { cli_count; cli_etype; cli_payload_start;_} -> cli_payload_start
let parquet_magic : Prims.string= "PAR1"
let parquet_magic_hex : Prims.string= "50415231"
let parquet_read_tail (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  if not (Sys.file_exists path) then FStar_Pervasives_Native.None
  else
    let ic = open_in_bin path in
    let module S = Stdlib in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let file_len = in_channel_length ic in
         let want = Z.to_int count in
         if S.(file_len < want) then FStar_Pervasives_Native.None
         else
           let start = S.(file_len - want) in
           seek_in ic start;
           FStar_Pervasives_Native.Some (really_input_string ic want))

let parquet_read_tail_hex (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match parquet_read_tail path count with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some raw ->
      let module S = Stdlib in
      let b = Buffer.create S.(2 * String.length raw) in
      String.iter
        (fun ch -> Buffer.add_string b (Printf.sprintf "%02X" (Char.code ch)))
        raw;
      FStar_Pervasives_Native.Some (Buffer.contents b)
let parquet_read_range (path : Prims.string) (start : Prims.nat) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  if not (Sys.file_exists path) then FStar_Pervasives_Native.None
  else
    let ic = open_in_bin path in
    let module S = Stdlib in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let file_len = in_channel_length ic in
         let offset = Z.to_int start in
         let want = Z.to_int count in
         if S.(offset < 0 || want < 0 || offset > file_len || offset + want > file_len)
         then FStar_Pervasives_Native.None
         else
           (seek_in ic offset;
            FStar_Pervasives_Native.Some (really_input_string ic want)))

let parquet_read_tail (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  if not (Sys.file_exists path) then FStar_Pervasives_Native.None
  else
    let ic = open_in_bin path in
    let module S = Stdlib in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let file_len = in_channel_length ic in
         let want = Z.to_int count in
         if S.(file_len < want) then FStar_Pervasives_Native.None
         else
           let start = S.(file_len - want) in
           seek_in ic start;
           FStar_Pervasives_Native.Some (really_input_string ic want))

let parquet_read_range_hex (path : Prims.string) (start : Prims.nat) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match parquet_read_range path start count with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some raw ->
      let module S = Stdlib in
      let b = Buffer.create S.(2 * String.length raw) in
      String.iter
        (fun ch -> Buffer.add_string b (Printf.sprintf "%02X" (Char.code ch)))
        raw;
      FStar_Pervasives_Native.Some (Buffer.contents b)

external parquet_zstd_decompress_hex_runtime :
  Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option
  = "caml_parquet_zstd_decompress_hex"

let parquet_zstd_decompress_hex (compressed_hex : Prims.string) (expected_size : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  parquet_zstd_decompress_hex_runtime compressed_hex (Prims.string_of_int expected_size)
let hex_nibble (c : FStar_Char.char) :
  Prims.nat FStar_Pervasives_Native.option=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (48))) && (code <= (Prims.of_int (57)))
  then FStar_Pervasives_Native.Some (code - (Prims.of_int (48)))
  else
    if (code >= (Prims.of_int (65))) && (code <= (Prims.of_int (70)))
    then
      FStar_Pervasives_Native.Some
        ((code - (Prims.of_int (65))) + (Prims.of_int (10)))
    else
      if (code >= (Prims.of_int (97))) && (code <= (Prims.of_int (102)))
      then
        FStar_Pervasives_Native.Some
          ((code - (Prims.of_int (97))) + (Prims.of_int (10)))
      else FStar_Pervasives_Native.None
let byte_at_hex (s : Prims.string) (i : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((hex_nibble (FStar_String.index s i)),
          (hex_nibble (FStar_String.index s (i + Prims.int_one))))
  with
  | (FStar_Pervasives_Native.Some hi, FStar_Pervasives_Native.Some lo) ->
      let value =
        (((((((((((((((hi + hi) + hi) + hi) + hi) + hi) + hi) + hi) + hi) +
                 hi)
                + hi)
               + hi)
              + hi)
             + hi)
            + hi)
           + hi)
          + lo in
      FStar_Pervasives_Native.Some value
  | uu___ -> FStar_Pervasives_Native.None
let le_u32_at_hex (s : Prims.string) (start : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((byte_at_hex s start), (byte_at_hex s (start + (Prims.of_int (2)))),
          (byte_at_hex s (start + (Prims.of_int (4)))),
          (byte_at_hex s (start + (Prims.of_int (6)))))
  with
  | (FStar_Pervasives_Native.Some n0, FStar_Pervasives_Native.Some n1,
     FStar_Pervasives_Native.Some n2, FStar_Pervasives_Native.Some n3) ->
      let b0 = FStar_UInt32.uint_to_t n0 in
      let b1 =
        FStar_UInt32.shift_left (FStar_UInt32.uint_to_t n1)
          (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
      let b2 =
        FStar_UInt32.shift_left (FStar_UInt32.uint_to_t n2)
          (FStar_UInt32.uint_to_t (Prims.of_int (16))) in
      let b3 =
        FStar_UInt32.shift_left (FStar_UInt32.uint_to_t n3)
          (FStar_UInt32.uint_to_t (Prims.of_int (24))) in
      FStar_Pervasives_Native.Some
        (FStar_UInt32.v
           (FStar_UInt32.logor b0
              (FStar_UInt32.logor b1 (FStar_UInt32.logor b2 b3))))
  | uu___ -> FStar_Pervasives_Native.None
let parse_parquet_footer_tail_hex (tail : Prims.string) :
  parquet_footer FStar_Pervasives_Native.option=
  let len = FStar_String.strlen tail in
  if len < (Prims.of_int (16))
  then FStar_Pervasives_Native.None
  else
    (let magic =
       FStar_String.sub tail (len - (Prims.of_int (8))) (Prims.of_int (8)) in
     if magic <> parquet_magic_hex
     then FStar_Pervasives_Native.None
     else
       (let footer_start = len - (Prims.of_int (16)) in
        match le_u32_at_hex tail footer_start with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some meta_len ->
            FStar_Pervasives_Native.Some
              {
                pf_metadata_len = meta_len;
                pf_footer_len = (meta_len + (Prims.of_int (8)));
                pf_magic = parquet_magic
              }))
let is_printable_byte (b : Prims.nat) : Prims.bool=
  (b >= (Prims.of_int (32))) && (b <= (Prims.of_int (126)))
let finish_ascii_run (current : FStar_Char.char Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  if (FStar_List_Tot_Base.length current) = Prims.int_zero
  then acc
  else (FStar_String.string_of_list (FStar_List_Tot_Base.rev current)) :: acc
let rec extract_ascii_strings_hex (hex : Prims.string) (pos : Prims.nat)
  (current : FStar_Char.char Prims.list) (acc : Prims.string Prims.list) :
  Prims.string Prims.list=
  if (pos + Prims.int_one) >= (FStar_String.strlen hex)
  then FStar_List_Tot_Base.rev (finish_ascii_run current acc)
  else
    (match byte_at_hex hex pos with
     | FStar_Pervasives_Native.None ->
         FStar_List_Tot_Base.rev (finish_ascii_run current acc)
     | FStar_Pervasives_Native.Some b ->
         if is_printable_byte b
         then
           extract_ascii_strings_hex hex (pos + (Prims.of_int (2)))
             ((FStar_Char.char_of_int b) :: current) acc
         else
           extract_ascii_strings_hex hex (pos + (Prims.of_int (2))) []
             (finish_ascii_run current acc))
let probe_parquet_footer (path : Prims.string) :
  parquet_footer FStar_Pervasives_Native.option=
  match parquet_read_tail_hex path (Prims.of_int (8)) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some tail -> parse_parquet_footer_tail_hex tail
let probe_parquet_metadata_strings (path : Prims.string) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             FStar_Pervasives_Native.Some
               (extract_ascii_strings_hex
                  (FStar_String.sub footer_hex Prims.int_zero meta_hex_len)
                  Prims.int_zero [] [])
           else FStar_Pervasives_Native.None)
let compact_t_stop : Prims.nat= Prims.int_zero
let compact_t_bool_true : Prims.nat= Prims.int_one
let compact_t_bool_false : Prims.nat= (Prims.of_int (2))
let compact_t_byte : Prims.nat= (Prims.of_int (3))
let compact_t_i16 : Prims.nat= (Prims.of_int (4))
let compact_t_i32 : Prims.nat= (Prims.of_int (5))
let compact_t_i64 : Prims.nat= (Prims.of_int (6))
let compact_t_double : Prims.nat= (Prims.of_int (7))
let compact_t_binary : Prims.nat= (Prims.of_int (8))
let compact_t_list : Prims.nat= (Prims.of_int (9))
let compact_t_set : Prims.nat= (Prims.of_int (10))
let compact_t_map : Prims.nat= (Prims.of_int (11))
let compact_t_struct : Prims.nat= (Prims.of_int (12))
let high_nibble (b : Prims.nat) : Prims.nat=
  FStar_UInt32.v
    (FStar_UInt32.shift_right (FStar_UInt32.uint_to_t b)
       (FStar_UInt32.uint_to_t (Prims.of_int (4))))
let low_nibble (b : Prims.nat) : Prims.nat=
  FStar_UInt32.v
    (FStar_UInt32.logand (FStar_UInt32.uint_to_t b)
       (FStar_UInt32.uint_to_t (Prims.of_int (15))))
let low_7_bits (b : Prims.nat) : Prims.nat=
  FStar_UInt32.v
    (FStar_UInt32.logand (FStar_UInt32.uint_to_t b)
       (FStar_UInt32.uint_to_t (Prims.of_int (127))))
let rec scale_pow2 (x : Prims.nat) (shift : Prims.nat) : Prims.nat=
  if shift = Prims.int_zero
  then x
  else scale_pow2 (x + x) (shift - Prims.int_one)
let rec mul_nat (x : Prims.nat) (y : Prims.nat) : Prims.nat=
  if y = Prims.int_zero
  then Prims.int_zero
  else x + (mul_nat x (y - Prims.int_one))
let pred_nat (n : Prims.nat) : Prims.nat= n - Prims.int_one
let succ_nat (n : Prims.nat) : Prims.nat= n + Prims.int_one
let div_nat_pos (x : Prims.nat) (y : Prims.nat) : Prims.nat= x / y
let le_u24_at_hex (s : Prims.string) (start : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((byte_at_hex s start), (byte_at_hex s (start + (Prims.of_int (2)))),
          (byte_at_hex s (start + (Prims.of_int (4)))))
  with
  | (FStar_Pervasives_Native.Some n0, FStar_Pervasives_Native.Some n1,
     FStar_Pervasives_Native.Some n2) ->
      FStar_Pervasives_Native.Some
        ((n0 + (scale_pow2 n1 (Prims.of_int (8)))) +
           (scale_pow2 n2 (Prims.of_int (16))))
  | uu___ -> FStar_Pervasives_Native.None
let rec skip_varint_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some b ->
           let next = pos + (Prims.of_int (2)) in
           if b < (Prims.of_int (128))
           then FStar_Pervasives_Native.Some next
           else skip_varint_hex hex next (fuel - Prims.int_one))
let rec skip_n_values_hex (hex : Prims.string) (etype : Prims.nat)
  (count : Prims.nat) (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if count = Prims.int_zero
    then FStar_Pervasives_Native.Some pos
    else
      (match skip_compact_value_hex hex etype pos (fuel - Prims.int_one) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some next ->
           skip_n_values_hex hex etype (count - Prims.int_one) next
             (fuel - Prims.int_one))
and skip_struct_fields_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some header ->
           if header = compact_t_stop
           then FStar_Pervasives_Native.Some (pos + (Prims.of_int (2)))
           else
             (let ftype = low_nibble header in
              let delta = high_nibble header in
              let value_pos =
                if delta = Prims.int_zero
                then
                  match skip_varint_hex hex (pos + (Prims.of_int (2)))
                          (fuel - Prims.int_one)
                  with
                  | FStar_Pervasives_Native.Some p -> p
                  | FStar_Pervasives_Native.None -> pos + (Prims.of_int (2))
                else pos + (Prims.of_int (2)) in
              if
                (delta = Prims.int_zero) &&
                  (value_pos = (pos + (Prims.of_int (2))))
              then FStar_Pervasives_Native.None
              else
                (match skip_compact_value_hex hex ftype value_pos
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some next ->
                     skip_struct_fields_hex hex next (fuel - Prims.int_one))))
and skip_compact_value_hex (hex : Prims.string) (ftype : Prims.nat)
  (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (ftype = compact_t_bool_true) || (ftype = compact_t_bool_false)
    then FStar_Pervasives_Native.Some pos
    else
      if ftype = compact_t_byte
      then
        (if (pos + Prims.int_one) < (FStar_String.strlen hex)
         then FStar_Pervasives_Native.Some (pos + (Prims.of_int (2)))
         else FStar_Pervasives_Native.None)
      else
        if
          ((ftype = compact_t_i16) || (ftype = compact_t_i32)) ||
            (ftype = compact_t_i64)
        then skip_varint_hex hex pos (fuel - Prims.int_one)
        else
          if ftype = compact_t_double
          then
            (if (pos + (Prims.of_int (15))) < (FStar_String.strlen hex)
             then FStar_Pervasives_Native.Some (pos + (Prims.of_int (16)))
             else FStar_Pervasives_Native.None)
          else
            if ftype = compact_t_binary
            then
              (match skip_varint_hex hex pos (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some len_end ->
                   let rec decode_varint_hex p shift acc fuel2 =
                     if fuel2 = Prims.int_zero
                     then FStar_Pervasives_Native.None
                     else
                       if (p + Prims.int_one) >= (FStar_String.strlen hex)
                       then FStar_Pervasives_Native.None
                       else
                         (match byte_at_hex hex p with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let payload = low_7_bits b in
                              let acc' = acc + (scale_pow2 payload shift) in
                              if b < (Prims.of_int (128))
                              then FStar_Pervasives_Native.Some acc'
                              else
                                decode_varint_hex (p + (Prims.of_int (2)))
                                  (shift + (Prims.of_int (7))) acc'
                                  (fuel2 - Prims.int_one)) in
                   (match decode_varint_hex pos Prims.int_zero Prims.int_zero
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some blen ->
                        let data_end = len_end + (blen + blen) in
                        if data_end <= (FStar_String.strlen hex)
                        then FStar_Pervasives_Native.Some data_end
                        else FStar_Pervasives_Native.None))
            else
              if (ftype = compact_t_list) || (ftype = compact_t_set)
              then
                (if (pos + Prims.int_one) >= (FStar_String.strlen hex)
                 then FStar_Pervasives_Native.None
                 else
                   (match byte_at_hex hex pos with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some header ->
                        let size_nibble = high_nibble header in
                        let etype = low_nibble header in
                        if size_nibble < (Prims.of_int (15))
                        then
                          skip_n_values_hex hex etype size_nibble
                            (pos + (Prims.of_int (2))) (fuel - Prims.int_one)
                        else
                          (let rec decode_varint_hex p shift acc fuel2 =
                             if fuel2 = Prims.int_zero
                             then FStar_Pervasives_Native.None
                             else
                               if
                                 (p + Prims.int_one) >=
                                   (FStar_String.strlen hex)
                               then FStar_Pervasives_Native.None
                               else
                                 (match byte_at_hex hex p with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some b ->
                                      let payload = low_7_bits b in
                                      let acc' =
                                        acc + (scale_pow2 payload shift) in
                                      if b < (Prims.of_int (128))
                                      then
                                        FStar_Pervasives_Native.Some
                                          (acc', (p + (Prims.of_int (2))))
                                      else
                                        decode_varint_hex
                                          (p + (Prims.of_int (2)))
                                          (shift + (Prims.of_int (7))) acc'
                                          (fuel2 - Prims.int_one)) in
                           match decode_varint_hex (pos + (Prims.of_int (2)))
                                   Prims.int_zero Prims.int_zero
                                   (fuel - Prims.int_one)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some
                               (count, after_count) ->
                               skip_n_values_hex hex etype count after_count
                                 (fuel - Prims.int_one))))
              else
                if ftype = compact_t_struct
                then skip_struct_fields_hex hex pos (fuel - Prims.int_one)
                else
                  if ftype = compact_t_map
                  then FStar_Pervasives_Native.None
                  else FStar_Pervasives_Native.None
let zigzag_decode_nat (n : Prims.nat) : Prims.nat= n / (Prims.of_int (2))
let zigzag_decode_int (n : Prims.nat) : Prims.int=
  if ((mod) n (Prims.of_int (2))) = Prims.int_zero
  then n / (Prims.of_int (2))
  else Prims.int_zero - ((n / (Prims.of_int (2))) + Prims.int_one)
let rec decode_varint_value_with_end_hex (hex : Prims.string) (p : Prims.nat)
  (shift : Prims.nat) (acc : Prims.nat) (fuel : Prims.nat) :
  (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (p + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some b ->
           let payload = low_7_bits b in
           let acc' = acc + (scale_pow2 payload shift) in
           if b < (Prims.of_int (128))
           then FStar_Pervasives_Native.Some (acc', (p + (Prims.of_int (2))))
           else
             decode_varint_value_with_end_hex hex (p + (Prims.of_int (2)))
               (shift + (Prims.of_int (7))) acc' (fuel - Prims.int_one))
let rec decode_varint_value_hex (hex : Prims.string) (p : Prims.nat)
  (shift : Prims.nat) (acc : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match decode_varint_value_with_end_hex hex p shift acc fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (n, uu___) -> FStar_Pervasives_Native.Some n
let decode_compact_list_info_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : compact_list_info FStar_Pervasives_Native.option=
  if (pos + Prims.int_one) >= (FStar_String.strlen hex)
  then FStar_Pervasives_Native.None
  else
    (match byte_at_hex hex pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some header ->
         let count_nibble = high_nibble header in
         let etype = low_nibble header in
         if count_nibble < (Prims.of_int (15))
         then
           FStar_Pervasives_Native.Some
             {
               cli_count = count_nibble;
               cli_etype = etype;
               cli_payload_start = (pos + (Prims.of_int (2)))
             }
         else
           (match decode_varint_value_with_end_hex hex
                    (pos + (Prims.of_int (2))) Prims.int_zero Prims.int_zero
                    fuel
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (count, payload_start) ->
                FStar_Pervasives_Native.Some
                  {
                    cli_count = count;
                    cli_etype = etype;
                    cli_payload_start = payload_start
                  }))
let decode_compact_list_count_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match decode_compact_list_info_hex hex pos fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some info ->
      FStar_Pervasives_Native.Some (info.cli_count)
let decode_compact_binary_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match decode_varint_value_with_end_hex hex pos Prims.int_zero
          Prims.int_zero fuel
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (blen, payload_start) ->
      let chars_hex_len = blen + blen in
      let payload_end = payload_start + chars_hex_len in
      if payload_end > (FStar_String.strlen hex)
      then FStar_Pervasives_Native.None
      else
        (let rec build_chars p remaining acc =
           if remaining = Prims.int_zero
           then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
           else
             if (p + Prims.int_one) >= payload_end
             then FStar_Pervasives_Native.None
             else
               (match byte_at_hex hex p with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some b ->
                    build_chars (p + (Prims.of_int (2)))
                      (remaining - Prims.int_one) ((FStar_Char.char_of_int b)
                      :: acc)) in
         match build_chars payload_start blen [] with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some chars ->
             FStar_Pervasives_Native.Some (FStar_String.string_of_list chars))
let nth_compact_list_element_start_hex (hex : Prims.string)
  (list_pos : Prims.nat) (index : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match decode_compact_list_info_hex hex list_pos fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some info ->
      if index >= info.cli_count
      then FStar_Pervasives_Native.None
      else
        (let rec loop remaining p fuel2 =
           if fuel2 = Prims.int_zero
           then FStar_Pervasives_Native.None
           else
             if remaining = Prims.int_zero
             then FStar_Pervasives_Native.Some p
             else
               (match skip_compact_value_hex hex info.cli_etype p
                        (fuel2 - Prims.int_one)
                with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some next ->
                    loop (remaining - Prims.int_one) next
                      (fuel2 - Prims.int_one)) in
         loop index info.cli_payload_start fuel)
let rec nth_field_hex (hex : Prims.string) (target_id : Prims.nat)
  (pos : Prims.nat) (prev_id : Prims.nat) (fuel : Prims.nat) :
  compact_field FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some header ->
           if header = compact_t_stop
           then FStar_Pervasives_Native.None
           else
             (let ftype = low_nibble header in
              let delta = high_nibble header in
              let rec decode_varint_hex p shift acc fuel2 =
                if fuel2 = Prims.int_zero
                then FStar_Pervasives_Native.None
                else
                  if (p + Prims.int_one) >= (FStar_String.strlen hex)
                  then FStar_Pervasives_Native.None
                  else
                    (match byte_at_hex hex p with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some b ->
                         let payload = low_7_bits b in
                         let acc' = acc + (scale_pow2 payload shift) in
                         if b < (Prims.of_int (128))
                         then
                           FStar_Pervasives_Native.Some
                             (acc', (p + (Prims.of_int (2))))
                         else
                           decode_varint_hex (p + (Prims.of_int (2)))
                             (shift + (Prims.of_int (7))) acc'
                             (fuel2 - Prims.int_one)) in
              let field_id_opt =
                if delta = Prims.int_zero
                then
                  match decode_varint_hex (pos + (Prims.of_int (2)))
                          Prims.int_zero Prims.int_zero
                          (fuel - Prims.int_one)
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (fid, uu___3) ->
                      FStar_Pervasives_Native.Some fid
                else FStar_Pervasives_Native.Some (prev_id + delta) in
              let value_pos_opt =
                if delta = Prims.int_zero
                then
                  match decode_varint_hex (pos + (Prims.of_int (2)))
                          Prims.int_zero Prims.int_zero
                          (fuel - Prims.int_one)
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (uu___3, p) ->
                      FStar_Pervasives_Native.Some p
                else FStar_Pervasives_Native.Some (pos + (Prims.of_int (2))) in
              match (field_id_opt, value_pos_opt) with
              | (FStar_Pervasives_Native.Some field_id,
                 FStar_Pervasives_Native.Some value_pos) ->
                  (match skip_compact_value_hex hex ftype value_pos
                           (fuel - Prims.int_one)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some next ->
                       if field_id = target_id
                       then
                         FStar_Pervasives_Native.Some
                           {
                             cf_id = field_id;
                             cf_type = ftype;
                             cf_value_start = value_pos;
                             cf_next = next
                           }
                       else
                         nth_field_hex hex target_id next field_id
                           (fuel - Prims.int_one))
              | uu___3 -> FStar_Pervasives_Native.None))
let probe_parquet_num_rows (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (3)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_i64
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_varint_value_hex meta_hex
                             field.cf_value_start Prims.int_zero
                             Prims.int_zero meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some raw ->
                         FStar_Pervasives_Native.Some (zigzag_decode_nat raw)))
           else FStar_Pervasives_Native.None)
let probe_parquet_row_group_count (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    decode_compact_list_count_hex meta_hex
                      field.cf_value_start meta_hex_len)
           else FStar_Pervasives_Native.None)
let probe_parquet_first_row_group_num_rows (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some info ->
                         if
                           (info.cli_count = Prims.int_zero) ||
                             (info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex (Prims.of_int (3))
                                    info.cli_payload_start Prims.int_zero
                                    meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some row_group_field ->
                                if row_group_field.cf_type <> compact_t_i64
                                then FStar_Pervasives_Native.None
                                else
                                  (match decode_varint_value_hex meta_hex
                                           row_group_field.cf_value_start
                                           Prims.int_zero Prims.int_zero
                                           meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some raw ->
                                       FStar_Pervasives_Native.Some
                                         (zigzag_decode_nat raw)))))
           else FStar_Pervasives_Native.None)
let probe_parquet_first_row_group_column_count (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some info ->
                         if
                           (info.cli_count = Prims.int_zero) ||
                             (info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    info.cli_payload_start Prims.int_zero
                                    meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some row_group_field ->
                                if row_group_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  decode_compact_list_count_hex meta_hex
                                    row_group_field.cf_value_start
                                    meta_hex_len)))
           else FStar_Pervasives_Native.None)
let probe_parquet_first_column_name (path : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           Prims.int_zero meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (3))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   path_field ->
                                                   if
                                                     path_field.cf_type <>
                                                       compact_t_list
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match nth_compact_list_element_start_hex
                                                              meta_hex
                                                              path_field.cf_value_start
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          path_start ->
                                                          decode_compact_binary_hex
                                                            meta_hex
                                                            path_start
                                                            meta_hex_len)))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_first_column_data_page_offset (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           Prims.int_zero meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (9))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   offset_field ->
                                                   if
                                                     offset_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              offset_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_name (path : Prims.string) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (3))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   path_field ->
                                                   if
                                                     path_field.cf_type <>
                                                       compact_t_list
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match nth_compact_list_element_start_hex
                                                              meta_hex
                                                              path_field.cf_value_start
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          path_start ->
                                                          decode_compact_binary_hex
                                                            meta_hex
                                                            path_start
                                                            meta_hex_len)))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_num_values (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (5))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   num_values_field ->
                                                   if
                                                     num_values_field.cf_type
                                                       <> compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              num_values_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_total_compressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (7))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   size_field ->
                                                   if
                                                     size_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              size_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_total_uncompressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (6))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   size_field ->
                                                   if
                                                     size_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              size_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let parquet_compression_codec_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "UNCOMPRESSED"
  else
    if n = Prims.int_one
    then "SNAPPY"
    else
      if n = (Prims.of_int (2))
      then "GZIP"
      else
        if n = (Prims.of_int (3))
        then "LZO"
        else
          if n = (Prims.of_int (4))
          then "BROTLI"
          else
            if n = (Prims.of_int (5))
            then "LZ4"
            else
              if n = (Prims.of_int (6))
              then "ZSTD"
              else if n = (Prims.of_int (7)) then "LZ4_RAW" else "UNKNOWN"
let probe_parquet_column_compression_codec (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (4))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   codec_field ->
                                                   if
                                                     codec_field.cf_type <>
                                                       compact_t_i32
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              codec_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (parquet_compression_codec_name
                                                               (zigzag_decode_nat
                                                                  raw)))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_data_page_offset (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (9))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   offset_field ->
                                                   if
                                                     offset_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              offset_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let parquet_page_type_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "DATA_PAGE"
  else
    if n = Prims.int_one
    then "INDEX_PAGE"
    else
      if n = (Prims.of_int (2))
      then "DICTIONARY_PAGE"
      else if n = (Prims.of_int (3)) then "DATA_PAGE_V2" else "UNKNOWN"
let parquet_encoding_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "PLAIN"
  else
    if n = Prims.int_one
    then "GROUP_VAR_INT"
    else
      if n = (Prims.of_int (2))
      then "PLAIN_DICTIONARY"
      else
        if n = (Prims.of_int (3))
        then "RLE"
        else
          if n = (Prims.of_int (4))
          then "BIT_PACKED"
          else
            if n = (Prims.of_int (5))
            then "DELTA_BINARY_PACKED"
            else
              if n = (Prims.of_int (6))
              then "DELTA_LENGTH_BYTE_ARRAY"
              else
                if n = (Prims.of_int (7))
                then "DELTA_BYTE_ARRAY"
                else
                  if n = (Prims.of_int (8))
                  then "RLE_DICTIONARY"
                  else
                    if n = (Prims.of_int (9))
                    then "BYTE_STREAM_SPLIT"
                    else "UNKNOWN"
let rec nat_mod (x : Prims.nat) (y : Prims.nat) : Prims.nat=
  if x < y then x else nat_mod (x - y) y
let zstd_block_type_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "RAW"
  else
    if n = Prims.int_one
    then "RLE"
    else
      if n = (Prims.of_int (2))
      then "COMPRESSED"
      else if n = (Prims.of_int (3)) then "RESERVED" else "UNKNOWN"
let zstd_frame_content_size_field_bytes (descriptor : Prims.nat) : Prims.nat=
  let fcs_flag = descriptor / (Prims.of_int (64)) in
  let single_segment =
    nat_mod (descriptor / (Prims.of_int (32))) (Prims.of_int (2)) in
  if fcs_flag = Prims.int_zero
  then
    (if single_segment = Prims.int_one then Prims.int_one else Prims.int_zero)
  else
    if fcs_flag = Prims.int_one
    then (Prims.of_int (2))
    else
      if fcs_flag = (Prims.of_int (2))
      then (Prims.of_int (4))
      else (Prims.of_int (8))
let zstd_dictionary_id_field_bytes (descriptor : Prims.nat) : Prims.nat=
  let did_flag = nat_mod descriptor (Prims.of_int (4)) in
  if did_flag = Prims.int_zero
  then Prims.int_zero
  else
    if did_flag = Prims.int_one
    then Prims.int_one
    else
      if did_flag = (Prims.of_int (2))
      then (Prims.of_int (2))
      else (Prims.of_int (4))
let zstd_window_descriptor_bytes (descriptor : Prims.nat) : Prims.nat=
  let single_segment =
    nat_mod (descriptor / (Prims.of_int (32))) (Prims.of_int (2)) in
  if single_segment = Prims.int_one then Prims.int_zero else Prims.int_one
let probe_parquet_column_page_header_type (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex Prims.int_one Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some type_field ->
                if type_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex page_hex
                           type_field.cf_value_start Prims.int_zero
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some
                         (parquet_page_type_name (zigzag_decode_nat raw)))))
let probe_parquet_column_page_header_uncompressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (2)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some size_field ->
                if size_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex page_hex
                           size_field.cf_value_start Prims.int_zero
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_page_header_compressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (3)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some size_field ->
                if size_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex page_hex
                           size_field.cf_value_start Prims.int_zero
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_page_header_num_values (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex Prims.int_one
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some num_values_field ->
                       if num_values_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  num_values_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (zigzag_decode_nat raw)))))
let probe_parquet_column_page_header_length (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match skip_struct_fields_hex page_hex Prims.int_zero
                    (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some end_hex ->
                FStar_Pervasives_Native.Some (end_hex / (Prims.of_int (2)))))
let probe_parquet_column_page_payload_offset (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_data_page_offset path col_index),
          (probe_parquet_column_page_header_length path col_index))
  with
  | (FStar_Pervasives_Native.Some page_offset, FStar_Pervasives_Native.Some
     header_len) -> FStar_Pervasives_Native.Some (page_offset + header_len)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_page_header_data_encoding (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (2))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_page_header_definition_level_encoding
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (3))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_page_header_repetition_level_encoding
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (4))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_page_payload_magic_hex (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match parquet_read_range_hex path payload_offset (Prims.of_int (4))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some payload_hex ->
           if (FStar_String.strlen payload_hex) >= (Prims.of_int (8))
           then
             FStar_Pervasives_Native.Some
               (FStar_String.sub payload_hex Prims.int_zero
                  (Prims.of_int (8)))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_zstd_frame_header_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match parquet_read_range_hex path payload_offset (Prims.of_int (18))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some payload_hex ->
           if (FStar_String.strlen payload_hex) < (Prims.of_int (10))
           then FStar_Pervasives_Native.None
           else
             (match byte_at_hex payload_hex (Prims.of_int (8)) with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some descriptor ->
                  FStar_Pervasives_Native.Some
                    ((((Prims.of_int (5)) +
                         (zstd_window_descriptor_bytes descriptor))
                        + (zstd_dictionary_id_field_bytes descriptor))
                       + (zstd_frame_content_size_field_bytes descriptor))))
let probe_parquet_column_zstd_first_block_type (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_zstd_frame_header_size path col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some frame_header_size ->
           (match parquet_read_range_hex path
                    (payload_offset + frame_header_size) (Prims.of_int (3))
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some block_hex ->
                if (FStar_String.strlen block_hex) < (Prims.of_int (6))
                then FStar_Pervasives_Native.None
                else
                  (match le_u24_at_hex block_hex Prims.int_zero with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some block_header ->
                       let block_type =
                         nat_mod (block_header / (Prims.of_int (2)))
                           (Prims.of_int (4)) in
                       FStar_Pervasives_Native.Some
                         (zstd_block_type_name block_type))))
let probe_parquet_column_zstd_first_block_last_flag (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_zstd_frame_header_size path col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some frame_header_size ->
           (match parquet_read_range_hex path
                    (payload_offset + frame_header_size) (Prims.of_int (3))
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some block_hex ->
                if (FStar_String.strlen block_hex) < (Prims.of_int (6))
                then FStar_Pervasives_Native.None
                else
                  (match le_u24_at_hex block_hex Prims.int_zero with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some block_header ->
                       FStar_Pervasives_Native.Some
                         (nat_mod block_header (Prims.of_int (2))))))
let probe_parquet_column_zstd_first_block_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_zstd_frame_header_size path col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some frame_header_size ->
           (match parquet_read_range_hex path
                    (payload_offset + frame_header_size) (Prims.of_int (3))
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some block_hex ->
                if (FStar_String.strlen block_hex) < (Prims.of_int (6))
                then FStar_Pervasives_Native.None
                else
                  (match le_u24_at_hex block_hex Prims.int_zero with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some block_header ->
                       FStar_Pervasives_Native.Some
                         (block_header / (Prims.of_int (8))))))
let probe_parquet_column_zstd_first_block_header_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_zstd_first_block_type path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some uu___ ->
      FStar_Pervasives_Native.Some (Prims.of_int (3))
let probe_parquet_column_zstd_first_block_payload_offset
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_page_payload_offset path col_index),
          (probe_parquet_column_zstd_frame_header_size path col_index),
          (probe_parquet_column_zstd_first_block_header_size path col_index))
  with
  | (FStar_Pervasives_Native.Some payload_offset,
     FStar_Pervasives_Native.Some frame_header_size,
     FStar_Pervasives_Native.Some block_header_size) ->
      FStar_Pervasives_Native.Some
        ((payload_offset + frame_header_size) + block_header_size)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_zstd_frame_accounted_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_zstd_frame_header_size path col_index),
          (probe_parquet_column_zstd_first_block_header_size path col_index),
          (probe_parquet_column_zstd_first_block_size path col_index))
  with
  | (FStar_Pervasives_Native.Some frame_header_size,
     FStar_Pervasives_Native.Some block_header_size,
     FStar_Pervasives_Native.Some block_size) ->
      FStar_Pervasives_Native.Some
        ((frame_header_size + block_header_size) + block_size)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_zstd_frame_size_matches_page (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_page_header_compressed_size path col_index),
          (probe_parquet_column_zstd_frame_accounted_size path col_index))
  with
  | (FStar_Pervasives_Native.Some page_compressed_size,
     FStar_Pervasives_Native.Some accounted) ->
      if page_compressed_size = accounted
      then FStar_Pervasives_Native.Some Prims.int_one
      else FStar_Pervasives_Native.Some Prims.int_zero
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_decompressed_payload_hex (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_page_header_compressed_size path col_index
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some compressed_size ->
           (match probe_parquet_column_page_header_uncompressed_size path
                    col_index
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some uncompressed_size ->
                (match parquet_read_range_hex path payload_offset
                         compressed_size
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some compressed_hex ->
                     parquet_zstd_decompress_hex compressed_hex
                       uncompressed_size)))
let probe_parquet_column_decompressed_payload_prefix_hex
  (path : Prims.string) (col_index : Prims.nat) (prefix_bytes : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      let want = prefix_bytes + prefix_bytes in
      if want <= (FStar_String.strlen payload_hex)
      then
        FStar_Pervasives_Native.Some
          (FStar_String.sub payload_hex Prims.int_zero want)
      else FStar_Pervasives_Native.Some payload_hex
let probe_parquet_column_decompressed_payload_hex_length
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      FStar_Pervasives_Native.Some
        ((FStar_String.strlen payload_hex) / (Prims.of_int (2)))
let probe_parquet_column_first_level_section_length (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      if (FStar_String.strlen payload_hex) < (Prims.of_int (8))
      then FStar_Pervasives_Native.None
      else le_u32_at_hex payload_hex Prims.int_zero
let probe_parquet_column_delta_length_byte_array_values_offset
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_first_level_section_length path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some section_len ->
      FStar_Pervasives_Native.Some ((Prims.of_int (4)) + section_len)
let probe_parquet_column_delta_length_byte_array_values_prefix_hex
  (path : Prims.string) (col_index : Prims.nat) (prefix_bytes : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex path col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset path
             col_index))
  with
  | (FStar_Pervasives_Native.Some payload_hex, FStar_Pervasives_Native.Some
     value_offset) ->
      let start = value_offset + value_offset in
      if start > (FStar_String.strlen payload_hex)
      then FStar_Pervasives_Native.None
      else
        (let remaining = (FStar_String.strlen payload_hex) - start in
         let want = prefix_bytes + prefix_bytes in
         let take = if want <= remaining then want else remaining in
         FStar_Pervasives_Native.Some
           (FStar_String.sub payload_hex start take))
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_delta_length_byte_array_block_size
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (n, uu___) ->
           FStar_Pervasives_Native.Some n)
let probe_parquet_column_delta_length_byte_array_miniblock_count
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (n, uu___1) ->
                FStar_Pervasives_Native.Some n))
let probe_parquet_column_delta_length_byte_array_value_count
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (n, uu___2) ->
                     FStar_Pervasives_Native.Some n)))
let probe_parquet_column_delta_length_byte_array_first_length
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (raw, uu___3) ->
                          FStar_Pervasives_Native.Some
                            (zigzag_decode_nat raw)))))
let probe_parquet_column_delta_length_byte_array_first_min_delta
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.int FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (64))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (uu___3, p4) ->
                          (match decode_varint_value_with_end_hex values_hex
                                   p4 Prims.int_zero Prims.int_zero
                                   (FStar_String.strlen values_hex)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (raw, uu___4) ->
                               FStar_Pervasives_Native.Some
                                 (zigzag_decode_int raw))))))
let probe_parquet_column_delta_length_byte_array_first_bit_width
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (64))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (uu___3, p4) ->
                          (match decode_varint_value_with_end_hex values_hex
                                   p4 Prims.int_zero Prims.int_zero
                                   (FStar_String.strlen values_hex)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uu___4, p5) ->
                               if
                                 (p5 + Prims.int_one) >=
                                   (FStar_String.strlen values_hex)
                               then FStar_Pervasives_Native.None
                               else
                                 (match byte_at_hex values_hex p5 with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some width ->
                                      FStar_Pervasives_Native.Some width))))))
let rec packed_lsb_value_hex (hex : Prims.string) (byte_start : Prims.nat)
  (start_bit : Prims.nat) (remaining : Prims.nat) (out_shift : Prims.nat)
  (acc : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    (let absolute_bit = start_bit + out_shift in
     let byte_index =
       byte_start +
         (mul_nat (absolute_bit / (Prims.of_int (8))) (Prims.of_int (2))) in
     if (byte_index + Prims.int_one) >= (FStar_String.strlen hex)
     then FStar_Pervasives_Native.None
     else
       (match byte_at_hex hex byte_index with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some b ->
            let bit_in_byte = (mod) absolute_bit (Prims.of_int (8)) in
            let bit =
              (mod) (b / (scale_pow2 Prims.int_one bit_in_byte))
                (Prims.of_int (2)) in
            let acc' =
              if bit = Prims.int_zero
              then acc
              else acc + (scale_pow2 Prims.int_one out_shift) in
            packed_lsb_value_hex hex byte_start start_bit
              (remaining - Prims.int_one) (out_shift + Prims.int_one) acc'))
let probe_parquet_column_delta_length_byte_array_length_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.int FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (96))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (first_raw, p4) ->
                          let first_len = zigzag_decode_int first_raw in
                          if value_index = Prims.int_zero
                          then FStar_Pervasives_Native.Some first_len
                          else
                            (match decode_varint_value_with_end_hex
                                     values_hex p4 Prims.int_zero
                                     Prims.int_zero
                                     (FStar_String.strlen values_hex)
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some
                                 (min_delta_raw, p5) ->
                                 let min_delta =
                                   zigzag_decode_int min_delta_raw in
                                 if
                                   (p5 + Prims.int_one) >=
                                     (FStar_String.strlen values_hex)
                                 then FStar_Pervasives_Native.None
                                 else
                                   (match byte_at_hex values_hex p5 with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.None
                                    | FStar_Pervasives_Native.Some width ->
                                        let packed_start =
                                          p5 + (Prims.of_int (16)) in
                                        let rec accumulate_lengths
                                          delta_index current =
                                          if delta_index >= value_index
                                          then
                                            FStar_Pervasives_Native.Some
                                              current
                                          else
                                            (let start_bit =
                                               mul_nat delta_index width in
                                             match packed_lsb_value_hex
                                                     values_hex packed_start
                                                     start_bit width
                                                     Prims.int_zero
                                                     Prims.int_zero
                                             with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some
                                                 adjusted ->
                                                 let next =
                                                   (current + min_delta) +
                                                     adjusted in
                                                 let delta_index' =
                                                   succ_nat delta_index in
                                                 accumulate_lengths
                                                   delta_index' next) in
                                        accumulate_lengths Prims.int_zero
                                          first_len))))))
let rec count_used_miniblocks (remaining : Prims.nat)
  (values_per_miniblock : Prims.nat) : Prims.nat=
  if remaining = Prims.int_zero
  then Prims.int_zero
  else
    if remaining <= values_per_miniblock
    then Prims.int_one
    else
      succ_nat
        (count_used_miniblocks (remaining - values_per_miniblock)
           values_per_miniblock)
let probe_parquet_column_delta_length_byte_array_length_nat_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_length_at path col_index
          value_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some n ->
      if n < Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some n
let probe_parquet_column_delta_length_byte_array_total_value_bytes
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_value_count path
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some value_count ->
      let rec loop remaining idx acc =
        if remaining = Prims.int_zero
        then FStar_Pervasives_Native.Some acc
        else
          (match probe_parquet_column_delta_length_byte_array_length_nat_at
                   path col_index idx
           with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some len ->
               loop (pred_nat remaining) (succ_nat idx) (acc + len)) in
      loop value_count Prims.int_zero Prims.int_zero
let probe_parquet_column_delta_length_byte_array_value_data_offset
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex_length path col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset path
             col_index),
          (probe_parquet_column_delta_length_byte_array_total_value_bytes
             path col_index))
  with
  | (FStar_Pervasives_Native.Some payload_len, FStar_Pervasives_Native.Some
     values_offset, FStar_Pervasives_Native.Some total_value_bytes) ->
      if values_offset > payload_len
      then FStar_Pervasives_Native.None
      else
        (let values_stream_len = payload_len - values_offset in
         if total_value_bytes > values_stream_len
         then FStar_Pervasives_Native.None
         else
           FStar_Pervasives_Native.Some
             (values_stream_len - total_value_bytes))
  | uu___ -> FStar_Pervasives_Native.None
let rec ascii_string_of_hex_slice (hex : Prims.string) (pos : Prims.nat)
  (remaining : Prims.nat) (acc : FStar_Char.char Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then
    FStar_Pervasives_Native.Some
      (FStar_String.string_of_list (FStar_List_Tot_Base.rev acc))
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some b ->
           ascii_string_of_hex_slice hex (pos + (Prims.of_int (2)))
             (remaining - Prims.int_one) ((FStar_Char.char_of_int b) :: acc))
let probe_parquet_column_delta_length_byte_array_value_hex_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex path col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset path
             col_index),
          (probe_parquet_column_delta_length_byte_array_value_data_offset
             path col_index))
  with
  | (FStar_Pervasives_Native.Some payload_hex, FStar_Pervasives_Native.Some
     values_offset, FStar_Pervasives_Native.Some value_data_offset) ->
      let values_start = values_offset + value_data_offset in
      let rec sum_previous_lengths remaining idx acc =
        if remaining = Prims.int_zero
        then FStar_Pervasives_Native.Some acc
        else
          (match probe_parquet_column_delta_length_byte_array_length_nat_at
                   path col_index idx
           with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some len ->
               sum_previous_lengths (pred_nat remaining) (succ_nat idx)
                 (acc + len)) in
      (match ((sum_previous_lengths value_index Prims.int_zero Prims.int_zero),
               (probe_parquet_column_delta_length_byte_array_length_nat_at
                  path col_index value_index))
       with
       | (FStar_Pervasives_Native.Some prior_len,
          FStar_Pervasives_Native.Some value_len) ->
           let start_byte = values_start + prior_len in
           let start = mul_nat start_byte (Prims.of_int (2)) in
           let want = mul_nat value_len (Prims.of_int (2)) in
           if (start + want) <= (FStar_String.strlen payload_hex)
           then
             FStar_Pervasives_Native.Some
               (FStar_String.sub payload_hex start want)
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_delta_length_byte_array_value_string_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_value_hex_at path
          col_index value_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some value_hex ->
      ascii_string_of_hex_slice value_hex Prims.int_zero
        ((FStar_String.strlen value_hex) / (Prims.of_int (2))) []
