open Prims
type cottas_quad =
  {
  cq_s: Prims.string ;
  cq_p: Prims.string ;
  cq_o: Prims.string ;
  cq_g: Prims.string }
let __proj__Mkcottas_quad__item__cq_s (projectee : cottas_quad) :
  Prims.string= match projectee with | { cq_s; cq_p; cq_o; cq_g;_} -> cq_s
let __proj__Mkcottas_quad__item__cq_p (projectee : cottas_quad) :
  Prims.string= match projectee with | { cq_s; cq_p; cq_o; cq_g;_} -> cq_p
let __proj__Mkcottas_quad__item__cq_o (projectee : cottas_quad) :
  Prims.string= match projectee with | { cq_s; cq_p; cq_o; cq_g;_} -> cq_o
let __proj__Mkcottas_quad__item__cq_g (projectee : cottas_quad) :
  Prims.string= match projectee with | { cq_s; cq_p; cq_o; cq_g;_} -> cq_g
let row_group_size : Prims.nat= (Prims.parse_int "122880")
let values_per_miniblock : Prims.nat= (Prims.of_int (32))
let parquet_type_byte_array : Prims.nat= (Prims.of_int (6))
let parquet_repetition_optional : Prims.nat= Prims.int_one
let parquet_encoding_dlba : Prims.nat= (Prims.of_int (6))
let parquet_encoding_rle : Prims.nat= (Prims.of_int (3))
let parquet_codec_uncompressed : Prims.nat= Prims.int_zero
let parquet_page_type_data_page : Prims.nat= Prims.int_zero
let rec write_uvarint_rev (n : Prims.nat) (acc : RDF_Bytes.byte Prims.list) :
  RDF_Bytes.byte Prims.list=
  if n < (Prims.of_int (128))
  then (RDF_Bytes.byte_of_int n) :: acc
  else
    write_uvarint_rev (n / (Prims.of_int (128)))
      ((RDF_Bytes.byte_of_int
          ((mod) ((Prims.of_int (128)) + ((mod) n (Prims.of_int (128))))
             (Prims.of_int (256)))) :: acc)
let write_uvarint (n : Prims.nat) : RDF_Bytes.bytes=
  FStar_List_Tot_Base.rev (write_uvarint_rev n [])
let zigzag_encode_nat (n : Prims.nat) : Prims.nat= n + n
let zigzag_encode_int (v : Prims.int) : Prims.nat=
  if v >= Prims.int_zero
  then v + v
  else ((Prims.int_zero - v) + (Prims.int_zero - v)) - Prims.int_one
let write_field_header (field_type : Prims.nat) (field_id : Prims.nat)
  (prev_id : Prims.nat) : RDF_Bytes.bytes=
  if (field_id > prev_id) && ((field_id - prev_id) <= (Prims.of_int (15)))
  then
    let fld_delta = field_id - prev_id in
    let hdr =
      (((mod) fld_delta (Prims.of_int (16))) * (Prims.of_int (16))) +
        field_type in
    [RDF_Bytes.byte_of_int ((mod) hdr (Prims.of_int (256)))]
  else (RDF_Bytes.byte_of_int ((mod) field_type (Prims.of_int (256)))) ::
    (write_uvarint (zigzag_encode_nat field_id))
let write_field_i32 (field_id : Prims.nat) (prev_id : Prims.nat)
  (v : Prims.nat) : RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr
    (write_field_header Parquet_Footer.compact_t_i32 field_id prev_id)
    (write_uvarint (zigzag_encode_nat v))
let write_field_i64 (field_id : Prims.nat) (prev_id : Prims.nat)
  (v : Prims.nat) : RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr
    (write_field_header Parquet_Footer.compact_t_i64 field_id prev_id)
    (write_uvarint (zigzag_encode_nat v))
let write_field_binary (field_id : Prims.nat) (prev_id : Prims.nat)
  (s : Prims.string) : RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr
    (write_field_header Parquet_Footer.compact_t_binary field_id prev_id)
    (RDF_List_Helpers.append_tr (write_uvarint (FStar_String.strlen s))
       (RDF_Bytes.bytes_of_string s))
let write_list_header (count : Prims.nat) (etype : Prims.nat) :
  RDF_Bytes.bytes=
  if count < (Prims.of_int (15))
  then
    let hdr =
      (((mod) count (Prims.of_int (16))) * (Prims.of_int (16))) + etype in
    [RDF_Bytes.byte_of_int ((mod) hdr (Prims.of_int (256)))]
  else
    (let hdr = (Prims.of_int (240)) + etype in
     (RDF_Bytes.byte_of_int ((mod) hdr (Prims.of_int (256)))) ::
       (write_uvarint count))
let write_field_list_header (field_id : Prims.nat) (prev_id : Prims.nat)
  (count : Prims.nat) (etype : Prims.nat) : RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr
    (write_field_header Parquet_Footer.compact_t_list field_id prev_id)
    (write_list_header count etype)
let write_stop : RDF_Bytes.bytes= [RDF_Bytes.byte_of_int Prims.int_zero]
let rec list_len_acc : 'a . 'a Prims.list -> Prims.nat -> Prims.nat =
  fun xs acc ->
    match xs with
    | [] -> acc
    | uu___::tl -> list_len_acc tl (acc + Prims.int_one)
let list_len (xs : 'a Prims.list) : Prims.nat= list_len_acc xs Prims.int_zero
let rec concat_bytes_list (xs : RDF_Bytes.bytes Prims.list) :
  RDF_Bytes.bytes=
  match xs with
  | [] -> []
  | hd::tl -> RDF_List_Helpers.append_tr hd (concat_bytes_list tl)
let rec string_lengths_acc (vs : Prims.string Prims.list)
  (acc : Prims.nat Prims.list) : Prims.nat Prims.list=
  match vs with
  | [] -> FStar_List_Tot_Base.rev acc
  | v::tl -> string_lengths_acc tl ((FStar_String.strlen v) :: acc)
let string_lengths (vs : Prims.string Prims.list) : Prims.nat Prims.list=
  string_lengths_acc vs []
let rec consecutive_deltas_acc (lengths : Prims.nat Prims.list)
  (acc : Prims.int Prims.list) : Prims.int Prims.list=
  match lengths with
  | [] -> FStar_List_Tot_Base.rev acc
  | uu___::[] -> FStar_List_Tot_Base.rev acc
  | a::b::rest -> consecutive_deltas_acc (b :: rest) ((b - a) :: acc)
let consecutive_deltas (lengths : Prims.nat Prims.list) :
  Prims.int Prims.list= consecutive_deltas_acc lengths []
let rec list_min_int_acc (xs : Prims.int Prims.list) (cur : Prims.int) :
  Prims.int=
  match xs with
  | [] -> cur
  | x::tl -> list_min_int_acc tl (if x < cur then x else cur)
let min_of_int_list (xs : Prims.int Prims.list) : Prims.int=
  match xs with | [] -> Prims.int_zero | x::tl -> list_min_int_acc tl x
let rec list_max_nat_acc (xs : Prims.nat Prims.list) (cur : Prims.nat) :
  Prims.nat=
  match xs with
  | [] -> cur
  | x::tl -> list_max_nat_acc tl (if x > cur then x else cur)
let max_of_nat_list (xs : Prims.nat Prims.list) : Prims.nat=
  match xs with | [] -> Prims.int_zero | x::tl -> list_max_nat_acc tl x
let rec bits_needed (v : Prims.nat) : Prims.nat=
  if v = Prims.int_zero
  then Prims.int_zero
  else Prims.int_one + (bits_needed (v / (Prims.of_int (2))))
let clamp_nonneg (x : Prims.int) : Prims.nat=
  if x < Prims.int_zero then Prims.int_zero else x
let rec map_clamp_nonneg_acc (xs : Prims.int Prims.list)
  (acc : Prims.nat Prims.list) : Prims.nat Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev acc
  | x::tl -> map_clamp_nonneg_acc tl ((clamp_nonneg x) :: acc)
let map_clamp_nonneg (xs : Prims.int Prims.list) : Prims.nat Prims.list=
  map_clamp_nonneg_acc xs []
let rec pad_to_length_acc (xs : Prims.nat Prims.list) (target : Prims.nat)
  (filler : Prims.nat) (acc : Prims.nat Prims.list) : Prims.nat Prims.list=
  if target = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    (match xs with
     | [] ->
         pad_to_length_acc [] (target - Prims.int_one) filler (filler :: acc)
     | hd::tl ->
         pad_to_length_acc tl (target - Prims.int_one) filler (hd :: acc))
let pad_to_length (xs : Prims.nat Prims.list) (target : Prims.nat)
  (filler : Prims.nat) : Prims.nat Prims.list=
  pad_to_length_acc xs target filler []
let rec repeat_byte (v : Prims.nat) (count : Prims.nat) : RDF_Bytes.bytes=
  if count = Prims.int_zero
  then []
  else (RDF_Bytes.byte_of_int ((mod) v (Prims.of_int (256)))) ::
    (repeat_byte v (count - Prims.int_one))
let rec chunk_rows_acc (rows : cottas_quad Prims.list) (cap : Prims.nat)
  (cur : cottas_quad Prims.list) (cur_n : Prims.nat)
  (acc : cottas_quad Prims.list Prims.list) :
  cottas_quad Prims.list Prims.list=
  match rows with
  | [] ->
      if cur_n = Prims.int_zero
      then FStar_List_Tot_Base.rev acc
      else FStar_List_Tot_Base.rev ((FStar_List_Tot_Base.rev cur) :: acc)
  | hd::tl ->
      if (cap = Prims.int_zero) || ((cur_n + Prims.int_one) >= cap)
      then
        chunk_rows_acc tl cap [] Prims.int_zero
          ((FStar_List_Tot_Base.rev (hd :: cur)) :: acc)
      else chunk_rows_acc tl cap (hd :: cur) (cur_n + Prims.int_one) acc
let chunk_rows (rows : cottas_quad Prims.list) (cap : Prims.nat) :
  cottas_quad Prims.list Prims.list=
  chunk_rows_acc rows cap [] Prims.int_zero []
let rec bits_of_nat_lsb (v : Prims.nat) (width : Prims.nat) :
  Prims.nat Prims.list=
  if width = Prims.int_zero
  then []
  else ((mod) v (Prims.of_int (2))) ::
    (bits_of_nat_lsb (v / (Prims.of_int (2))) (width - Prims.int_one))
let rec bits_of_nat_list_racc (vs : Prims.nat Prims.list) (width : Prims.nat)
  (racc : Prims.nat Prims.list) : Prims.nat Prims.list=
  match vs with
  | [] -> FStar_List_Tot_Base.rev racc
  | v::tl ->
      bits_of_nat_list_racc tl width
        (FStar_List_Tot_Base.rev_acc (bits_of_nat_lsb v width) racc)
let bits_of_nat_list (vs : Prims.nat Prims.list) (width : Prims.nat) :
  Prims.nat Prims.list= bits_of_nat_list_racc vs width []
let rec pack_bits_to_bytes_acc (bits : Prims.nat Prims.list)
  (collected : Prims.nat Prims.list) (count : Prims.nat)
  (out : RDF_Bytes.bytes) : RDF_Bytes.bytes=
  match bits with
  | [] -> FStar_List_Tot_Base.rev out
  | hd::tl ->
      if count = (Prims.of_int (7))
      then
        (match FStar_List_Tot_Base.rev (hd :: collected) with
         | b0::b1::b2::b3::b4::b5::b6::b7::[] ->
             let v =
               ((((((b0 + ((Prims.of_int (2)) * b1)) +
                      ((Prims.of_int (4)) * b2))
                     + ((Prims.of_int (8)) * b3))
                    + ((Prims.of_int (16)) * b4))
                   + ((Prims.of_int (32)) * b5))
                  + ((Prims.of_int (64)) * b6))
                 + ((Prims.of_int (128)) * b7) in
             pack_bits_to_bytes_acc tl [] Prims.int_zero
               ((RDF_Bytes.byte_of_int ((mod) v (Prims.of_int (256)))) ::
               out)
         | uu___ -> FStar_List_Tot_Base.rev out)
      else
        pack_bits_to_bytes_acc tl (hd :: collected) (count + Prims.int_one)
          out
let pack_bits_to_bytes (bits : Prims.nat Prims.list) : RDF_Bytes.bytes=
  pack_bits_to_bytes_acc bits [] Prims.int_zero []
let rec map_sub_min_acc (xs : Prims.int Prims.list) (min_delta : Prims.int)
  (acc : Prims.int Prims.list) : Prims.int Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev acc
  | x::tl -> map_sub_min_acc tl min_delta ((x - min_delta) :: acc)
let build_dlba_length_block (values : Prims.string Prims.list) :
  (Prims.nat * RDF_Bytes.bytes)=
  let lengths = string_lengths values in
  let value_count = list_len lengths in
  match lengths with
  | [] ->
      let header =
        RDF_List_Helpers.append_tr (write_uvarint values_per_miniblock)
          (RDF_List_Helpers.append_tr (write_uvarint Prims.int_one)
             (RDF_List_Helpers.append_tr (write_uvarint Prims.int_zero)
                (RDF_List_Helpers.append_tr
                   (write_uvarint (zigzag_encode_nat Prims.int_zero))
                   (write_uvarint (zigzag_encode_int Prims.int_zero))))) in
      (Prims.int_zero,
        (RDF_List_Helpers.append_tr header
           [RDF_Bytes.byte_of_int Prims.int_zero]))
  | first_length::uu___ ->
      let deltas = consecutive_deltas lengths in
      let num_deltas = list_len deltas in
      let min_delta = min_of_int_list deltas in
      let adjusted_int = map_sub_min_acc deltas min_delta [] in
      let adjusted = map_clamp_nonneg adjusted_int in
      let bit_width = bits_needed (max_of_nat_list adjusted) in
      let miniblocks =
        if num_deltas = Prims.int_zero
        then Prims.int_one
        else
          ((num_deltas + values_per_miniblock) - Prims.int_one) /
            values_per_miniblock in
      let block_size = miniblocks * values_per_miniblock in
      let padded = pad_to_length adjusted block_size Prims.int_zero in
      let bits = bits_of_nat_list padded bit_width in
      let packed = pack_bits_to_bytes bits in
      let widths = repeat_byte bit_width miniblocks in
      let header =
        RDF_List_Helpers.append_tr (write_uvarint block_size)
          (RDF_List_Helpers.append_tr (write_uvarint miniblocks)
             (RDF_List_Helpers.append_tr (write_uvarint value_count)
                (RDF_List_Helpers.append_tr
                   (write_uvarint (zigzag_encode_nat first_length))
                   (write_uvarint (zigzag_encode_int min_delta))))) in
      (value_count,
        (RDF_List_Helpers.append_tr header
           (RDF_List_Helpers.append_tr widths packed)))
let rec concat_strings_bytes_racc (vs : Prims.string Prims.list)
  (racc : RDF_Bytes.bytes) : RDF_Bytes.bytes=
  match vs with
  | [] -> FStar_List_Tot_Base.rev racc
  | v::tl ->
      concat_strings_bytes_racc tl
        (FStar_List_Tot_Base.rev_acc (RDF_Bytes.bytes_of_string v) racc)
let concat_strings_bytes (vs : Prims.string Prims.list) : RDF_Bytes.bytes=
  concat_strings_bytes_racc vs []
let build_def_level_section (value_count : Prims.nat) : RDF_Bytes.bytes=
  let rle_bytes =
    if value_count = Prims.int_zero
    then []
    else
      RDF_List_Helpers.append_tr (write_uvarint (value_count + value_count))
        [RDF_Bytes.byte_of_int Prims.int_one] in
  let section_len = FStar_List_Tot_Base.length rle_bytes in
  if section_len >= (Prims.parse_int "4294967296")
  then []
  else
    RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le section_len) rle_bytes
let build_page_header (encoding : Prims.nat) (num_values : Prims.nat)
  (uncompressed_size : Prims.nat) (compressed_size : Prims.nat) :
  RDF_Bytes.bytes=
  let f1 =
    write_field_i32 Prims.int_one Prims.int_zero parquet_page_type_data_page in
  let f2 = write_field_i32 (Prims.of_int (2)) Prims.int_one uncompressed_size in
  let f3 =
    write_field_i32 (Prims.of_int (3)) (Prims.of_int (2)) compressed_size in
  let d1 = write_field_i32 Prims.int_one Prims.int_zero num_values in
  let d2 = write_field_i32 (Prims.of_int (2)) Prims.int_one encoding in
  let d3 =
    write_field_i32 (Prims.of_int (3)) (Prims.of_int (2))
      parquet_encoding_rle in
  let d4 =
    write_field_i32 (Prims.of_int (4)) (Prims.of_int (3))
      parquet_encoding_rle in
  let dph =
    RDF_List_Helpers.append_tr d1
      (RDF_List_Helpers.append_tr d2
         (RDF_List_Helpers.append_tr d3
            (RDF_List_Helpers.append_tr d4 write_stop))) in
  let f5 =
    RDF_List_Helpers.append_tr
      (write_field_header Parquet_Footer.compact_t_struct (Prims.of_int (5))
         (Prims.of_int (3))) dph in
  RDF_List_Helpers.append_tr f1
    (RDF_List_Helpers.append_tr f2
       (RDF_List_Helpers.append_tr f3
          (RDF_List_Helpers.append_tr f5 write_stop)))
let build_column_page (values : Prims.string Prims.list) :
  (Prims.nat * Prims.nat * RDF_Bytes.bytes)=
  let value_count = list_len values in
  let def_section = build_def_level_section value_count in
  let uu___ = build_dlba_length_block values in
  match uu___ with
  | (_dlba_value_count, length_block) ->
      let value_bytes = concat_strings_bytes values in
      let payload =
        RDF_List_Helpers.append_tr def_section
          (RDF_List_Helpers.append_tr length_block value_bytes) in
      let payload_len = list_len payload in
      let header =
        build_page_header parquet_encoding_dlba value_count payload_len
          payload_len in
      let page_bytes = RDF_List_Helpers.append_tr header payload in
      (value_count, (list_len page_bytes), page_bytes)
let build_column_metadata (name : Prims.string) (num_values : Prims.nat)
  (page_len : Prims.nat) (data_page_offset : Prims.nat) : RDF_Bytes.bytes=
  let f1 =
    write_field_i32 Prims.int_one Prims.int_zero parquet_type_byte_array in
  let f2 =
    write_field_list_header (Prims.of_int (2)) Prims.int_one Prims.int_one
      Parquet_Footer.compact_t_i32 in
  let f2v = write_uvarint (zigzag_encode_nat parquet_encoding_dlba) in
  let f3 =
    write_field_list_header (Prims.of_int (3)) (Prims.of_int (2))
      Prims.int_one Parquet_Footer.compact_t_binary in
  let f3v =
    RDF_List_Helpers.append_tr (write_uvarint (FStar_String.strlen name))
      (RDF_Bytes.bytes_of_string name) in
  let f4 =
    write_field_i32 (Prims.of_int (4)) (Prims.of_int (3))
      parquet_codec_uncompressed in
  let f5 = write_field_i64 (Prims.of_int (5)) (Prims.of_int (4)) num_values in
  let f6 = write_field_i64 (Prims.of_int (6)) (Prims.of_int (5)) page_len in
  let f7 = write_field_i64 (Prims.of_int (7)) (Prims.of_int (6)) page_len in
  let f9 =
    write_field_i64 (Prims.of_int (9)) (Prims.of_int (7)) data_page_offset in
  RDF_List_Helpers.append_tr f1
    (RDF_List_Helpers.append_tr f2
       (RDF_List_Helpers.append_tr f2v
          (RDF_List_Helpers.append_tr f3
             (RDF_List_Helpers.append_tr f3v
                (RDF_List_Helpers.append_tr f4
                   (RDF_List_Helpers.append_tr f5
                      (RDF_List_Helpers.append_tr f6
                         (RDF_List_Helpers.append_tr f7
                            (RDF_List_Helpers.append_tr f9 write_stop)))))))))
let build_column_chunk (name : Prims.string) (num_values : Prims.nat)
  (page_len : Prims.nat) (data_page_offset : Prims.nat) : RDF_Bytes.bytes=
  let f2 = write_field_i64 (Prims.of_int (2)) Prims.int_zero data_page_offset in
  let meta = build_column_metadata name num_values page_len data_page_offset in
  let f3 =
    RDF_List_Helpers.append_tr
      (write_field_header Parquet_Footer.compact_t_struct (Prims.of_int (3))
         (Prims.of_int (2))) meta in
  RDF_List_Helpers.append_tr f2 (RDF_List_Helpers.append_tr f3 write_stop)
let build_schema_leaf (name : Prims.string) : RDF_Bytes.bytes=
  let f1 =
    write_field_i32 Prims.int_one Prims.int_zero parquet_type_byte_array in
  let f3 =
    write_field_i32 (Prims.of_int (3)) Prims.int_one
      parquet_repetition_optional in
  let f4 = write_field_binary (Prims.of_int (4)) (Prims.of_int (3)) name in
  let f6 =
    write_field_i32 (Prims.of_int (6)) (Prims.of_int (4)) Prims.int_zero in
  RDF_List_Helpers.append_tr f1
    (RDF_List_Helpers.append_tr f3
       (RDF_List_Helpers.append_tr f4
          (RDF_List_Helpers.append_tr f6 write_stop)))
let build_schema_root (num_children : Prims.nat) : RDF_Bytes.bytes=
  let f4 = write_field_binary (Prims.of_int (4)) Prims.int_zero "schema" in
  let f5 = write_field_i32 (Prims.of_int (5)) (Prims.of_int (4)) num_children in
  RDF_List_Helpers.append_tr f4 (RDF_List_Helpers.append_tr f5 write_stop)
let build_schema_list (names : Prims.string Prims.list) :
  (Prims.nat * RDF_Bytes.bytes)=
  let root = build_schema_root (FStar_List_Tot_Base.length names) in
  let leaves = RDF_List_Helpers.concatMap_tr build_schema_leaf names in
  ((Prims.int_one + (FStar_List_Tot_Base.length names)),
    (RDF_List_Helpers.append_tr root leaves))
let rec map_cq_s_acc (rows : cottas_quad Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match rows with
  | [] -> FStar_List_Tot_Base.rev acc
  | r::tl -> map_cq_s_acc tl ((r.cq_s) :: acc)
let map_cq_s (rows : cottas_quad Prims.list) : Prims.string Prims.list=
  map_cq_s_acc rows []
let rec map_cq_p_acc (rows : cottas_quad Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match rows with
  | [] -> FStar_List_Tot_Base.rev acc
  | r::tl -> map_cq_p_acc tl ((r.cq_p) :: acc)
let map_cq_p (rows : cottas_quad Prims.list) : Prims.string Prims.list=
  map_cq_p_acc rows []
let rec map_cq_o_acc (rows : cottas_quad Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match rows with
  | [] -> FStar_List_Tot_Base.rev acc
  | r::tl -> map_cq_o_acc tl ((r.cq_o) :: acc)
let map_cq_o (rows : cottas_quad Prims.list) : Prims.string Prims.list=
  map_cq_o_acc rows []
let rec map_cq_g_acc (rows : cottas_quad Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match rows with
  | [] -> FStar_List_Tot_Base.rev acc
  | r::tl -> map_cq_g_acc tl ((r.cq_g) :: acc)
let map_cq_g (rows : cottas_quad Prims.list) : Prims.string Prims.list=
  map_cq_g_acc rows []
let build_row_group (start_offset : Prims.nat)
  (rows : cottas_quad Prims.list) :
  (Prims.nat * RDF_Bytes.bytes * RDF_Bytes.bytes * Prims.nat)=
  let num_rows = list_len rows in
  let uu___ = build_column_page (map_cq_s rows) in
  match uu___ with
  | (nv_s, len_s, bytes_s) ->
      let off_s = start_offset in
      let off_p = off_s + len_s in
      let uu___1 = build_column_page (map_cq_p rows) in
      (match uu___1 with
       | (nv_p, len_p, bytes_p) ->
           let off_o = off_p + len_p in
           let uu___2 = build_column_page (map_cq_o rows) in
           (match uu___2 with
            | (nv_o, len_o, bytes_o) ->
                let off_g = off_o + len_o in
                let uu___3 = build_column_page (map_cq_g rows) in
                (match uu___3 with
                 | (nv_g, len_g, bytes_g) ->
                     let next_offset = off_g + len_g in
                     let page_bytes =
                       RDF_List_Helpers.append_tr bytes_s
                         (RDF_List_Helpers.append_tr bytes_p
                            (RDF_List_Helpers.append_tr bytes_o bytes_g)) in
                     let chunk_s = build_column_chunk "s" nv_s len_s off_s in
                     let chunk_p = build_column_chunk "p" nv_p len_p off_p in
                     let chunk_o = build_column_chunk "o" nv_o len_o off_o in
                     let chunk_g = build_column_chunk "g" nv_g len_g off_g in
                     let columns_list =
                       RDF_List_Helpers.append_tr
                         (write_list_header (Prims.of_int (4))
                            Parquet_Footer.compact_t_struct)
                         (RDF_List_Helpers.append_tr chunk_s
                            (RDF_List_Helpers.append_tr chunk_p
                               (RDF_List_Helpers.append_tr chunk_o chunk_g))) in
                     let f1 =
                       RDF_List_Helpers.append_tr
                         (write_field_header Parquet_Footer.compact_t_list
                            Prims.int_one Prims.int_zero) columns_list in
                     let total_byte_size = ((len_s + len_p) + len_o) + len_g in
                     let f2 =
                       write_field_i64 (Prims.of_int (2)) Prims.int_one
                         total_byte_size in
                     let f3 =
                       write_field_i64 (Prims.of_int (3)) (Prims.of_int (2))
                         num_rows in
                     let rg_meta =
                       RDF_List_Helpers.append_tr f1
                         (RDF_List_Helpers.append_tr f2
                            (RDF_List_Helpers.append_tr f3 write_stop)) in
                     (next_offset, page_bytes, rg_meta, num_rows))))
let rec build_row_groups_acc (start_offset : Prims.nat)
  (groups : cottas_quad Prims.list Prims.list) :
  (Prims.nat * RDF_Bytes.bytes * RDF_Bytes.bytes Prims.list * Prims.nat)=
  match groups with
  | [] -> (start_offset, [], [], Prims.int_zero)
  | g::rest ->
      let uu___ = build_row_group start_offset g in
      (match uu___ with
       | (off1, pbytes, rgmeta, nrows) ->
           let uu___1 = build_row_groups_acc off1 rest in
           (match uu___1 with
            | (off2, rest_pbytes, rest_rgmeta, rest_nrows) ->
                (off2, (RDF_List_Helpers.append_tr pbytes rest_pbytes),
                  (rgmeta :: rest_rgmeta), (nrows + rest_nrows))))
let build_file_metadata (num_rows : Prims.nat)
  (rg_metas : RDF_Bytes.bytes Prims.list) : RDF_Bytes.bytes=
  let f1 = write_field_i32 Prims.int_one Prims.int_zero Prims.int_one in
  let uu___ = build_schema_list ["s"; "p"; "o"; "g"] in
  match uu___ with
  | (schema_count, schema_elems) ->
      let f2 =
        RDF_List_Helpers.append_tr
          (write_field_header Parquet_Footer.compact_t_list
             (Prims.of_int (2)) Prims.int_one)
          (RDF_List_Helpers.append_tr
             (write_list_header schema_count Parquet_Footer.compact_t_struct)
             schema_elems) in
      let f3 = write_field_i64 (Prims.of_int (3)) (Prims.of_int (2)) num_rows in
      let num_rg = FStar_List_Tot_Base.length rg_metas in
      let rg_list =
        RDF_List_Helpers.append_tr
          (write_list_header num_rg Parquet_Footer.compact_t_struct)
          (concat_bytes_list rg_metas) in
      let f4 =
        RDF_List_Helpers.append_tr
          (write_field_header Parquet_Footer.compact_t_list
             (Prims.of_int (4)) (Prims.of_int (3))) rg_list in
      RDF_List_Helpers.append_tr f1
        (RDF_List_Helpers.append_tr f2
           (RDF_List_Helpers.append_tr f3
              (RDF_List_Helpers.append_tr f4 write_stop)))
let magic_header : RDF_Bytes.bytes=
  RDF_Bytes.bytes_of_string Parquet_Footer.parquet_magic
let serialize_cottas (rows : cottas_quad Prims.list) : RDF_Bytes.bytes=
  let groups = chunk_rows rows row_group_size in
  let uu___ =
    build_row_groups_acc (FStar_List_Tot_Base.length magic_header) groups in
  match uu___ with
  | (_final_offset, page_bytes, rg_metas, num_rows) ->
      let metadata = build_file_metadata num_rows rg_metas in
      let metadata_len = list_len metadata in
      if metadata_len >= (Prims.parse_int "4294967296")
      then RDF_List_Helpers.append_tr magic_header page_bytes
      else
        RDF_List_Helpers.append_tr magic_header
          (RDF_List_Helpers.append_tr page_bytes
             (RDF_List_Helpers.append_tr metadata
                (RDF_List_Helpers.append_tr
                   (RDF_Bytes.write_u32_le metadata_len) magic_header)))
let parquet_encoding_plain : Prims.nat= Prims.int_zero
let parquet_encoding_rle_dictionary : Prims.nat= (Prims.of_int (8))
let parquet_page_type_dictionary_page : Prims.nat= (Prims.of_int (2))
let str_lt (a : Prims.string) (b : Prims.string) : Prims.bool=
  (FStar_String.compare a b) < Prims.int_zero
let str_le (a : Prims.string) (b : Prims.string) : Prims.bool=
  (FStar_String.compare a b) <= Prims.int_zero
let rec str_list_len_acc (xs : Prims.string Prims.list) (acc : Prims.nat) :
  Prims.nat=
  match xs with
  | [] -> acc
  | uu___::tl -> str_list_len_acc tl (acc + Prims.int_one)
let str_list_len (xs : Prims.string Prims.list) : Prims.nat=
  str_list_len_acc xs Prims.int_zero
let rec split_pos_str_acc (n : Prims.nat) (xs : Prims.string Prims.list)
  (acc : Prims.string Prims.list) :
  (Prims.string Prims.list * Prims.string Prims.list)=
  match xs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | hd::tl ->
      if n = Prims.int_zero
      then ((FStar_List_Tot_Base.rev acc), xs)
      else split_pos_str_acc (n - Prims.int_one) tl (hd :: acc)
let rec merge_sorted_str_acc (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) (fuel : Prims.nat)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then
    RDF_List_Helpers.append_tr (FStar_List_Tot_Base.rev acc)
      (RDF_List_Helpers.append_tr xs ys)
  else
    (match (xs, ys) with
     | ([], []) -> FStar_List_Tot_Base.rev acc
     | ([], hd::tl) ->
         merge_sorted_str_acc [] tl (fuel - Prims.int_one) (hd :: acc)
     | (hd::tl, []) ->
         merge_sorted_str_acc tl [] (fuel - Prims.int_one) (hd :: acc)
     | (hx::tx, hy::ty) ->
         if str_le hx hy
         then merge_sorted_str_acc tx ys (fuel - Prims.int_one) (hx :: acc)
         else merge_sorted_str_acc xs ty (fuel - Prims.int_one) (hy :: acc))
let rec merge_sort_strings_fuel (xs : Prims.string Prims.list)
  (depth_fuel : Prims.nat) : Prims.string Prims.list=
  match xs with
  | [] -> []
  | uu___::[] -> xs
  | uu___::uu___1::uu___2 ->
      if depth_fuel = Prims.int_zero
      then xs
      else
        (let n = str_list_len xs in
         let uu___4 = split_pos_str_acc (n / (Prims.of_int (2))) xs [] in
         match uu___4 with
         | (left, right) ->
             let sl =
               merge_sort_strings_fuel left (depth_fuel - Prims.int_one) in
             let sr =
               merge_sort_strings_fuel right (depth_fuel - Prims.int_one) in
             let fuel = (str_list_len sl) + (str_list_len sr) in
             merge_sorted_str_acc sl sr fuel [])
let merge_sort_strings (xs : Prims.string Prims.list) :
  Prims.string Prims.list=
  merge_sort_strings_fuel xs ((str_list_len xs) + Prims.int_one)
let rec dedup_sorted_str_acc (xs : Prims.string Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev acc
  | x::[] -> FStar_List_Tot_Base.rev (x :: acc)
  | x::y::tl ->
      if x = y
      then dedup_sorted_str_acc (y :: tl) acc
      else dedup_sorted_str_acc (y :: tl) (x :: acc)
let dedup_sorted_str (xs : Prims.string Prims.list) :
  Prims.string Prims.list= dedup_sorted_str_acc xs []
let rec zip_with_index_acc (xs : Prims.string Prims.list) (i : Prims.nat)
  (acc : (Prims.string * Prims.nat) Prims.list) :
  (Prims.string * Prims.nat) Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev acc
  | hd::tl -> zip_with_index_acc tl (i + Prims.int_one) ((hd, i) :: acc)
let zip_with_index (xs : Prims.string Prims.list) :
  (Prims.string * Prims.nat) Prims.list=
  zip_with_index_acc xs Prims.int_zero []
type dict_lookup_tree =
  | DLT_Leaf 
  | DLT_Node of (dict_lookup_tree * Prims.string * Prims.nat *
  dict_lookup_tree) 
let uu___is_DLT_Leaf (projectee : dict_lookup_tree) : Prims.bool=
  match projectee with | DLT_Leaf -> true | uu___ -> false
let uu___is_DLT_Node (projectee : dict_lookup_tree) : Prims.bool=
  match projectee with | DLT_Node _0 -> true | uu___ -> false
let __proj__DLT_Node__item___0 (projectee : dict_lookup_tree) :
  (dict_lookup_tree * Prims.string * Prims.nat * dict_lookup_tree)=
  match projectee with | DLT_Node _0 -> _0
let rec split_pos_pair_acc (n : Prims.nat)
  (xs : (Prims.string * Prims.nat) Prims.list)
  (acc : (Prims.string * Prims.nat) Prims.list) :
  ((Prims.string * Prims.nat) Prims.list * (Prims.string * Prims.nat)
    Prims.list)=
  match xs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | hd::tl ->
      if n = Prims.int_zero
      then ((FStar_List_Tot_Base.rev acc), xs)
      else split_pos_pair_acc (n - Prims.int_one) tl (hd :: acc)
let rec dict_tree_of_sorted (xs : (Prims.string * Prims.nat) Prims.list)
  (n : Prims.nat) : dict_lookup_tree=
  if n = Prims.int_zero
  then DLT_Leaf
  else
    (let mid = n / (Prims.of_int (2)) in
     let uu___1 = split_pos_pair_acc mid xs [] in
     match uu___1 with
     | (left, rest) ->
         (match rest with
          | [] -> DLT_Leaf
          | (k, v)::right ->
              DLT_Node
                ((dict_tree_of_sorted left mid), k, v,
                  (dict_tree_of_sorted right ((n - mid) - Prims.int_one)))))
let rec dict_tree_find (v : Prims.string) (t : dict_lookup_tree) :
  Prims.nat FStar_Pervasives_Native.option=
  match t with
  | DLT_Leaf -> FStar_Pervasives_Native.None
  | DLT_Node (l, k, idx, r) ->
      if v = k
      then FStar_Pervasives_Native.Some idx
      else if str_lt v k then dict_tree_find v l else dict_tree_find v r
let rec lookup_indices_acc (values : Prims.string Prims.list)
  (t : dict_lookup_tree) (acc : Prims.nat Prims.list) : Prims.nat Prims.list=
  match values with
  | [] -> FStar_List_Tot_Base.rev acc
  | v::tl ->
      let idx =
        match dict_tree_find v t with
        | FStar_Pervasives_Native.Some i -> i
        | FStar_Pervasives_Native.None -> Prims.int_zero in
      lookup_indices_acc tl t (idx :: acc)
let lookup_indices (values : Prims.string Prims.list) (t : dict_lookup_tree)
  : Prims.nat Prims.list= lookup_indices_acc values t []
let rec group_runs_acc (indices : Prims.nat Prims.list) (cur_val : Prims.nat)
  (cur_count : Prims.nat) (acc : (Prims.nat * Prims.nat) Prims.list) :
  (Prims.nat * Prims.nat) Prims.list=
  match indices with
  | [] -> FStar_List_Tot_Base.rev ((cur_val, cur_count) :: acc)
  | v::tl ->
      if v = cur_val
      then group_runs_acc tl cur_val (cur_count + Prims.int_one) acc
      else group_runs_acc tl v Prims.int_one ((cur_val, cur_count) :: acc)
let group_runs (indices : Prims.nat Prims.list) :
  (Prims.nat * Prims.nat) Prims.list=
  match indices with
  | [] -> []
  | v::tl -> group_runs_acc tl v Prims.int_one []
let rec write_le_uint_bytes_acc (v : Prims.nat) (nbytes : Prims.nat)
  (acc : RDF_Bytes.byte Prims.list) : RDF_Bytes.bytes=
  if nbytes = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    write_le_uint_bytes_acc (v / (Prims.of_int (256)))
      (nbytes - Prims.int_one)
      ((RDF_Bytes.byte_of_int ((mod) v (Prims.of_int (256)))) :: acc)
let write_le_uint_bytes (v : Prims.nat) (nbytes : Prims.nat) :
  RDF_Bytes.bytes= write_le_uint_bytes_acc v nbytes []
let rec build_rle_runs_acc (body_nbytes : Prims.nat)
  (runs : (Prims.nat * Prims.nat) Prims.list) (racc : RDF_Bytes.bytes) :
  RDF_Bytes.bytes=
  match runs with
  | [] -> FStar_List_Tot_Base.rev racc
  | (value, count)::tl ->
      let header = write_uvarint (count + count) in
      let body = write_le_uint_bytes value body_nbytes in
      build_rle_runs_acc body_nbytes tl
        (FStar_List_Tot_Base.rev_acc (RDF_List_Helpers.append_tr header body)
           racc)
let build_rle_runs (body_nbytes : Prims.nat)
  (runs : (Prims.nat * Prims.nat) Prims.list) : RDF_Bytes.bytes=
  build_rle_runs_acc body_nbytes runs []
let write_dict_entry (e : Prims.string) : RDF_Bytes.bytes=
  let len = FStar_String.strlen e in
  if len >= (Prims.parse_int "4294967296")
  then []
  else
    RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le len)
      (RDF_Bytes.bytes_of_string e)
let rec build_dict_entries_acc (entries : Prims.string Prims.list)
  (racc : RDF_Bytes.bytes) : RDF_Bytes.bytes=
  match entries with
  | [] -> FStar_List_Tot_Base.rev racc
  | e::tl ->
      build_dict_entries_acc tl
        (FStar_List_Tot_Base.rev_acc (write_dict_entry e) racc)
let build_dict_page_payload (entries : Prims.string Prims.list) :
  RDF_Bytes.bytes= build_dict_entries_acc entries []
let build_dictionary_page_header (num_values : Prims.nat)
  (uncompressed_size : Prims.nat) (compressed_size : Prims.nat) :
  RDF_Bytes.bytes=
  let f1 =
    write_field_i32 Prims.int_one Prims.int_zero
      parquet_page_type_dictionary_page in
  let f2 = write_field_i32 (Prims.of_int (2)) Prims.int_one uncompressed_size in
  let f3 =
    write_field_i32 (Prims.of_int (3)) (Prims.of_int (2)) compressed_size in
  let d1 = write_field_i32 Prims.int_one Prims.int_zero num_values in
  let d2 =
    write_field_i32 (Prims.of_int (2)) Prims.int_one parquet_encoding_plain in
  let dph =
    RDF_List_Helpers.append_tr d1 (RDF_List_Helpers.append_tr d2 write_stop) in
  let f7 =
    RDF_List_Helpers.append_tr
      (write_field_header Parquet_Footer.compact_t_struct (Prims.of_int (7))
         (Prims.of_int (3))) dph in
  RDF_List_Helpers.append_tr f1
    (RDF_List_Helpers.append_tr f2
       (RDF_List_Helpers.append_tr f3
          (RDF_List_Helpers.append_tr f7 write_stop)))
let build_rle_dictionary_page_payload (value_count : Prims.nat)
  (bit_width : Prims.nat) (runs : (Prims.nat * Prims.nat) Prims.list) :
  RDF_Bytes.bytes=
  let def_section = build_def_level_section value_count in
  let body_nbytes = (bit_width + (Prims.of_int (7))) / (Prims.of_int (8)) in
  let runs_bytes = build_rle_runs body_nbytes runs in
  RDF_List_Helpers.append_tr def_section
    (RDF_List_Helpers.append_tr
       [RDF_Bytes.byte_of_int ((mod) bit_width (Prims.of_int (256)))]
       runs_bytes)
type column_encoding =
  | CE_DLBA 
  | CE_RleDictionary 
let uu___is_CE_DLBA (projectee : column_encoding) : Prims.bool=
  match projectee with | CE_DLBA -> true | uu___ -> false
let uu___is_CE_RleDictionary (projectee : column_encoding) : Prims.bool=
  match projectee with | CE_RleDictionary -> true | uu___ -> false
type col_encoded =
  {
  ce_kind: column_encoding ;
  ce_num_values: Prims.nat ;
  ce_dict_page_len: Prims.nat ;
  ce_total_len: Prims.nat ;
  ce_bytes: RDF_Bytes.bytes }
let __proj__Mkcol_encoded__item__ce_kind (projectee : col_encoded) :
  column_encoding=
  match projectee with
  | { ce_kind; ce_num_values; ce_dict_page_len; ce_total_len; ce_bytes;_} ->
      ce_kind
let __proj__Mkcol_encoded__item__ce_num_values (projectee : col_encoded) :
  Prims.nat=
  match projectee with
  | { ce_kind; ce_num_values; ce_dict_page_len; ce_total_len; ce_bytes;_} ->
      ce_num_values
let __proj__Mkcol_encoded__item__ce_dict_page_len (projectee : col_encoded) :
  Prims.nat=
  match projectee with
  | { ce_kind; ce_num_values; ce_dict_page_len; ce_total_len; ce_bytes;_} ->
      ce_dict_page_len
let __proj__Mkcol_encoded__item__ce_total_len (projectee : col_encoded) :
  Prims.nat=
  match projectee with
  | { ce_kind; ce_num_values; ce_dict_page_len; ce_total_len; ce_bytes;_} ->
      ce_total_len
let __proj__Mkcol_encoded__item__ce_bytes (projectee : col_encoded) :
  RDF_Bytes.bytes=
  match projectee with
  | { ce_kind; ce_num_values; ce_dict_page_len; ce_total_len; ce_bytes;_} ->
      ce_bytes
let build_column_page_dlba_v2 (values : Prims.string Prims.list) :
  col_encoded=
  let uu___ = build_column_page values in
  match uu___ with
  | (nv, len, bytes) ->
      {
        ce_kind = CE_DLBA;
        ce_num_values = nv;
        ce_dict_page_len = Prims.int_zero;
        ce_total_len = len;
        ce_bytes = bytes
      }
let build_column_page_rle_dict (values : Prims.string Prims.list) :
  col_encoded=
  let value_count = list_len values in
  if value_count = Prims.int_zero
  then
    let dict_header =
      build_dictionary_page_header Prims.int_zero Prims.int_zero
        Prims.int_zero in
    let dict_len = list_len dict_header in
    let data_payload =
      build_rle_dictionary_page_payload Prims.int_zero Prims.int_zero [] in
    let data_payload_len = list_len data_payload in
    let data_header =
      build_page_header parquet_encoding_rle_dictionary Prims.int_zero
        data_payload_len data_payload_len in
    let data_bytes = RDF_List_Helpers.append_tr data_header data_payload in
    let data_len = list_len data_bytes in
    {
      ce_kind = CE_RleDictionary;
      ce_num_values = Prims.int_zero;
      ce_dict_page_len = dict_len;
      ce_total_len = (dict_len + data_len);
      ce_bytes = (RDF_List_Helpers.append_tr dict_header data_bytes)
    }
  else
    (let sorted = merge_sort_strings values in
     let distinct = dedup_sorted_str sorted in
     let dict_size = list_len distinct in
     let indexed = zip_with_index distinct in
     let tree = dict_tree_of_sorted indexed dict_size in
     let indices = lookup_indices values tree in
     let max_index =
       if dict_size = Prims.int_zero
       then Prims.int_zero
       else dict_size - Prims.int_one in
     let bit_width = bits_needed max_index in
     let runs = group_runs indices in
     let data_payload =
       build_rle_dictionary_page_payload value_count bit_width runs in
     let data_payload_len = list_len data_payload in
     let data_header =
       build_page_header parquet_encoding_rle_dictionary value_count
         data_payload_len data_payload_len in
     let data_bytes = RDF_List_Helpers.append_tr data_header data_payload in
     let dict_payload = build_dict_page_payload distinct in
     let dict_payload_len = list_len dict_payload in
     let dict_header =
       build_dictionary_page_header dict_size dict_payload_len
         dict_payload_len in
     let dict_bytes = RDF_List_Helpers.append_tr dict_header dict_payload in
     let dict_len = list_len dict_bytes in
     let data_len = list_len data_bytes in
     {
       ce_kind = CE_RleDictionary;
       ce_num_values = value_count;
       ce_dict_page_len = dict_len;
       ce_total_len = (dict_len + data_len);
       ce_bytes = (RDF_List_Helpers.append_tr dict_bytes data_bytes)
     })
let encode_column_forced_dict (values : Prims.string Prims.list) :
  col_encoded= build_column_page_rle_dict values
let encode_column_choose_smaller (values : Prims.string Prims.list) :
  col_encoded=
  let dlba = build_column_page_dlba_v2 values in
  let dict = build_column_page_rle_dict values in
  if dict.ce_total_len < dlba.ce_total_len then dict else dlba
let build_column_metadata_v2 (name : Prims.string) (ce : col_encoded)
  (chunk_start_offset : Prims.nat) : RDF_Bytes.bytes=
  match ce.ce_kind with
  | CE_DLBA ->
      build_column_metadata name ce.ce_num_values ce.ce_total_len
        chunk_start_offset
  | CE_RleDictionary ->
      let data_page_offset = chunk_start_offset + ce.ce_dict_page_len in
      let f1 =
        write_field_i32 Prims.int_one Prims.int_zero parquet_type_byte_array in
      let f2 =
        write_field_list_header (Prims.of_int (2)) Prims.int_one
          (Prims.of_int (2)) Parquet_Footer.compact_t_i32 in
      let f2v =
        RDF_List_Helpers.append_tr
          (write_uvarint (zigzag_encode_nat parquet_encoding_plain))
          (write_uvarint (zigzag_encode_nat parquet_encoding_rle_dictionary)) in
      let f3 =
        write_field_list_header (Prims.of_int (3)) (Prims.of_int (2))
          Prims.int_one Parquet_Footer.compact_t_binary in
      let f3v =
        RDF_List_Helpers.append_tr (write_uvarint (FStar_String.strlen name))
          (RDF_Bytes.bytes_of_string name) in
      let f4 =
        write_field_i32 (Prims.of_int (4)) (Prims.of_int (3))
          parquet_codec_uncompressed in
      let f5 =
        write_field_i64 (Prims.of_int (5)) (Prims.of_int (4))
          ce.ce_num_values in
      let f6 =
        write_field_i64 (Prims.of_int (6)) (Prims.of_int (5)) ce.ce_total_len in
      let f7 =
        write_field_i64 (Prims.of_int (7)) (Prims.of_int (6)) ce.ce_total_len in
      let f9 =
        write_field_i64 (Prims.of_int (9)) (Prims.of_int (7))
          data_page_offset in
      let f11 =
        write_field_i64 (Prims.of_int (11)) (Prims.of_int (9))
          chunk_start_offset in
      RDF_List_Helpers.append_tr f1
        (RDF_List_Helpers.append_tr f2
           (RDF_List_Helpers.append_tr f2v
              (RDF_List_Helpers.append_tr f3
                 (RDF_List_Helpers.append_tr f3v
                    (RDF_List_Helpers.append_tr f4
                       (RDF_List_Helpers.append_tr f5
                          (RDF_List_Helpers.append_tr f6
                             (RDF_List_Helpers.append_tr f7
                                (RDF_List_Helpers.append_tr f9
                                   (RDF_List_Helpers.append_tr f11 write_stop))))))))))
let build_column_chunk_v2 (name : Prims.string) (ce : col_encoded)
  (chunk_start_offset : Prims.nat) : RDF_Bytes.bytes=
  let f2 =
    write_field_i64 (Prims.of_int (2)) Prims.int_zero chunk_start_offset in
  let meta = build_column_metadata_v2 name ce chunk_start_offset in
  let f3 =
    RDF_List_Helpers.append_tr
      (write_field_header Parquet_Footer.compact_t_struct (Prims.of_int (3))
         (Prims.of_int (2))) meta in
  RDF_List_Helpers.append_tr f2 (RDF_List_Helpers.append_tr f3 write_stop)
let build_row_group_v2 (start_offset : Prims.nat)
  (rows : cottas_quad Prims.list) :
  (Prims.nat * RDF_Bytes.bytes * RDF_Bytes.bytes * Prims.nat)=
  let num_rows = list_len rows in
  let ce_s = encode_column_choose_smaller (map_cq_s rows) in
  let off_s = start_offset in
  let off_p = off_s + ce_s.ce_total_len in
  let ce_p = encode_column_forced_dict (map_cq_p rows) in
  let off_o = off_p + ce_p.ce_total_len in
  let ce_o = encode_column_choose_smaller (map_cq_o rows) in
  let off_g = off_o + ce_o.ce_total_len in
  let ce_g = encode_column_forced_dict (map_cq_g rows) in
  let next_offset = off_g + ce_g.ce_total_len in
  let page_bytes =
    RDF_List_Helpers.append_tr ce_s.ce_bytes
      (RDF_List_Helpers.append_tr ce_p.ce_bytes
         (RDF_List_Helpers.append_tr ce_o.ce_bytes ce_g.ce_bytes)) in
  let chunk_s = build_column_chunk_v2 "s" ce_s off_s in
  let chunk_p = build_column_chunk_v2 "p" ce_p off_p in
  let chunk_o = build_column_chunk_v2 "o" ce_o off_o in
  let chunk_g = build_column_chunk_v2 "g" ce_g off_g in
  let columns_list =
    RDF_List_Helpers.append_tr
      (write_list_header (Prims.of_int (4)) Parquet_Footer.compact_t_struct)
      (RDF_List_Helpers.append_tr chunk_s
         (RDF_List_Helpers.append_tr chunk_p
            (RDF_List_Helpers.append_tr chunk_o chunk_g))) in
  let f1 =
    RDF_List_Helpers.append_tr
      (write_field_header Parquet_Footer.compact_t_list Prims.int_one
         Prims.int_zero) columns_list in
  let total_byte_size =
    ((ce_s.ce_total_len + ce_p.ce_total_len) + ce_o.ce_total_len) +
      ce_g.ce_total_len in
  let f2 = write_field_i64 (Prims.of_int (2)) Prims.int_one total_byte_size in
  let f3 = write_field_i64 (Prims.of_int (3)) (Prims.of_int (2)) num_rows in
  let rg_meta =
    RDF_List_Helpers.append_tr f1
      (RDF_List_Helpers.append_tr f2
         (RDF_List_Helpers.append_tr f3 write_stop)) in
  (next_offset, page_bytes, rg_meta, num_rows)
let rec build_row_groups_acc_v2 (start_offset : Prims.nat)
  (groups : cottas_quad Prims.list Prims.list) :
  (Prims.nat * RDF_Bytes.bytes * RDF_Bytes.bytes Prims.list * Prims.nat)=
  match groups with
  | [] -> (start_offset, [], [], Prims.int_zero)
  | g::rest ->
      let uu___ = build_row_group_v2 start_offset g in
      (match uu___ with
       | (off1, pbytes, rgmeta, nrows) ->
           let uu___1 = build_row_groups_acc_v2 off1 rest in
           (match uu___1 with
            | (off2, rest_pbytes, rest_rgmeta, rest_nrows) ->
                (off2, (RDF_List_Helpers.append_tr pbytes rest_pbytes),
                  (rgmeta :: rest_rgmeta), (nrows + rest_nrows))))
let serialize_cottas_v2 (rows : cottas_quad Prims.list) : RDF_Bytes.bytes=
  let groups = chunk_rows rows row_group_size in
  let uu___ =
    build_row_groups_acc_v2 (FStar_List_Tot_Base.length magic_header) groups in
  match uu___ with
  | (_final_offset, page_bytes, rg_metas, num_rows) ->
      let metadata = build_file_metadata num_rows rg_metas in
      let metadata_len = list_len metadata in
      if metadata_len >= (Prims.parse_int "4294967296")
      then RDF_List_Helpers.append_tr magic_header page_bytes
      else
        RDF_List_Helpers.append_tr magic_header
          (RDF_List_Helpers.append_tr page_bytes
             (RDF_List_Helpers.append_tr metadata
                (RDF_List_Helpers.append_tr
                   (RDF_Bytes.write_u32_le metadata_len) magic_header)))
