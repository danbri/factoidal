module Parquet.Footer

module U32 = FStar.UInt32

type parquet_footer = {
  pf_metadata_len : nat;
  pf_footer_len : nat;
  pf_magic : string;
}

type compact_field = {
  cf_id : nat;
  cf_type : nat;
  cf_value_start : nat;
  cf_next : nat;
}

type compact_list_info = {
  cli_count : nat;
  cli_etype : nat;
  cli_payload_start : nat;
}

let parquet_magic : string = "PAR1"
let parquet_magic_hex : string = "50415231"

assume val parquet_read_tail_hex :
  path:string -> count:nat -> Tot (option string)

assume val parquet_read_range_hex :
  path:string -> start:nat -> count:nat -> Tot (option string)

assume val parquet_zstd_decompress_hex :
  compressed_hex:string -> expected_size:nat -> Tot (option string)

let hex_nibble (c:FStar.Char.char) : option nat =
  let code = FStar.Char.int_of_char c in
  if code >= 48 && code <= 57 then Some (code - 48)
  else if code >= 65 && code <= 70 then Some (code - 65 + 10)
  else if code >= 97 && code <= 102 then Some (code - 97 + 10)
  else None

let byte_at_hex (s:string) (i:nat { i + 1 < String.length s }) : option (b:nat { b < 256 }) =
  match hex_nibble (String.index s i), hex_nibble (String.index s (i + 1)) with
  | Some hi, Some lo ->
    let value:nat = hi + hi + hi + hi + hi + hi + hi + hi +
                    hi + hi + hi + hi + hi + hi + hi + hi + lo in
    Some value
  | _ -> None

let le_u32_at_hex (s:string) (start:nat { start + 7 < String.length s }) : option nat =
  match byte_at_hex s start,
        byte_at_hex s (start + 2),
        byte_at_hex s (start + 4),
        byte_at_hex s (start + 6) with
  | Some n0, Some n1, Some n2, Some n3 ->
    let b0 = U32.uint_to_t n0 in
    let b1 = U32.shift_left (U32.uint_to_t n1) (U32.uint_to_t 8) in
    let b2 = U32.shift_left (U32.uint_to_t n2) (U32.uint_to_t 16) in
    let b3 = U32.shift_left (U32.uint_to_t n3) (U32.uint_to_t 24) in
    Some (U32.v (U32.logor b0 (U32.logor b1 (U32.logor b2 b3))))
  | _ -> None

let parse_parquet_footer_tail_hex (tail:string) : option parquet_footer =
  let len = String.length tail in
  if len < 16 then None
  else
    let magic = String.sub tail (len - 8) 8 in
    if magic <> parquet_magic_hex then None
    else
      let footer_start = len - 16 in
      match le_u32_at_hex tail footer_start with
      | None -> None
      | Some meta_len ->
        Some {
          pf_metadata_len = meta_len;
          pf_footer_len = meta_len + 8;
          pf_magic = parquet_magic;
        }

let is_printable_byte (b:nat) : bool =
  b >= 32 && b <= 126

let finish_ascii_run (current:list FStar.Char.char) (acc:list string) : list string =
  if List.Tot.length current = 0 then acc
  else (String.string_of_list (List.Tot.rev current)) :: acc

let rec extract_ascii_strings_hex (hex:string) (pos:nat)
  (current:list FStar.Char.char) (acc:list string)
  : Tot (list string) (decreases (String.length hex - pos)) =
  if pos + 1 >= String.length hex then
    List.Tot.rev (finish_ascii_run current acc)
  else
    match byte_at_hex hex pos with
    | None -> List.Tot.rev (finish_ascii_run current acc)
    | Some b ->
      if is_printable_byte b then
        extract_ascii_strings_hex hex (pos + 2) ((FStar.Char.char_of_int b) :: current) acc
      else
        extract_ascii_strings_hex hex (pos + 2) [] (finish_ascii_run current acc)

let probe_parquet_footer (path:string) : option parquet_footer =
  match parquet_read_tail_hex path 8 with
  | None -> None
  | Some tail -> parse_parquet_footer_tail_hex tail

let probe_parquet_metadata_strings (path:string) : option (list string) =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        Some (extract_ascii_strings_hex (String.sub footer_hex 0 meta_hex_len) 0 [] [])
      else
        None

let compact_t_stop : nat = 0
let compact_t_bool_true : nat = 1
let compact_t_bool_false : nat = 2
let compact_t_byte : nat = 3
let compact_t_i16 : nat = 4
let compact_t_i32 : nat = 5
let compact_t_i64 : nat = 6
let compact_t_double : nat = 7
let compact_t_binary : nat = 8
let compact_t_list : nat = 9
let compact_t_set : nat = 10
let compact_t_map : nat = 11
let compact_t_struct : nat = 12

let high_nibble (b:nat { b < 256 }) : nat =
  U32.v (U32.shift_right (U32.uint_to_t b) (U32.uint_to_t 4))

let low_nibble (b:nat { b < 256 }) : nat =
  U32.v (U32.logand (U32.uint_to_t b) (U32.uint_to_t 15))

let low_7_bits (b:nat { b < 256 }) : nat =
  U32.v (U32.logand (U32.uint_to_t b) (U32.uint_to_t 127))

let rec scale_pow2 (x:nat) (shift:nat) : Tot nat (decreases shift) =
  if shift = 0 then x else scale_pow2 (x + x) (shift - 1)

let rec mul_nat (x:nat) (y:nat) : Tot nat (decreases y) =
  if y = 0 then 0 else x + mul_nat x (y - 1)

let pred_nat (n:nat { n > 0 }) : nat =
  n - 1

let succ_nat (n:nat) : nat =
  n + 1

let div_nat_pos (x:nat) (y:nat { y > 0 }) : nat =
  x / y

let le_u24_at_hex (s:string) (start:nat { start + 5 < String.length s }) : option nat =
  match byte_at_hex s start,
        byte_at_hex s (start + 2),
        byte_at_hex s (start + 4) with
  | Some n0, Some n1, Some n2 ->
    Some (n0 + scale_pow2 n1 8 + scale_pow2 n2 16)
  | _ -> None

let rec skip_varint_hex (hex:string) (pos:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else if pos + 1 >= String.length hex then None
  else
    match byte_at_hex hex pos with
    | None -> None
    | Some b ->
      let next = pos + 2 in
      if b < 128 then Some next
      else skip_varint_hex hex next (fuel - 1)

let rec skip_n_values_hex (hex:string) (etype:nat) (count:nat) (pos:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else if count = 0 then Some pos
  else
    match skip_compact_value_hex hex etype pos (fuel - 1) with
    | None -> None
    | Some next -> skip_n_values_hex hex etype (count - 1) next (fuel - 1)

and skip_struct_fields_hex (hex:string) (pos:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else if pos + 1 >= String.length hex then None
  else
    match byte_at_hex hex pos with
    | None -> None
    | Some header ->
      if header = compact_t_stop then Some (pos + 2)
      else
        let ftype = low_nibble header in
        let delta = high_nibble header in
        let value_pos =
          if delta = 0 then
            match skip_varint_hex hex (pos + 2) (fuel - 1) with
            | Some p -> p
            | None -> pos + 2
          else pos + 2 in
        if delta = 0 && value_pos = pos + 2 then None
        else
          match skip_compact_value_hex hex ftype value_pos (fuel - 1) with
          | None -> None
          | Some next -> skip_struct_fields_hex hex next (fuel - 1)

and skip_compact_value_hex (hex:string) (ftype:nat) (pos:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    if ftype = compact_t_bool_true || ftype = compact_t_bool_false then Some pos
    else if ftype = compact_t_byte then
      if pos + 1 < String.length hex then Some (pos + 2) else None
    else if ftype = compact_t_i16 || ftype = compact_t_i32 || ftype = compact_t_i64 then
      skip_varint_hex hex pos (fuel - 1)
    else if ftype = compact_t_double then
      if pos + 15 < String.length hex then Some (pos + 16) else None
    else if ftype = compact_t_binary then
      match skip_varint_hex hex pos (fuel - 1) with
      | None -> None
      | Some len_end ->
        let rec decode_varint_hex (p:nat) (shift:nat) (acc:nat) (fuel2:nat)
          : Tot (option nat) (decreases fuel2) =
          if fuel2 = 0 then None
          else if p + 1 >= String.length hex then None
          else
            match byte_at_hex hex p with
            | None -> None
            | Some b ->
              let payload = low_7_bits b in
              let acc' = acc + scale_pow2 payload shift in
              if b < 128 then Some acc' else decode_varint_hex (p + 2) (shift + 7) acc' (fuel2 - 1)
        in
        (match decode_varint_hex pos 0 0 (fuel - 1) with
         | None -> None
         | Some blen ->
           let data_end = len_end + (blen + blen) in
           if data_end <= String.length hex then Some data_end else None)
    else if ftype = compact_t_list || ftype = compact_t_set then
      if pos + 1 >= String.length hex then None
      else match byte_at_hex hex pos with
      | None -> None
      | Some header ->
        let size_nibble = high_nibble header in
        let etype = low_nibble header in
        if size_nibble < 15 then
          skip_n_values_hex hex etype size_nibble (pos + 2) (fuel - 1)
        else
          let rec decode_varint_hex (p:nat) (shift:nat) (acc:nat) (fuel2:nat)
            : Tot (option (nat & nat)) (decreases fuel2) =
            if fuel2 = 0 then None
            else if p + 1 >= String.length hex then None
            else
              match byte_at_hex hex p with
              | None -> None
              | Some b ->
                let payload = low_7_bits b in
                let acc' = acc + scale_pow2 payload shift in
                if b < 128 then Some (acc', p + 2)
                else decode_varint_hex (p + 2) (shift + 7) acc' (fuel2 - 1)
          in
          (match decode_varint_hex (pos + 2) 0 0 (fuel - 1) with
           | None -> None
           | Some (count, after_count) ->
             skip_n_values_hex hex etype count after_count (fuel - 1))
    else if ftype = compact_t_struct then
      skip_struct_fields_hex hex pos (fuel - 1)
    else if ftype = compact_t_map then
      None
    else None

let zigzag_decode_nat (n:nat) : nat =
  n / 2

let zigzag_decode_int (n:nat) : int =
  if n % 2 = 0 then (n / 2)
  else 0 - ((n / 2) + 1)

let rec decode_varint_value_with_end_hex (hex:string) (p:nat) (shift:nat) (acc:nat) (fuel:nat)
  : Tot (option (nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else if p + 1 >= String.length hex then None
  else
    match byte_at_hex hex p with
    | None -> None
    | Some b ->
      let payload = low_7_bits b in
      let acc' = acc + scale_pow2 payload shift in
      if b < 128 then Some (acc', p + 2)
      else decode_varint_value_with_end_hex hex (p + 2) (shift + 7) acc' (fuel - 1)

let rec decode_varint_value_hex (hex:string) (p:nat) (shift:nat) (acc:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  match decode_varint_value_with_end_hex hex p shift acc fuel with
  | None -> None
  | Some (n, _) -> Some n

let decode_compact_list_info_hex (hex:string) (pos:nat) (fuel:nat) : option compact_list_info =
  if pos + 1 >= String.length hex then None
  else
    match byte_at_hex hex pos with
    | None -> None
    | Some header ->
      let count_nibble = high_nibble header in
      let etype = low_nibble header in
      if count_nibble < 15 then
        Some { cli_count = count_nibble; cli_etype = etype; cli_payload_start = pos + 2 }
      else
        match decode_varint_value_with_end_hex hex (pos + 2) 0 0 fuel with
        | None -> None
        | Some (count, payload_start) ->
          Some { cli_count = count; cli_etype = etype; cli_payload_start = payload_start }

let decode_compact_list_count_hex (hex:string) (pos:nat) (fuel:nat) : option nat =
  match decode_compact_list_info_hex hex pos fuel with
  | None -> None
  | Some info -> Some info.cli_count

let decode_compact_binary_hex (hex:string) (pos:nat) (fuel:nat) : option string =
  match decode_varint_value_with_end_hex hex pos 0 0 fuel with
  | None -> None
  | Some (blen, payload_start) ->
    let chars_hex_len = blen + blen in
    let payload_end = payload_start + chars_hex_len in
    if payload_end > String.length hex then None
    else
      let rec build_chars (p:nat) (remaining:nat) (acc:list FStar.Char.char)
        : Tot (option (list FStar.Char.char)) (decreases remaining) =
        if remaining = 0 then Some (List.Tot.rev acc)
        else if p + 1 >= payload_end then None
        else
          match byte_at_hex hex p with
          | None -> None
          | Some b ->
            build_chars (p + 2) (remaining - 1) ((FStar.Char.char_of_int b) :: acc)
      in
      match build_chars payload_start blen [] with
      | None -> None
      | Some chars -> Some (String.string_of_list chars)

let nth_compact_list_element_start_hex (hex:string) (list_pos:nat) (index:nat) (fuel:nat)
  : option nat =
  match decode_compact_list_info_hex hex list_pos fuel with
  | None -> None
  | Some info ->
    if index >= info.cli_count then None
    else
      let rec loop (remaining:nat) (p:nat) (fuel2:nat)
        : Tot (option nat) (decreases fuel2) =
        if fuel2 = 0 then None
        else if remaining = 0 then Some p
        else
          match skip_compact_value_hex hex info.cli_etype p (fuel2 - 1) with
          | None -> None
          | Some next -> loop (remaining - 1) next (fuel2 - 1)
      in
      loop index info.cli_payload_start fuel

let rec nth_field_hex (hex:string) (target_id:nat) (pos:nat) (prev_id:nat) (fuel:nat)
  : Tot (option compact_field) (decreases fuel) =
  if fuel = 0 then None
  else if pos + 1 >= String.length hex then None
  else
    match byte_at_hex hex pos with
    | None -> None
    | Some header ->
      if header = compact_t_stop then None
      else
        let ftype = low_nibble header in
        let delta = high_nibble header in
        let rec decode_varint_hex (p:nat) (shift:nat) (acc:nat) (fuel2:nat)
          : Tot (option (nat & nat)) (decreases fuel2) =
          if fuel2 = 0 then None
          else if p + 1 >= String.length hex then None
          else
            match byte_at_hex hex p with
            | None -> None
            | Some b ->
              let payload = low_7_bits b in
              let acc' = acc + scale_pow2 payload shift in
              if b < 128 then Some (acc', p + 2)
              else decode_varint_hex (p + 2) (shift + 7) acc' (fuel2 - 1)
        in
        // Thrift compact protocol: when the high-nibble field-id delta is 0,
        // the field id is encoded inline as a zigzag-i16 varint; otherwise it
        // is `prev_id + delta`. We decode the inline varint once and zigzag-
        // decode it (the previous code skipped zigzag, so for any field id
        // >= 16 we would land on the wrong field id and chain a bad
        // prev_id forward through the rest of the struct).
        let id_and_value_pos =
          if delta = 0 then
            match decode_varint_hex (pos + 2) 0 0 (fuel - 1) with
            | None -> None
            | Some (raw, p) -> Some (zigzag_decode_nat raw, p)
          else Some (prev_id + delta, pos + 2)
        in
        (match id_and_value_pos with
         | None -> None
         | Some (field_id, value_pos) ->
           (match skip_compact_value_hex hex ftype value_pos (fuel - 1) with
            | None -> None
            | Some next ->
              if field_id = target_id then
                Some { cf_id = field_id; cf_type = ftype; cf_value_start = value_pos; cf_next = next }
              else
                nth_field_hex hex target_id next field_id (fuel - 1)))

let probe_parquet_num_rows (path:string) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 3 0 0 meta_hex_len with
        | None -> None
        | Some field ->
          if field.cf_type <> compact_t_i64 then None
          else
            match decode_varint_value_hex meta_hex field.cf_value_start 0 0 meta_hex_len with
            | None -> None
            | Some raw -> Some (zigzag_decode_nat raw)
      else None

let probe_parquet_row_group_count (path:string) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some field ->
          if field.cf_type <> compact_t_list then None
          else decode_compact_list_count_hex meta_hex field.cf_value_start meta_hex_len
      else None

let probe_parquet_first_row_group_num_rows (path:string) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some field ->
          if field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex field.cf_value_start meta_hex_len with
            | None -> None
            | Some info ->
              if info.cli_count = 0 || info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 3 info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some row_group_field ->
                  if row_group_field.cf_type <> compact_t_i64 then None
                  else
                    match decode_varint_value_hex meta_hex row_group_field.cf_value_start 0 0 meta_hex_len with
                    | None -> None
                    | Some raw -> Some (zigzag_decode_nat raw)
      else None

let probe_parquet_first_row_group_column_count (path:string) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some field ->
          if field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex field.cf_value_start meta_hex_len with
            | None -> None
            | Some info ->
              if info.cli_count = 0 || info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some row_group_field ->
                  if row_group_field.cf_type <> compact_t_list then None
                  else decode_compact_list_count_hex meta_hex row_group_field.cf_value_start meta_hex_len
      else None

let probe_parquet_first_column_name (path:string) : option string =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start 0 meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 3 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some path_field ->
                            if path_field.cf_type <> compact_t_list then None
                            else
                              match nth_compact_list_element_start_hex meta_hex path_field.cf_value_start 0 meta_hex_len with
                              | None -> None
                              | Some path_start -> decode_compact_binary_hex meta_hex path_start meta_hex_len
      else None

let probe_parquet_first_column_data_page_offset (path:string) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start 0 meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 9 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some offset_field ->
                            if offset_field.cf_type <> compact_t_i64 then None
                            else
                              match decode_varint_value_hex meta_hex offset_field.cf_value_start 0 0 meta_hex_len with
                              | None -> None
                              | Some raw -> Some (zigzag_decode_nat raw)
      else None

let probe_parquet_column_name (path:string) (col_index:nat) : option string =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start col_index meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 3 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some path_field ->
                            if path_field.cf_type <> compact_t_list then None
                            else
                              match nth_compact_list_element_start_hex meta_hex path_field.cf_value_start 0 meta_hex_len with
                              | None -> None
                              | Some path_start -> decode_compact_binary_hex meta_hex path_start meta_hex_len
      else None

let probe_parquet_column_num_values (path:string) (col_index:nat) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start col_index meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 5 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some num_values_field ->
                            if num_values_field.cf_type <> compact_t_i64 then None
                            else
                              match decode_varint_value_hex meta_hex num_values_field.cf_value_start 0 0 meta_hex_len with
                              | None -> None
                              | Some raw -> Some (zigzag_decode_nat raw)
      else None

let probe_parquet_column_total_compressed_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start col_index meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 7 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some size_field ->
                            if size_field.cf_type <> compact_t_i64 then None
                            else
                              match decode_varint_value_hex meta_hex size_field.cf_value_start 0 0 meta_hex_len with
                              | None -> None
                              | Some raw -> Some (zigzag_decode_nat raw)
      else None

let probe_parquet_column_total_uncompressed_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start col_index meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 6 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some size_field ->
                            if size_field.cf_type <> compact_t_i64 then None
                            else
                              match decode_varint_value_hex meta_hex size_field.cf_value_start 0 0 meta_hex_len with
                              | None -> None
                              | Some raw -> Some (zigzag_decode_nat raw)
      else None

let parquet_compression_codec_name (n:nat) : string =
  if n = 0 then "UNCOMPRESSED"
  else if n = 1 then "SNAPPY"
  else if n = 2 then "GZIP"
  else if n = 3 then "LZO"
  else if n = 4 then "BROTLI"
  else if n = 5 then "LZ4"
  else if n = 6 then "ZSTD"
  else if n = 7 then "LZ4_RAW"
  else "UNKNOWN"

let probe_parquet_column_compression_codec (path:string) (col_index:nat) : option string =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start col_index meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 4 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some codec_field ->
                            if codec_field.cf_type <> compact_t_i32 then None
                            else
                              match decode_varint_value_hex meta_hex codec_field.cf_value_start 0 0 meta_hex_len with
                              | None -> None
                              | Some raw -> Some (parquet_compression_codec_name (zigzag_decode_nat raw))
      else None

let probe_parquet_column_data_page_offset (path:string) (col_index:nat) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start col_index meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 9 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some offset_field ->
                            if offset_field.cf_type <> compact_t_i64 then None
                            else
                              match decode_varint_value_hex meta_hex offset_field.cf_value_start 0 0 meta_hex_len with
                              | None -> None
                              | Some raw -> Some (zigzag_decode_nat raw)
      else None

let parquet_page_type_name (n:nat) : string =
  if n = 0 then "DATA_PAGE"
  else if n = 1 then "INDEX_PAGE"
  else if n = 2 then "DICTIONARY_PAGE"
  else if n = 3 then "DATA_PAGE_V2"
  else "UNKNOWN"

let parquet_encoding_name (n:nat) : string =
  if n = 0 then "PLAIN"
  else if n = 1 then "GROUP_VAR_INT"
  else if n = 2 then "PLAIN_DICTIONARY"
  else if n = 3 then "RLE"
  else if n = 4 then "BIT_PACKED"
  else if n = 5 then "DELTA_BINARY_PACKED"
  else if n = 6 then "DELTA_LENGTH_BYTE_ARRAY"
  else if n = 7 then "DELTA_BYTE_ARRAY"
  else if n = 8 then "RLE_DICTIONARY"
  else if n = 9 then "BYTE_STREAM_SPLIT"
  else "UNKNOWN"

let rec nat_mod (x:nat) (y:nat { y > 0 }) : Tot nat (decreases x) =
  if x < y then x else nat_mod (x - y) y

let zstd_block_type_name (n:nat) : string =
  if n = 0 then "RAW"
  else if n = 1 then "RLE"
  else if n = 2 then "COMPRESSED"
  else if n = 3 then "RESERVED"
  else "UNKNOWN"

let zstd_frame_content_size_field_bytes (descriptor:nat { descriptor < 256 }) : nat =
  let fcs_flag = descriptor / 64 in
  let single_segment = nat_mod (descriptor / 32) 2 in
  if fcs_flag = 0 then
    if single_segment = 1 then 1 else 0
  else if fcs_flag = 1 then 2
  else if fcs_flag = 2 then 4
  else 8

let zstd_dictionary_id_field_bytes (descriptor:nat { descriptor < 256 }) : nat =
  let did_flag = nat_mod descriptor 4 in
  if did_flag = 0 then 0
  else if did_flag = 1 then 1
  else if did_flag = 2 then 2
  else 4

let zstd_window_descriptor_bytes (descriptor:nat { descriptor < 256 }) : nat =
  let single_segment = nat_mod (descriptor / 32) 2 in
  if single_segment = 1 then 0 else 1

let probe_parquet_column_page_header_type (path:string) (col_index:nat) : option string =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 1 0 0 (String.length page_hex) with
      | None -> None
      | Some type_field ->
        if type_field.cf_type <> compact_t_i32 then None
        else
          match decode_varint_value_hex page_hex type_field.cf_value_start 0 0 (String.length page_hex) with
          | None -> None
          | Some raw -> Some (parquet_page_type_name (zigzag_decode_nat raw))

let probe_parquet_column_page_header_uncompressed_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 2 0 0 (String.length page_hex) with
      | None -> None
      | Some size_field ->
        if size_field.cf_type <> compact_t_i32 then None
        else
          match decode_varint_value_hex page_hex size_field.cf_value_start 0 0 (String.length page_hex) with
          | None -> None
          | Some raw -> Some (zigzag_decode_nat raw)

let probe_parquet_column_page_header_compressed_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 3 0 0 (String.length page_hex) with
      | None -> None
      | Some size_field ->
        if size_field.cf_type <> compact_t_i32 then None
        else
          match decode_varint_value_hex page_hex size_field.cf_value_start 0 0 (String.length page_hex) with
          | None -> None
          | Some raw -> Some (zigzag_decode_nat raw)

let probe_parquet_column_page_header_num_values (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 5 0 0 (String.length page_hex) with
      | None -> None
      | Some data_page_header_field ->
        if data_page_header_field.cf_type <> compact_t_struct then None
        else
          match nth_field_hex page_hex 1 data_page_header_field.cf_value_start 0 (String.length page_hex) with
          | None -> None
          | Some num_values_field ->
            if num_values_field.cf_type <> compact_t_i32 then None
            else
              match decode_varint_value_hex page_hex num_values_field.cf_value_start 0 0 (String.length page_hex) with
              | None -> None
              | Some raw -> Some (zigzag_decode_nat raw)

let probe_parquet_column_page_header_length (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match skip_struct_fields_hex page_hex 0 (String.length page_hex) with
      | None -> None
      | Some end_hex -> Some (end_hex / 2)

let probe_parquet_column_page_payload_offset (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset path col_index,
        probe_parquet_column_page_header_length path col_index with
  | Some page_offset, Some header_len -> Some (page_offset + header_len)
  | _ -> None

let probe_parquet_column_page_header_data_encoding (path:string) (col_index:nat) : option string =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 5 0 0 (String.length page_hex) with
      | None -> None
      | Some data_page_header_field ->
        if data_page_header_field.cf_type <> compact_t_struct then None
        else
          match nth_field_hex page_hex 2 data_page_header_field.cf_value_start 0 (String.length page_hex) with
          | None -> None
          | Some encoding_field ->
            if encoding_field.cf_type <> compact_t_i32 then None
            else
              match decode_varint_value_hex page_hex encoding_field.cf_value_start 0 0 (String.length page_hex) with
              | None -> None
              | Some raw -> Some (parquet_encoding_name (zigzag_decode_nat raw))

let probe_parquet_column_page_header_definition_level_encoding (path:string) (col_index:nat) : option string =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 5 0 0 (String.length page_hex) with
      | None -> None
      | Some data_page_header_field ->
        if data_page_header_field.cf_type <> compact_t_struct then None
        else
          match nth_field_hex page_hex 3 data_page_header_field.cf_value_start 0 (String.length page_hex) with
          | None -> None
          | Some encoding_field ->
            if encoding_field.cf_type <> compact_t_i32 then None
            else
              match decode_varint_value_hex page_hex encoding_field.cf_value_start 0 0 (String.length page_hex) with
              | None -> None
              | Some raw -> Some (parquet_encoding_name (zigzag_decode_nat raw))

let probe_parquet_column_page_header_repetition_level_encoding (path:string) (col_index:nat) : option string =
  match probe_parquet_column_data_page_offset path col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 5 0 0 (String.length page_hex) with
      | None -> None
      | Some data_page_header_field ->
        if data_page_header_field.cf_type <> compact_t_struct then None
        else
          match nth_field_hex page_hex 4 data_page_header_field.cf_value_start 0 (String.length page_hex) with
          | None -> None
          | Some encoding_field ->
            if encoding_field.cf_type <> compact_t_i32 then None
            else
              match decode_varint_value_hex page_hex encoding_field.cf_value_start 0 0 (String.length page_hex) with
              | None -> None
              | Some raw -> Some (parquet_encoding_name (zigzag_decode_nat raw))

let probe_parquet_column_page_payload_magic_hex (path:string) (col_index:nat) : option string =
  match probe_parquet_column_page_payload_offset path col_index with
  | None -> None
  | Some payload_offset ->
    match parquet_read_range_hex path payload_offset 4 with
    | None -> None
    | Some payload_hex ->
      if String.length payload_hex >= 8 then Some (String.sub payload_hex 0 8) else None

let probe_parquet_column_zstd_frame_header_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_page_payload_offset path col_index with
  | None -> None
  | Some payload_offset ->
    match parquet_read_range_hex path payload_offset 18 with
    | None -> None
    | Some payload_hex ->
      if String.length payload_hex < 10 then None
      else
        match byte_at_hex payload_hex 8 with
        | None -> None
        | Some descriptor ->
          Some
            (4 + 1 +
             zstd_window_descriptor_bytes descriptor +
             zstd_dictionary_id_field_bytes descriptor +
             zstd_frame_content_size_field_bytes descriptor)

let probe_parquet_column_zstd_first_block_type (path:string) (col_index:nat) : option string =
  match probe_parquet_column_page_payload_offset path col_index with
  | None -> None
  | Some payload_offset ->
    match probe_parquet_column_zstd_frame_header_size path col_index with
    | None -> None
    | Some frame_header_size ->
      match parquet_read_range_hex path (payload_offset + frame_header_size) 3 with
      | None -> None
      | Some block_hex ->
        if String.length block_hex < 6 then None
        else
          match le_u24_at_hex block_hex 0 with
          | None -> None
          | Some block_header ->
            let block_type = nat_mod (block_header / 2) 4 in
            Some (zstd_block_type_name block_type)

let probe_parquet_column_zstd_first_block_last_flag (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_page_payload_offset path col_index with
  | None -> None
  | Some payload_offset ->
    match probe_parquet_column_zstd_frame_header_size path col_index with
    | None -> None
    | Some frame_header_size ->
      match parquet_read_range_hex path (payload_offset + frame_header_size) 3 with
      | None -> None
      | Some block_hex ->
        if String.length block_hex < 6 then None
        else
          match le_u24_at_hex block_hex 0 with
          | None -> None
          | Some block_header -> Some (nat_mod block_header 2)

let probe_parquet_column_zstd_first_block_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_page_payload_offset path col_index with
  | None -> None
  | Some payload_offset ->
    match probe_parquet_column_zstd_frame_header_size path col_index with
    | None -> None
    | Some frame_header_size ->
      match parquet_read_range_hex path (payload_offset + frame_header_size) 3 with
      | None -> None
      | Some block_hex ->
        if String.length block_hex < 6 then None
        else
          match le_u24_at_hex block_hex 0 with
          | None -> None
          | Some block_header -> Some (block_header / 8)

let probe_parquet_column_zstd_first_block_header_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_zstd_first_block_type path col_index with
  | None -> None
  | Some _ -> Some 3

let probe_parquet_column_zstd_first_block_payload_offset (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_page_payload_offset path col_index,
        probe_parquet_column_zstd_frame_header_size path col_index,
        probe_parquet_column_zstd_first_block_header_size path col_index with
  | Some payload_offset, Some frame_header_size, Some block_header_size ->
    Some (payload_offset + frame_header_size + block_header_size)
  | _ -> None

let probe_parquet_column_zstd_frame_accounted_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_zstd_frame_header_size path col_index,
        probe_parquet_column_zstd_first_block_header_size path col_index,
        probe_parquet_column_zstd_first_block_size path col_index with
  | Some frame_header_size, Some block_header_size, Some block_size ->
    Some (frame_header_size + block_header_size + block_size)
  | _ -> None

let probe_parquet_column_zstd_frame_size_matches_page (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_page_header_compressed_size path col_index,
        probe_parquet_column_zstd_frame_accounted_size path col_index with
  | Some page_compressed_size, Some accounted ->
    if page_compressed_size = accounted then Some 1 else Some 0
  | _ -> None

let probe_parquet_column_decompressed_payload_hex (path:string) (col_index:nat) : option string =
  match probe_parquet_column_page_payload_offset path col_index with
  | None -> None
  | Some payload_offset ->
    match probe_parquet_column_page_header_compressed_size path col_index with
    | None -> None
    | Some compressed_size ->
      match probe_parquet_column_page_header_uncompressed_size path col_index with
      | None -> None
      | Some uncompressed_size ->
        match parquet_read_range_hex path payload_offset compressed_size with
        | None -> None
        | Some compressed_hex ->
          parquet_zstd_decompress_hex compressed_hex uncompressed_size

let probe_parquet_column_decompressed_payload_prefix_hex (path:string) (col_index:nat) (prefix_bytes:nat) : option string =
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | None -> None
  | Some payload_hex ->
    let want = prefix_bytes + prefix_bytes in
    if want <= String.length payload_hex then Some (String.sub payload_hex 0 want)
    else Some payload_hex

let probe_parquet_column_decompressed_payload_hex_length (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | None -> None
  | Some payload_hex -> Some (String.length payload_hex / 2)

let probe_parquet_column_first_level_section_length (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | None -> None
  | Some payload_hex ->
    if String.length payload_hex < 8 then None
    else le_u32_at_hex payload_hex 0

let probe_parquet_column_delta_length_byte_array_values_offset (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_first_level_section_length path col_index with
  | None -> None
  | Some section_len -> Some (4 + section_len)

let probe_parquet_column_delta_length_byte_array_values_prefix_hex (path:string) (col_index:nat) (prefix_bytes:nat)
  : option string =
  match probe_parquet_column_decompressed_payload_hex path col_index,
        probe_parquet_column_delta_length_byte_array_values_offset path col_index with
  | Some payload_hex, Some value_offset ->
    let start = value_offset + value_offset in
    if start > String.length payload_hex then None
    else
      let remaining = String.length payload_hex - start in
      let want = prefix_bytes + prefix_bytes in
      let take = if want <= remaining then want else remaining in
      Some (String.sub payload_hex start take)
  | _ -> None

let probe_parquet_column_delta_length_byte_array_block_size (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path col_index 32 with
  | None -> None
  | Some values_hex ->
    match decode_varint_value_with_end_hex values_hex 0 0 0 (String.length values_hex) with
    | None -> None
    | Some (n, _) -> Some n

let probe_parquet_column_delta_length_byte_array_miniblock_count (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path col_index 32 with
  | None -> None
  | Some values_hex ->
    match decode_varint_value_with_end_hex values_hex 0 0 0 (String.length values_hex) with
    | None -> None
    | Some (_, p1) ->
      match decode_varint_value_with_end_hex values_hex p1 0 0 (String.length values_hex) with
      | None -> None
      | Some (n, _) -> Some n

let probe_parquet_column_delta_length_byte_array_value_count (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path col_index 32 with
  | None -> None
  | Some values_hex ->
    match decode_varint_value_with_end_hex values_hex 0 0 0 (String.length values_hex) with
    | None -> None
    | Some (_, p1) ->
      match decode_varint_value_with_end_hex values_hex p1 0 0 (String.length values_hex) with
      | None -> None
      | Some (_, p2) ->
        match decode_varint_value_with_end_hex values_hex p2 0 0 (String.length values_hex) with
        | None -> None
        | Some (n, _) -> Some n

let probe_parquet_column_delta_length_byte_array_first_length (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path col_index 32 with
  | None -> None
  | Some values_hex ->
    match decode_varint_value_with_end_hex values_hex 0 0 0 (String.length values_hex) with
    | None -> None
    | Some (_, p1) ->
      match decode_varint_value_with_end_hex values_hex p1 0 0 (String.length values_hex) with
      | None -> None
      | Some (_, p2) ->
        match decode_varint_value_with_end_hex values_hex p2 0 0 (String.length values_hex) with
        | None -> None
        | Some (_, p3) ->
          match decode_varint_value_with_end_hex values_hex p3 0 0 (String.length values_hex) with
          | None -> None
          | Some (raw, _) -> Some (zigzag_decode_nat raw)

let probe_parquet_column_delta_length_byte_array_first_min_delta (path:string) (col_index:nat) : option int =
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path col_index 64 with
  | None -> None
  | Some values_hex ->
    match decode_varint_value_with_end_hex values_hex 0 0 0 (String.length values_hex) with
    | None -> None
    | Some (_, p1) ->
      match decode_varint_value_with_end_hex values_hex p1 0 0 (String.length values_hex) with
      | None -> None
      | Some (_, p2) ->
        match decode_varint_value_with_end_hex values_hex p2 0 0 (String.length values_hex) with
        | None -> None
        | Some (_, p3) ->
          match decode_varint_value_with_end_hex values_hex p3 0 0 (String.length values_hex) with
          | None -> None
          | Some (_, p4) ->
            match decode_varint_value_with_end_hex values_hex p4 0 0 (String.length values_hex) with
            | None -> None
            | Some (raw, _) -> Some (zigzag_decode_int raw)

let probe_parquet_column_delta_length_byte_array_first_bit_width (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path col_index 64 with
  | None -> None
  | Some values_hex ->
    match decode_varint_value_with_end_hex values_hex 0 0 0 (String.length values_hex) with
    | None -> None
    | Some (_, p1) ->
      match decode_varint_value_with_end_hex values_hex p1 0 0 (String.length values_hex) with
      | None -> None
      | Some (_, p2) ->
        match decode_varint_value_with_end_hex values_hex p2 0 0 (String.length values_hex) with
        | None -> None
        | Some (_, p3) ->
          match decode_varint_value_with_end_hex values_hex p3 0 0 (String.length values_hex) with
          | None -> None
          | Some (_, p4) ->
            match decode_varint_value_with_end_hex values_hex p4 0 0 (String.length values_hex) with
            | None -> None
            | Some (_, p5) ->
              if p5 + 1 >= String.length values_hex then None
              else
                match byte_at_hex values_hex p5 with
                | None -> None
                | Some width -> Some width

let rec packed_lsb_value_hex (hex:string) (byte_start:nat) (start_bit:nat) (remaining:nat) (out_shift:nat) (acc:nat)
  : Tot (option nat) (decreases remaining) =
  if remaining = 0 then Some acc
  else
    let absolute_bit = start_bit + out_shift in
    let byte_index = byte_start + mul_nat (absolute_bit / 8) 2 in
    if byte_index + 1 >= String.length hex then None
    else
      match byte_at_hex hex byte_index with
      | None -> None
      | Some b ->
        let bit_in_byte = absolute_bit % 8 in
        let bit = (b / scale_pow2 1 bit_in_byte) % 2 in
        let acc' = if bit = 0 then acc else acc + scale_pow2 1 out_shift in
        packed_lsb_value_hex hex byte_start start_bit (remaining - 1) (out_shift + 1) acc'

let probe_parquet_column_delta_length_byte_array_length_at (path:string) (col_index:nat) (value_index:nat) : option int =
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path col_index 96 with
  | None -> None
  | Some values_hex ->
    match decode_varint_value_with_end_hex values_hex 0 0 0 (String.length values_hex) with
    | None -> None
    | Some (_, p1) ->
      match decode_varint_value_with_end_hex values_hex p1 0 0 (String.length values_hex) with
      | None -> None
      | Some (_, p2) ->
        match decode_varint_value_with_end_hex values_hex p2 0 0 (String.length values_hex) with
        | None -> None
        | Some (_, p3) ->
          match decode_varint_value_with_end_hex values_hex p3 0 0 (String.length values_hex) with
          | None -> None
          | Some (first_raw, p4) ->
            let first_len = zigzag_decode_int first_raw in
            if value_index = 0 then Some first_len
            else
              match decode_varint_value_with_end_hex values_hex p4 0 0 (String.length values_hex) with
              | None -> None
              | Some (min_delta_raw, p5) ->
                let min_delta = zigzag_decode_int min_delta_raw in
                if p5 + 1 >= String.length values_hex then None
                else
                  match byte_at_hex values_hex p5 with
                  | None -> None
                  | Some width ->
                    let packed_start = p5 + 16 in
                    let rec accumulate_lengths (delta_index:nat) (current:int)
                      : Tot (option int) (decreases (value_index - delta_index)) =
                      if delta_index >= value_index then Some current
                      else
                        let start_bit = mul_nat delta_index width in
                        match packed_lsb_value_hex values_hex packed_start start_bit width 0 0 with
                        | None -> None
                        | Some adjusted ->
                          let next = current + min_delta + adjusted in
                          let delta_index' = succ_nat delta_index in
                          assert (value_index - delta_index' < value_index - delta_index);
                          accumulate_lengths delta_index' next
                    in
                    accumulate_lengths 0 first_len

let rec count_used_miniblocks (remaining:nat) (values_per_miniblock:nat { values_per_miniblock > 0 })
  : Tot nat (decreases remaining) =
  if remaining = 0 then 0
  else if remaining <= values_per_miniblock then 1
  else succ_nat (count_used_miniblocks (remaining - values_per_miniblock) values_per_miniblock)

let probe_parquet_column_delta_length_byte_array_length_nat_at (path:string) (col_index:nat) (value_index:nat) : option nat =
  match probe_parquet_column_delta_length_byte_array_length_at path col_index value_index with
  | None -> None
  | Some n ->
    if n < 0 then None else Some n

let probe_parquet_column_delta_length_byte_array_total_value_bytes (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_delta_length_byte_array_value_count path col_index with
  | None -> None
  | Some value_count ->
    let rec loop (remaining:nat) (idx:nat) (acc:nat)
      : Tot (option nat) (decreases remaining) =
      if remaining = 0 then Some acc
      else
        match probe_parquet_column_delta_length_byte_array_length_nat_at path col_index idx with
        | None -> None
        | Some len ->
          loop (pred_nat remaining) (succ_nat idx) (acc + len)
    in
    loop value_count 0 0

let probe_parquet_column_delta_length_byte_array_value_data_offset (path:string) (col_index:nat) : option nat =
  match probe_parquet_column_decompressed_payload_hex_length path col_index,
        probe_parquet_column_delta_length_byte_array_values_offset path col_index,
        probe_parquet_column_delta_length_byte_array_total_value_bytes path col_index with
  | Some payload_len, Some values_offset, Some total_value_bytes ->
    if values_offset > payload_len then None
    else
      let values_stream_len = payload_len - values_offset in
      if total_value_bytes > values_stream_len then None
      else Some (values_stream_len - total_value_bytes)
  | _ -> None

let rec ascii_string_of_hex_slice (hex:string) (pos:nat) (remaining:nat) (acc:list FStar.Char.char)
  : Tot (option string) (decreases remaining) =
  if remaining = 0 then Some (String.string_of_list (List.Tot.rev acc))
  else if pos + 1 >= String.length hex then None
  else
    match byte_at_hex hex pos with
    | None -> None
    | Some b ->
      ascii_string_of_hex_slice hex (pos + 2) (remaining - 1) ((FStar.Char.char_of_int b) :: acc)

let probe_parquet_column_delta_length_byte_array_value_hex_at (path:string) (col_index:nat) (value_index:nat) : option string =
  match probe_parquet_column_decompressed_payload_hex path col_index,
        probe_parquet_column_delta_length_byte_array_values_offset path col_index,
        probe_parquet_column_delta_length_byte_array_value_data_offset path col_index with
  | Some payload_hex, Some values_offset, Some value_data_offset ->
    let values_start = values_offset + value_data_offset in
    let rec sum_previous_lengths (remaining:nat) (idx:nat) (acc:nat)
      : Tot (option nat) (decreases remaining) =
      if remaining = 0 then Some acc
      else
        match probe_parquet_column_delta_length_byte_array_length_nat_at path col_index idx with
        | None -> None
        | Some len ->
          sum_previous_lengths (pred_nat remaining) (succ_nat idx) (acc + len)
    in
    (match sum_previous_lengths value_index 0 0,
            probe_parquet_column_delta_length_byte_array_length_nat_at path col_index value_index with
     | Some prior_len, Some value_len ->
       let start_byte = values_start + prior_len in
       let start = mul_nat start_byte 2 in
       let want = mul_nat value_len 2 in
       if start + want <= String.length payload_hex then Some (String.sub payload_hex start want) else None
     | _ -> None)
  | _ -> None

let probe_parquet_column_delta_length_byte_array_value_string_at (path:string) (col_index:nat) (value_index:nat) : option string =
  match probe_parquet_column_delta_length_byte_array_value_hex_at path col_index value_index with
  | None -> None
  | Some value_hex ->
    ascii_string_of_hex_slice value_hex 0 (String.length value_hex / 2) []

// ---------------------------------------------------------------------------
// Bulk page-level decode for DELTA_LENGTH_BYTE_ARRAY columns.
//
// The legacy `_value_string_at` accessors above are O(N^2) per column:
// each row pays for re-decompressing the page payload, re-walking every
// prior length, and re-slicing the value byte stream. For the 3.14 M-quad
// UK Parliament COTTAS that adds up to ~12.6 M re-probes per `COUNT(*)`.
//
// This block replaces the per-row work with three single passes:
//   (a) one decompression of the column page,
//   (b) one decode of the bit-packed length deltas into a length list,
//   (c) one running prefix-sum over those lengths to slice all values.
//
// The result is a `dlba_page_cache` record that is consumed by the OCaml
// glue (cottas_runtime.sh) to materialise all rows of one column with a
// single F* call. See docs/designissues/2026-04-25-cottas-perf-fix-plan.md
// for the full plan.
// ---------------------------------------------------------------------------

noeq type dlba_page_cache = {
  dpc_payload_hex : string;       // full decompressed page bytes (hex)
  dpc_values_offset : nat;        // byte offset of the varint header
  dpc_value_count : nat;          // total values on the page
  dpc_first_length : nat;         // first length, post-zigzag
  dpc_min_delta : int;            // miniblock minimum delta (block-level)
  dpc_bit_width : nat;            // first miniblock bit width
  dpc_packed_start : nat;         // hex offset of the bit-packed deltas
  dpc_value_data_offset : nat;    // byte offset of contiguous value bytes
                                  //  (relative to values_offset)
  dpc_lengths : list nat;         // decoded lengths in row order, length = dpc_value_count
  dpc_value_starts : list nat;    // start-byte offsets relative to values_start
                                  //  (length = dpc_value_count)
}

// Decode a single packed length delta from the bit-packed stream and return
// the total length. Mirrors the inner step of `accumulate_lengths` from
// `probe_parquet_column_delta_length_byte_array_length_at`.
let decode_one_dlba_delta
  (values_hex:string) (packed_start:nat) (bit_width:nat)
  (min_delta:int) (delta_index:nat) (current_len:int)
  : option int =
  let start_bit = mul_nat delta_index bit_width in
  match packed_lsb_value_hex values_hex packed_start start_bit bit_width 0 0 with
  | None -> None
  | Some adjusted -> Some (current_len + min_delta + adjusted)

// Decode a single packed length delta using an explicit miniblock-relative
// `mb_pos` (so each miniblock's bit-packed area is independent — the delta
// at index 0 within a miniblock starts at `packed_start` itself). Mirrors
// `decode_one_dlba_delta` but indexed against the active miniblock's start.
let decode_one_dlba_delta_at_miniblock
  (values_hex:string) (mb_packed_start:nat) (bit_width:nat)
  (min_delta:int) (mb_pos:nat) (current_len:int)
  : option int =
  let start_bit = mul_nat mb_pos bit_width in
  match packed_lsb_value_hex values_hex mb_packed_start start_bit bit_width 0 0 with
  | None -> None
  | Some adjusted -> Some (current_len + min_delta + adjusted)

// Hex chars consumed by a complete miniblock at the given width.
//   values_per_miniblock * bit_width bits
// = values_per_miniblock * bit_width / 8 bytes
// = values_per_miniblock * bit_width / 4 hex chars
// `values_per_miniblock` is required by the Parquet spec to be a multiple
// of 8, so this is exact.
let miniblock_hex_size (values_per_miniblock:nat) (bit_width:nat) : nat =
  mul_nat values_per_miniblock bit_width / 4

// Read the `idx`-th width byte (one byte per miniblock) starting at
// `widths_offset` (hex offset). Each width byte is two hex chars.
let widths_byte_at (values_hex:string) (widths_offset:nat) (idx:nat) : option nat =
  let p = widths_offset + mul_nat idx 2 in
  if p + 1 >= String.length values_hex then None
  else
    match byte_at_hex values_hex p with
    | None -> None
    | Some b -> let n : nat = b in Some n

// Walk the bit-packed length deltas across every (block, miniblock, value)
// position to build the list of all `value_count` lengths.
//
// State threaded through the recursion:
//   `min_delta`         — current block's zigzag-decoded min delta
//   `widths_offset`     — hex offset of the current block's bit_widths[]
//   `mb_packed_start`   — hex offset of the current miniblock's packed area
//   `bit_width`         — current miniblock's bit width
//   `mb_idx`            — index of the current miniblock within the block
//                         (0..miniblocks-1)
//   `mb_pos`            — position within the current miniblock
//                         (0..values_per_miniblock-1)
//
// Each iteration consumes one value (one width-bit-packed delta). At
// miniblock boundaries we advance `mb_packed_start` past the just-finished
// miniblock and pick up the next miniblock's width byte. At block
// boundaries we re-read `min_delta` (varint) and the new bit_widths[]
// array, then start at miniblock 0.
let rec build_dlba_length_list
  (values_hex:string) (vh_len:nat) (block_size:nat) (miniblocks:nat)
  (values_per_miniblock:nat)
  (min_delta:int) (widths_offset:nat) (mb_packed_start:nat) (bit_width:nat)
  (mb_idx:nat) (mb_pos:nat)
  (remaining:nat) (current_len:int) (acc:list nat)
  : Tot (option (list nat)) (decreases remaining) =
  if remaining = 0 then Some (List.Tot.rev acc)
  else if current_len < 0 then None
  // values_per_miniblock must be positive for the miniblock-pos arithmetic
  // to be meaningful; the caller establishes this but we re-guard here so
  // the function is total over its declared signature.
  else if values_per_miniblock = 0 then None
  else
    let safe_len : nat = current_len in
    let acc' = safe_len :: acc in
    if remaining = 1 then Some (List.Tot.rev acc')
    else
      // Advance one position; figure out where the *next* value lives.
      let mb_pos' = mb_pos + 1 in
      if mb_pos' < values_per_miniblock then
        // Still inside the same miniblock — just decode one more delta at
        // the next miniblock-relative position.
        match decode_one_dlba_delta_at_miniblock values_hex mb_packed_start
                bit_width min_delta mb_pos current_len with
        | None -> None
        | Some next_len ->
          build_dlba_length_list values_hex vh_len block_size miniblocks
            values_per_miniblock min_delta widths_offset mb_packed_start
            bit_width mb_idx mb_pos' (remaining - 1) next_len acc'
      else
        // Crossed a miniblock boundary. Decode the last delta of the
        // *current* miniblock first (it lives at mb_pos == values_per_miniblock - 1
        // within the current miniblock), then advance to the next miniblock.
        match decode_one_dlba_delta_at_miniblock values_hex mb_packed_start
                bit_width min_delta mb_pos current_len with
        | None -> None
        | Some next_len ->
          // Advance `mb_packed_start` past the miniblock we just exited.
          let next_mb_packed_start =
            mb_packed_start + miniblock_hex_size values_per_miniblock bit_width in
          let mb_idx' = mb_idx + 1 in
          if mb_idx' < miniblocks then
            // Next miniblock within the same block. Pick up its width byte.
            match widths_byte_at values_hex widths_offset mb_idx' with
            | None -> None
            | Some next_bw ->
              build_dlba_length_list values_hex vh_len block_size miniblocks
                values_per_miniblock min_delta widths_offset
                next_mb_packed_start next_bw mb_idx' 0
                (remaining - 1) next_len acc'
          else
            // Crossed a block boundary. The next bytes in `values_hex` are
            // the new block's `min_delta` varint, followed by `miniblocks`
            // width bytes, then the new packed area.
            match decode_varint_value_with_end_hex values_hex
                    next_mb_packed_start 0 0 vh_len with
            | None -> None
            | Some (md_raw, after_md) ->
              let new_min_delta = zigzag_decode_int md_raw in
              let new_widths_offset : nat = after_md in
              // miniblocks bytes of widths = 2 * miniblocks hex chars
              let new_packed_start : nat =
                new_widths_offset + mul_nat miniblocks 2 in
              if new_widths_offset + 1 >= String.length values_hex then None
              else
                match byte_at_hex values_hex new_widths_offset with
                | None -> None
                | Some new_bw ->
                  let new_bw_nat : nat = new_bw in
                  build_dlba_length_list values_hex vh_len block_size
                    miniblocks values_per_miniblock new_min_delta
                    new_widths_offset new_packed_start new_bw_nat 0 0
                    (remaining - 1) next_len acc'

// Build the running prefix-sum of value byte starts. `value_starts[0] = 0`,
// `value_starts[i+1] = value_starts[i] + lengths[i]`. Output has the same
// length as `lengths`.
let rec prefix_sums (lengths:list nat) (running:nat) (acc:list nat)
  : Tot (list nat) (decreases lengths) =
  match lengths with
  | [] -> List.Tot.rev acc
  | hd :: tl -> prefix_sums tl (running + hd) (running :: acc)

// Compute the total of a list of nats (zero-cost over the prefix sum, but
// we do it once at the end of the page-cache build to size the value-data
// region).
let rec sum_nat_list (xs:list nat) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | hd :: tl -> hd + sum_nat_list tl

// One-shot DELTA_LENGTH_BYTE_ARRAY page cache builder. Given a path + column
// index, decompress the page once, parse the four varints + bit_width, decode
// every length, and return the populated cache. All subsequent value lookups
// are O(1) string slices off `dpc_payload_hex`.
let probe_parquet_column_delta_length_byte_array_page_cache
  (path:string) (col_index:nat) : option dlba_page_cache =
  match probe_parquet_column_decompressed_payload_hex path col_index,
        probe_parquet_column_delta_length_byte_array_values_offset path col_index with
  | Some payload_hex, Some values_offset ->
    let payload_len_hex = String.length payload_hex in
    let values_start_hex = mul_nat values_offset 2 in
    if values_start_hex > payload_len_hex then None
    else
      let values_hex = String.sub payload_hex values_start_hex
                         (payload_len_hex - values_start_hex) in
      let vh_len = String.length values_hex in
      // Parse varint header: block_size, miniblocks, value_count, first_length,
      // then the first block's min_delta + bit_widths[miniblocks].
      // Per the Parquet DELTA_LENGTH_BYTE_ARRAY spec, bit_width changes per
      // miniblock and min_delta changes per block — `build_dlba_length_list`
      // re-reads them at each boundary.
      (match decode_varint_value_with_end_hex values_hex 0 0 0 vh_len with
       | None -> None
       | Some (block_size, p1) ->
         match decode_varint_value_with_end_hex values_hex p1 0 0 vh_len with
         | None -> None
         | Some (miniblocks, p2) ->
           if miniblocks = 0 then None
           else
           match decode_varint_value_with_end_hex values_hex p2 0 0 vh_len with
           | None -> None
           | Some (value_count, p3) ->
             match decode_varint_value_with_end_hex values_hex p3 0 0 vh_len with
             | None -> None
             | Some (first_raw, p4) ->
               let first_length = zigzag_decode_nat first_raw in
               match decode_varint_value_with_end_hex values_hex p4 0 0 vh_len with
               | None -> None
               | Some (min_delta_raw, p5) ->
                 let min_delta = zigzag_decode_int min_delta_raw in
                 if p5 + 1 >= vh_len then None
                 else
                   match byte_at_hex values_hex p5 with
                   | None -> None
                   | Some bit_width ->
                     // First block's bit_widths[] starts at p5; the packed
                     // data area for the first miniblock starts after all
                     // `miniblocks` width bytes (2 hex chars per byte).
                     let widths_offset = p5 in
                     let packed_start = p5 + mul_nat miniblocks 2 in
                     // miniblocks > 0 was already checked above, but the
                     // refinement is lost across the nested matches.
                     // `build_dlba_length_list` re-guards on
                     // values_per_miniblock=0 so the call site only needs a
                     // plain nat here. Re-wrap miniblocks via div_nat_pos
                     // to get a nat result (FStar/Prims `/` over int yields
                     // int).
                     let values_per_miniblock : nat =
                       if miniblocks > 0 then div_nat_pos block_size miniblocks
                       else 0 in
                     // Walk all `value_count` lengths in one pass.
                     match build_dlba_length_list values_hex vh_len
                             block_size miniblocks values_per_miniblock
                             min_delta widths_offset packed_start bit_width
                             0 0 value_count first_length [] with
                     | None -> None
                     | Some lengths ->
                       let total_value_bytes = sum_nat_list lengths in
                       let payload_byte_len = payload_len_hex / 2 in
                       if values_offset > payload_byte_len then None
                       else
                         let values_stream_len =
                           payload_byte_len - values_offset in
                         if total_value_bytes > values_stream_len then None
                         else
                           let value_data_offset =
                             values_stream_len - total_value_bytes in
                           let starts = prefix_sums lengths 0 [] in
                           Some {
                             dpc_payload_hex = payload_hex;
                             dpc_values_offset = values_offset;
                             dpc_value_count = value_count;
                             dpc_first_length = first_length;
                             dpc_min_delta = min_delta;
                             dpc_bit_width = bit_width;
                             dpc_packed_start = packed_start;
                             dpc_value_data_offset = value_data_offset;
                             dpc_lengths = lengths;
                             dpc_value_starts = starts;
                           })
  | _ -> None

// Walk a length / start pair list together and produce, for every row, the
// raw hex slice of the value bytes. Mirrors the inner string-slice of
// `_value_hex_at`. Output length == `lengths` length.
let rec slice_all_dlba_values
  (payload_hex:string) (values_start_byte:nat)
  (lengths:list nat) (starts:list nat) (acc:list (option string))
  : Tot (list (option string)) (decreases lengths) =
  match lengths, starts with
  | [], _ -> List.Tot.rev acc
  | _, [] -> List.Tot.rev acc
  | len :: lts, st :: sts ->
    let start_byte = values_start_byte + st in
    let start = mul_nat start_byte 2 in
    let want = mul_nat len 2 in
    let slice =
      if start + want <= String.length payload_hex
      then Some (String.sub payload_hex start want)
      else None in
    slice_all_dlba_values payload_hex values_start_byte lts sts (slice :: acc)

// Decode every value on the page into its hex slice in one shot.
let dlba_page_decode_all_value_hex (cache:dlba_page_cache) : list (option string) =
  let values_start_byte = cache.dpc_values_offset + cache.dpc_value_data_offset in
  slice_all_dlba_values cache.dpc_payload_hex values_start_byte
    cache.dpc_lengths cache.dpc_value_starts []

// Map a list of hex slices to their ASCII string decoding.
let rec ascii_strings_of_hex_slices (slices:list (option string)) (acc:list (option string))
  : Tot (list (option string)) (decreases slices) =
  match slices with
  | [] -> List.Tot.rev acc
  | None :: tl -> ascii_strings_of_hex_slices tl (None :: acc)
  | Some hx :: tl ->
    let s = ascii_string_of_hex_slice hx 0 (String.length hx / 2) [] in
    ascii_strings_of_hex_slices tl (s :: acc)

// Decode every value on the page directly to its ASCII string form.
let dlba_page_decode_all_strings (cache:dlba_page_cache) : list (option string) =
  ascii_strings_of_hex_slices (dlba_page_decode_all_value_hex cache) []

// One-shot column-bulk entry point. Returns the decoded ASCII string for
// every row in column `col_index`, or `None` if the column page cannot be
// decoded. This is what the OCaml COTTAS runtime calls instead of the per-
// row `_value_string_at` loop.
let probe_parquet_column_delta_length_byte_array_decode_all
  (path:string) (col_index:nat) : option (list (option string)) =
  match probe_parquet_column_delta_length_byte_array_page_cache path col_index with
  | None -> None
  | Some cache -> Some (dlba_page_decode_all_strings cache)

// ===========================================================================
// Issue #98 — RLE_DICTIONARY column decode.
//
// pycottas writes predicates (col 1) and graph-names (col 3) as
// RLE_DICTIONARY because their cardinality is small and repetition is
// heavy. The wire format for such a column is two pages:
//
//   1. Dictionary page (page header type=DICTIONARY_PAGE, encoding
//      PLAIN_DICTIONARY): payload is a sequence of length-prefixed BYTE_ARRAY
//      values. Each entry is `LE u32 length` followed by `length` bytes.
//      Number of entries = page_header.dictionary_page_header.num_values.
//   2. Data page (page header type=DATA_PAGE, encoding RLE_DICTIONARY):
//      payload's first byte = bit-width of indices into the dictionary.
//      Remaining bytes = hybrid RLE-bit-packed-encoded indices, count =
//      page_header.data_page_header.num_values.
//
// The dictionary page lives at column_metadata.dictionary_page_offset
// (Thrift field 14). The data page lives at column_metadata.data_page_offset
// (field 9, already supported by the existing helpers).
// ===========================================================================

// Field-14 lookup of column_metadata.dictionary_page_offset. Mirrors the
// shape of `probe_parquet_column_data_page_offset`.
let probe_parquet_column_dictionary_page_offset (path:string) (col_index:nat) : option nat =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if row_groups_info.cli_count = 0 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_field_hex meta_hex 1 row_groups_info.cli_payload_start 0 meta_hex_len with
                | None -> None
                | Some columns_field ->
                  if columns_field.cf_type <> compact_t_list then None
                  else
                    match nth_compact_list_element_start_hex meta_hex columns_field.cf_value_start col_index meta_hex_len with
                    | None -> None
                    | Some column_chunk_start ->
                      match nth_field_hex meta_hex 3 column_chunk_start 0 meta_hex_len with
                      | None -> None
                      | Some metadata_field ->
                        if metadata_field.cf_type <> compact_t_struct then None
                        else
                          match nth_field_hex meta_hex 14 metadata_field.cf_value_start 0 meta_hex_len with
                          | None -> None
                          | Some offset_field ->
                            if offset_field.cf_type <> compact_t_i64 then None
                            else
                              match decode_varint_value_hex meta_hex offset_field.cf_value_start 0 0 meta_hex_len with
                              | None -> None
                              | Some raw -> Some (zigzag_decode_nat raw)
      else None

// ---------------------------------------------------------------------------
// Page-header probes parameterised by an explicit page-start byte offset.
// The existing `probe_parquet_column_page_header_*` family hard-codes
// `data_page_offset`, but for an RLE_DICTIONARY column we must read the
// dictionary page header at `dictionary_page_offset` first. These helpers
// mirror the existing shape but take a `page_offset:nat`.
// ---------------------------------------------------------------------------

let parquet_page_header_uncompressed_size_at (path:string) (page_offset:nat) : option nat =
  match parquet_read_range_hex path page_offset 128 with
  | None -> None
  | Some page_hex ->
    match nth_field_hex page_hex 2 0 0 (String.length page_hex) with
    | None -> None
    | Some size_field ->
      if size_field.cf_type <> compact_t_i32 then None
      else
        match decode_varint_value_hex page_hex size_field.cf_value_start 0 0 (String.length page_hex) with
        | None -> None
        | Some raw -> Some (zigzag_decode_nat raw)

let parquet_page_header_compressed_size_at (path:string) (page_offset:nat) : option nat =
  match parquet_read_range_hex path page_offset 128 with
  | None -> None
  | Some page_hex ->
    match nth_field_hex page_hex 3 0 0 (String.length page_hex) with
    | None -> None
    | Some size_field ->
      if size_field.cf_type <> compact_t_i32 then None
      else
        match decode_varint_value_hex page_hex size_field.cf_value_start 0 0 (String.length page_hex) with
        | None -> None
        | Some raw -> Some (zigzag_decode_nat raw)

let parquet_page_header_length_at (path:string) (page_offset:nat) : option nat =
  match parquet_read_range_hex path page_offset 128 with
  | None -> None
  | Some page_hex ->
    match skip_struct_fields_hex page_hex 0 (String.length page_hex) with
    | None -> None
    | Some end_hex -> Some (end_hex / 2)

// Number of dictionary entries on a DICTIONARY_PAGE header. Field 7 of the
// page header is the dictionary_page_header struct; field 1 of that struct
// is its `num_values` (i32).
let parquet_dictionary_page_num_values_at (path:string) (page_offset:nat) : option nat =
  match parquet_read_range_hex path page_offset 128 with
  | None -> None
  | Some page_hex ->
    match nth_field_hex page_hex 7 0 0 (String.length page_hex) with
    | None -> None
    | Some dict_header_field ->
      if dict_header_field.cf_type <> compact_t_struct then None
      else
        match nth_field_hex page_hex 1 dict_header_field.cf_value_start 0 (String.length page_hex) with
        | None -> None
        | Some nv_field ->
          if nv_field.cf_type <> compact_t_i32 then None
          else
            match decode_varint_value_hex page_hex nv_field.cf_value_start 0 0 (String.length page_hex) with
            | None -> None
            | Some raw -> Some (zigzag_decode_nat raw)

// Decompress the page payload that begins at `page_offset` (header + payload
// in storage). Mirrors the body of
// `probe_parquet_column_decompressed_payload_hex`, but starting at an
// arbitrary page offset.
let parquet_decompressed_page_at (path:string) (page_offset:nat) : option string =
  match parquet_page_header_length_at path page_offset with
  | None -> None
  | Some header_len ->
    let payload_offset = page_offset + header_len in
    match parquet_page_header_compressed_size_at path page_offset with
    | None -> None
    | Some compressed_size ->
      match parquet_page_header_uncompressed_size_at path page_offset with
      | None -> None
      | Some uncompressed_size ->
        match parquet_read_range_hex path payload_offset compressed_size with
        | None -> None
        | Some compressed_hex ->
          parquet_zstd_decompress_hex compressed_hex uncompressed_size

// ---------------------------------------------------------------------------
// PLAIN_DICTIONARY parser: walk a sequence of `num_values` length-prefixed
// byte strings (LE u32 length, then `length` bytes of ASCII).
// ---------------------------------------------------------------------------

// Decode one dictionary entry starting at hex position `pos`. Returns
// `(entry_string, next_pos)` or None.
let decode_one_plain_dictionary_entry (payload_hex:string) (pos:nat) : option (string & nat) =
  // Need 4 bytes (8 hex chars) for the LE u32 length.
  if pos + 7 >= String.length payload_hex then None
  else
    match le_u32_at_hex payload_hex pos with
    | None -> None
    | Some entry_len ->
      let value_start = pos + 8 in
      let value_hex_len = entry_len + entry_len in
      let value_end = value_start + value_hex_len in
      if value_end > String.length payload_hex then None
      else
        let value_hex = String.sub payload_hex value_start value_hex_len in
        let s = ascii_string_of_hex_slice value_hex 0 entry_len [] in
        match s with
        | None -> None
        | Some str -> Some (str, value_end)

// Walk `num_values` PLAIN_DICTIONARY entries from the start of the
// decompressed dictionary-page payload. Output preserves entry order.
let rec decode_plain_dictionary_entries
  (payload_hex:string) (pos:nat) (remaining:nat) (acc:list string)
  : Tot (option (list string)) (decreases remaining) =
  if remaining = 0 then Some (List.Tot.rev acc)
  else
    match decode_one_plain_dictionary_entry payload_hex pos with
    | None -> None
    | Some (s, next_pos) ->
      decode_plain_dictionary_entries payload_hex next_pos (remaining - 1) (s :: acc)

// Top-level entry: start from offset 0 of the decompressed dictionary-page
// payload.
let decode_plain_dictionary (payload_hex:string) (num_values:nat) : option (list string) =
  decode_plain_dictionary_entries payload_hex 0 num_values []

// ---------------------------------------------------------------------------
// Hybrid RLE / bit-packed run decoder.
//
// Wire format (Parquet hybrid RLE, used by RLE_DICTIONARY data pages):
//   <varint header> <run-body>
//
//   header = (run_length << 1) | mode
//
//   mode = 0  =>  RLE run.
//                 run_length = repeat count.
//                 body       = a single value, packed as
//                              ceil(bit_width / 8) bytes, little-endian.
//   mode = 1  =>  bit-packed run.
//                 run_length = number of *groups of 8 values*.
//                 body       = `run_length * bit_width` bytes containing
//                              `run_length * 8` values, LSB-first within
//                              each byte (same packing as DLBA bit_widths).
//
// We decode runs back-to-back until `remaining` indices have been collected.
// ---------------------------------------------------------------------------

// Read `bit_width` bits as a single LSB-first value, starting at bit 0 of
// byte position `byte_start` (in hex chars). Reuses `packed_lsb_value_hex`.
let read_lsb_packed_value (hex:string) (byte_start:nat) (start_bit:nat) (bit_width:nat) : option nat =
  packed_lsb_value_hex hex byte_start start_bit bit_width 0 0

// Bytes (= 2 hex chars) consumed by an RLE run body of width `bit_width`.
//   ceil(bit_width / 8)
let rle_run_body_hex_size (bit_width:nat) : nat =
  let bytes = (bit_width + 7) / 8 in
  mul_nat bytes 2

// Read the single value of an RLE run as a little-endian unsigned int of
// `ceil(bit_width / 8)` bytes. Returns the value and the position past the
// body.
let rec read_le_uint_bytes (hex:string) (pos:nat) (remaining_bytes:nat) (shift:nat) (acc:nat)
  : Tot (option (nat & nat)) (decreases remaining_bytes) =
  if remaining_bytes = 0 then Some (acc, pos)
  else if pos + 1 >= String.length hex then None
  else
    match byte_at_hex hex pos with
    | None -> None
    | Some b ->
      let acc' = acc + scale_pow2 b shift in
      read_le_uint_bytes hex (pos + 2) (remaining_bytes - 1) (shift + 8) acc'

// Append `count` copies of `value` to `acc`. Used to materialise an RLE run.
let rec repeat_append (value:nat) (count:nat) (acc:list nat)
  : Tot (list nat) (decreases count) =
  if count = 0 then acc
  else repeat_append value (count - 1) (value :: acc)

// Decode `count` consecutive bit-packed indices starting at hex position
// `byte_start`, mb-pos 0 within that packed area. Each index is `bit_width`
// bits, LSB-first. Output is reverse-prepended to `acc` for tail-recursion;
// the caller reverses if needed.
let rec decode_bit_packed_indices
  (values_hex:string) (byte_start:nat) (bit_width:nat)
  (count:nat) (mb_pos:nat) (acc:list nat)
  : Tot (option (list nat)) (decreases count) =
  if count = 0 then Some acc
  else
    let start_bit = mul_nat mb_pos bit_width in
    match read_lsb_packed_value values_hex byte_start start_bit bit_width with
    | None -> None
    | Some v ->
      decode_bit_packed_indices values_hex byte_start bit_width
        (count - 1) (mb_pos + 1) (v :: acc)

// Decode hybrid RLE / bit-packed runs back-to-back until `remaining`
// indices have been collected. `pos` is the hex position of the next run's
// varint header. Output preserves index order.
//
// `fuel` bounds the run-iteration count; in practice it never blows up on
// real Parquet pages (each run consumes at least one index), but the F*
// totality checker needs an explicit decreasing measure.
let rec decode_hybrid_rle_runs
  (values_hex:string) (vh_len:nat) (pos:nat) (bit_width:nat)
  (remaining:nat) (acc:list nat) (fuel:nat)
  : Tot (option (list nat)) (decreases fuel) =
  if remaining = 0 then Some (List.Tot.rev acc)
  else if fuel = 0 then None
  else
    // 1. Read the run header (varint), then split: high bits = run_length,
    //    low bit = mode (0 = RLE, 1 = bit-packed).
    match decode_varint_value_with_end_hex values_hex pos 0 0 vh_len with
    | None -> None
    | Some (header_value, body_pos) ->
      let mode = header_value % 2 in
      let run_length = header_value / 2 in
      if mode = 0 then begin
        // RLE run: one little-endian value of ceil(bit_width / 8) bytes,
        // repeated `run_length` times.
        let body_bytes = (bit_width + 7) / 8 in
        match read_le_uint_bytes values_hex body_pos body_bytes 0 0 with
        | None -> None
        | Some (value, next_pos) ->
          let take = if run_length <= remaining then run_length else remaining in
          let acc' = repeat_append value take acc in
          decode_hybrid_rle_runs values_hex vh_len next_pos bit_width
            (remaining - take) acc' (fuel - 1)
      end else begin
        // Bit-packed run: `run_length` groups of 8 values, total
        // `run_length * 8` values; body length = `run_length * bit_width`
        // bytes.
        let total_values = mul_nat run_length 8 in
        let body_bytes = mul_nat run_length bit_width in
        let body_hex_len = mul_nat body_bytes 2 in
        if body_pos + body_hex_len > vh_len then None
        else begin
          let take = if total_values <= remaining then total_values else remaining in
          // Decode all `total_values` indices (or `remaining` of them, if
          // we'd otherwise overshoot — Parquet sometimes pads the last
          // bit-packed run, and the spec says to stop at value_count).
          match decode_bit_packed_indices values_hex body_pos bit_width
                  take 0 acc with
          | None -> None
          | Some acc' ->
            decode_hybrid_rle_runs values_hex vh_len (body_pos + body_hex_len)
              bit_width (remaining - take) acc' (fuel - 1)
        end
      end

// Decode an RLE_DICTIONARY data-page payload. The first byte is the bit
// width of indices; the remaining bytes are a hybrid RLE / bit-packed
// stream that produces `value_count` indices.
let decode_rle_dictionary_data_page (payload_hex:string) (value_count:nat)
  : option (list nat) =
  if String.length payload_hex < 2 then None
  else
    match byte_at_hex payload_hex 0 with
    | None -> None
    | Some bit_width ->
      // Fuel: each run consumes at least one index (mode=0 with run_length=0
      // is impossible — run_length=0 means "no indices", which would loop
      // forever; we additionally cap fuel by `value_count + payload_hex /
      // 4` to ensure total decreasing measure).
      let fuel = value_count + (String.length payload_hex / 2) + 1 in
      decode_hybrid_rle_runs payload_hex (String.length payload_hex)
        2 bit_width value_count [] fuel

// ---------------------------------------------------------------------------
// Index-to-value lookup against the dictionary list. Returns None on
// out-of-range indices (defensive — pycottas-emitted Parquet should never
// produce them, but verification is "no holes").
// ---------------------------------------------------------------------------

let rec list_nth_string (xs:list string) (idx:nat) : Tot (option string) (decreases xs) =
  match xs with
  | [] -> None
  | hd :: tl -> if idx = 0 then Some hd else list_nth_string tl (idx - 1)

// Build a flat array-like cache of the dictionary entries for O(N) cons.
// We expose a list-of-options because callers consume it as a row order
// stream identical in shape to `dlba_page_decode_all_strings`.
let rec map_indices_to_dict (indices:list nat) (dict:list string) (acc:list (option string))
  : Tot (list (option string)) (decreases indices) =
  match indices with
  | [] -> List.Tot.rev acc
  | i :: rest ->
    let v = match list_nth_string dict i with
            | Some s -> Some s
            | None -> None in
    map_indices_to_dict rest dict (v :: acc)

// Top-level: decode every row of an RLE_DICTIONARY column. Returns the
// list-of-option-string in row order (one entry per page row), or None if
// either page is missing / mis-encoded.
let probe_parquet_column_rle_dictionary_decode_all (path:string) (col_index:nat)
  : option (list (option string)) =
  match probe_parquet_column_dictionary_page_offset path col_index with
  | None -> None
  | Some dict_offset ->
    match parquet_decompressed_page_at path dict_offset with
    | None -> None
    | Some dict_payload_hex ->
      match parquet_dictionary_page_num_values_at path dict_offset with
      | None -> None
      | Some dict_num_values ->
        match decode_plain_dictionary dict_payload_hex dict_num_values with
        | None -> None
        | Some dict ->
          // Now read the data page (already at column.data_page_offset).
          match probe_parquet_column_decompressed_payload_hex path col_index with
          | None -> None
          | Some data_payload_hex ->
            match probe_parquet_column_page_header_num_values path col_index with
            | None -> None
            | Some value_count ->
              match decode_rle_dictionary_data_page data_payload_hex value_count with
              | None -> None
              | Some indices -> Some (map_indices_to_dict indices dict [])

// Combined dispatcher: try DELTA_LENGTH_BYTE_ARRAY first (covers cols 0+2
// in a COTTAS), fall back to RLE_DICTIONARY (covers cols 1+3). Callers
// (Parser.BallyhooCOTTAS) can swap to this single entry point and stop
// caring about per-column encoding.
let probe_parquet_column_decode_all (path:string) (col_index:nat)
  : option (list (option string)) =
  match probe_parquet_column_delta_length_byte_array_decode_all path col_index with
  | Some result -> Some result
  | None ->
    probe_parquet_column_rle_dictionary_decode_all path col_index

// ===========================================================================
// Issue #98 Gap B — multi-row-group iteration.
//
// All `probe_parquet_column_*` helpers above hard-code row-group 0
// (the first element of footer.row_groups[]). For a multi-row-group
// parquet file (e.g. UK Parliament COTTAS, ~25 row groups, ~3.14M rows)
// they only see the first ~125k rows.
//
// The fix is strictly additive: a parallel family of `_in_row_group`
// helpers takes an `rg_index:nat`, and a top-level
// `_decode_all_row_groups` walks every row group and concatenates.
//
// The existing single-row-group entry points are preserved so that any
// caller still hard-coding row-group-0 stays correct.
// ===========================================================================

// Locate the start (in metadata hex) of column_chunk[col_index] inside
// row_group[rg_index]. Returns the in-meta hex offset of the column-chunk
// struct's first field. Bundles the meta_hex + length so that follow-on
// per-row-group helpers can reuse it without re-reading the footer.
type meta_column_chunk_locator = {
  mcc_meta_hex : string;
  mcc_meta_hex_len : nat;
  mcc_column_chunk_start : nat;
}

let probe_parquet_column_chunk_in_row_group_locator
  (path:string) (rg_index:nat) (col_index:nat)
  : option meta_column_chunk_locator =
  match probe_parquet_footer path with
  | None -> None
  | Some footer ->
    match parquet_read_tail_hex path footer.pf_footer_len with
    | None -> None
    | Some footer_hex ->
      let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
      if meta_hex_len <= String.length footer_hex then
        let meta_hex = String.sub footer_hex 0 meta_hex_len in
        match nth_field_hex meta_hex 4 0 0 meta_hex_len with
        | None -> None
        | Some row_groups_field ->
          if row_groups_field.cf_type <> compact_t_list then None
          else
            match decode_compact_list_info_hex meta_hex
                    row_groups_field.cf_value_start meta_hex_len with
            | None -> None
            | Some row_groups_info ->
              if rg_index >= row_groups_info.cli_count
                 || row_groups_info.cli_etype <> compact_t_struct then None
              else
                match nth_compact_list_element_start_hex meta_hex
                        row_groups_field.cf_value_start rg_index meta_hex_len with
                | None -> None
                | Some rg_start ->
                  match nth_field_hex meta_hex 1 rg_start 0 meta_hex_len with
                  | None -> None
                  | Some columns_field ->
                    if columns_field.cf_type <> compact_t_list then None
                    else
                      match nth_compact_list_element_start_hex meta_hex
                              columns_field.cf_value_start col_index meta_hex_len with
                      | None -> None
                      | Some column_chunk_start ->
                        Some {
                          mcc_meta_hex = meta_hex;
                          mcc_meta_hex_len = meta_hex_len;
                          mcc_column_chunk_start = column_chunk_start;
                        }
      else None

// Helper: drill from column_chunk_start to column_metadata struct start.
let column_metadata_start_of (loc:meta_column_chunk_locator) : option nat =
  match nth_field_hex loc.mcc_meta_hex 3
          loc.mcc_column_chunk_start 0 loc.mcc_meta_hex_len with
  | None -> None
  | Some metadata_field ->
    if metadata_field.cf_type <> compact_t_struct then None
    else Some metadata_field.cf_value_start

// data_page_offset for one (rg_index, col_index). Field 9.
let probe_parquet_column_data_page_offset_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_chunk_in_row_group_locator path rg_index col_index with
  | None -> None
  | Some loc ->
    match column_metadata_start_of loc with
    | None -> None
    | Some md_start ->
      match nth_field_hex loc.mcc_meta_hex 9 md_start 0 loc.mcc_meta_hex_len with
      | None -> None
      | Some offset_field ->
        if offset_field.cf_type <> compact_t_i64 then None
        else
          match decode_varint_value_hex loc.mcc_meta_hex
                  offset_field.cf_value_start 0 0 loc.mcc_meta_hex_len with
          | None -> None
          | Some raw -> Some (zigzag_decode_nat raw)

// dictionary_page_offset for one (rg_index, col_index). Field 14.
let probe_parquet_column_dictionary_page_offset_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_chunk_in_row_group_locator path rg_index col_index with
  | None -> None
  | Some loc ->
    match column_metadata_start_of loc with
    | None -> None
    | Some md_start ->
      match nth_field_hex loc.mcc_meta_hex 14 md_start 0 loc.mcc_meta_hex_len with
      | None -> None
      | Some offset_field ->
        if offset_field.cf_type <> compact_t_i64 then None
        else
          match decode_varint_value_hex loc.mcc_meta_hex
                  offset_field.cf_value_start 0 0 loc.mcc_meta_hex_len with
          | None -> None
          | Some raw -> Some (zigzag_decode_nat raw)

// Page-header probes for a per-row-group data page. The page-header probes
// `parquet_page_header_*_at` already take an explicit page offset, so all we
// need is the per-row-group `data_page_offset`.
let probe_parquet_column_page_header_compressed_size_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset_in_row_group path rg_index col_index with
  | None -> None
  | Some page_offset -> parquet_page_header_compressed_size_at path page_offset

let probe_parquet_column_page_header_uncompressed_size_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset_in_row_group path rg_index col_index with
  | None -> None
  | Some page_offset -> parquet_page_header_uncompressed_size_at path page_offset

let probe_parquet_column_page_header_length_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset_in_row_group path rg_index col_index with
  | None -> None
  | Some page_offset -> parquet_page_header_length_at path page_offset

// data_page header.data_page_header.num_values (field 5 -> field 1, i32).
let probe_parquet_column_page_header_num_values_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_data_page_offset_in_row_group path rg_index col_index with
  | None -> None
  | Some page_offset ->
    match parquet_read_range_hex path page_offset 128 with
    | None -> None
    | Some page_hex ->
      match nth_field_hex page_hex 5 0 0 (String.length page_hex) with
      | None -> None
      | Some data_page_header_field ->
        if data_page_header_field.cf_type <> compact_t_struct then None
        else
          match nth_field_hex page_hex 1 data_page_header_field.cf_value_start 0
                  (String.length page_hex) with
          | None -> None
          | Some num_values_field ->
            if num_values_field.cf_type <> compact_t_i32 then None
            else
              match decode_varint_value_hex page_hex
                      num_values_field.cf_value_start 0 0 (String.length page_hex) with
              | None -> None
              | Some raw -> Some (zigzag_decode_nat raw)

// Decompress the data page payload for one (rg_index, col_index). Mirrors
// `probe_parquet_column_decompressed_payload_hex` but per-row-group.
let probe_parquet_column_decompressed_payload_hex_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option string =
  match probe_parquet_column_data_page_offset_in_row_group path rg_index col_index,
        probe_parquet_column_page_header_length_in_row_group path rg_index col_index,
        probe_parquet_column_page_header_compressed_size_in_row_group path rg_index col_index,
        probe_parquet_column_page_header_uncompressed_size_in_row_group path rg_index col_index with
  | Some page_offset, Some header_len, Some compressed_size, Some uncompressed_size ->
    let payload_offset = page_offset + header_len in
    (match parquet_read_range_hex path payload_offset compressed_size with
     | None -> None
     | Some compressed_hex ->
       parquet_zstd_decompress_hex compressed_hex uncompressed_size)
  | _ -> None

// First-level section length (LE u32 at offset 0 of the decompressed page).
let probe_parquet_column_first_level_section_length_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_decompressed_payload_hex_in_row_group path rg_index col_index with
  | None -> None
  | Some payload_hex ->
    if String.length payload_hex < 8 then None
    else le_u32_at_hex payload_hex 0

// DLBA value-stream byte offset (relative to start of decompressed page).
let probe_parquet_column_delta_length_byte_array_values_offset_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option nat =
  match probe_parquet_column_first_level_section_length_in_row_group path rg_index col_index with
  | None -> None
  | Some section_len -> Some (4 + section_len)

// One-shot DELTA_LENGTH_BYTE_ARRAY page cache builder for one row group.
// Mirrors `probe_parquet_column_delta_length_byte_array_page_cache` but
// composed off the `_in_row_group` payload accessors.
let probe_parquet_column_delta_length_byte_array_page_cache_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option dlba_page_cache =
  match probe_parquet_column_decompressed_payload_hex_in_row_group path rg_index col_index,
        probe_parquet_column_delta_length_byte_array_values_offset_in_row_group
          path rg_index col_index with
  | Some payload_hex, Some values_offset ->
    let payload_len_hex = String.length payload_hex in
    let values_start_hex = mul_nat values_offset 2 in
    if values_start_hex > payload_len_hex then None
    else
      let values_hex = String.sub payload_hex values_start_hex
                         (payload_len_hex - values_start_hex) in
      let vh_len = String.length values_hex in
      (match decode_varint_value_with_end_hex values_hex 0 0 0 vh_len with
       | None -> None
       | Some (block_size, p1) ->
         match decode_varint_value_with_end_hex values_hex p1 0 0 vh_len with
         | None -> None
         | Some (miniblocks, p2) ->
           if miniblocks = 0 then None
           else
           match decode_varint_value_with_end_hex values_hex p2 0 0 vh_len with
           | None -> None
           | Some (value_count, p3) ->
             match decode_varint_value_with_end_hex values_hex p3 0 0 vh_len with
             | None -> None
             | Some (first_raw, p4) ->
               let first_length = zigzag_decode_nat first_raw in
               match decode_varint_value_with_end_hex values_hex p4 0 0 vh_len with
               | None -> None
               | Some (min_delta_raw, p5) ->
                 let min_delta = zigzag_decode_int min_delta_raw in
                 if p5 + 1 >= vh_len then None
                 else
                   match byte_at_hex values_hex p5 with
                   | None -> None
                   | Some bit_width ->
                     let widths_offset = p5 in
                     let packed_start = p5 + mul_nat miniblocks 2 in
                     let values_per_miniblock : nat =
                       if miniblocks > 0 then div_nat_pos block_size miniblocks
                       else 0 in
                     match build_dlba_length_list values_hex vh_len
                             block_size miniblocks values_per_miniblock
                             min_delta widths_offset packed_start bit_width
                             0 0 value_count first_length [] with
                     | None -> None
                     | Some lengths ->
                       let total_value_bytes = sum_nat_list lengths in
                       let payload_byte_len = payload_len_hex / 2 in
                       if values_offset > payload_byte_len then None
                       else
                         let values_stream_len =
                           payload_byte_len - values_offset in
                         if total_value_bytes > values_stream_len then None
                         else
                           let value_data_offset =
                             values_stream_len - total_value_bytes in
                           let starts = prefix_sums lengths 0 [] in
                           Some {
                             dpc_payload_hex = payload_hex;
                             dpc_values_offset = values_offset;
                             dpc_value_count = value_count;
                             dpc_first_length = first_length;
                             dpc_min_delta = min_delta;
                             dpc_bit_width = bit_width;
                             dpc_packed_start = packed_start;
                             dpc_value_data_offset = value_data_offset;
                             dpc_lengths = lengths;
                             dpc_value_starts = starts;
                           })
  | _ -> None

let probe_parquet_column_delta_length_byte_array_decode_all_in_row_group
  (path:string) (rg_index:nat) (col_index:nat)
  : option (list (option string)) =
  match probe_parquet_column_delta_length_byte_array_page_cache_in_row_group
          path rg_index col_index with
  | None -> None
  | Some cache -> Some (dlba_page_decode_all_strings cache)

// RLE_DICTIONARY decoder for one row group. Composes per-row-group dictionary
// page + data page. `parquet_decompressed_page_at` and
// `parquet_dictionary_page_num_values_at` already work off arbitrary page
// offsets, so they don't need a per-row-group sibling.
let probe_parquet_column_rle_dictionary_decode_all_in_row_group
  (path:string) (rg_index:nat) (col_index:nat)
  : option (list (option string)) =
  match probe_parquet_column_dictionary_page_offset_in_row_group
          path rg_index col_index with
  | None -> None
  | Some dict_offset ->
    match parquet_decompressed_page_at path dict_offset with
    | None -> None
    | Some dict_payload_hex ->
      match parquet_dictionary_page_num_values_at path dict_offset with
      | None -> None
      | Some dict_num_values ->
        match decode_plain_dictionary dict_payload_hex dict_num_values with
        | None -> None
        | Some dict ->
          match probe_parquet_column_decompressed_payload_hex_in_row_group
                  path rg_index col_index with
          | None -> None
          | Some data_payload_hex ->
            match probe_parquet_column_page_header_num_values_in_row_group
                    path rg_index col_index with
            | None -> None
            | Some value_count ->
              match decode_rle_dictionary_data_page data_payload_hex value_count with
              | None -> None
              | Some indices -> Some (map_indices_to_dict indices dict [])

// Per-row-group dispatcher: try DLBA first, fall back to RLE_DICTIONARY.
// Bet4 (lazy mmap'd backend) calls this one row group at a time.
let probe_parquet_column_decode_in_row_group
  (path:string) (rg_index:nat) (col_index:nat)
  : option (list (option string)) =
  match probe_parquet_column_delta_length_byte_array_decode_all_in_row_group
          path rg_index col_index with
  | Some result -> Some result
  | None ->
    probe_parquet_column_rle_dictionary_decode_all_in_row_group
      path rg_index col_index

// Concatenate two lists, tail-recursive via reverse-then-flip. Avoids
// `List.Tot.append`'s O(n) per-cons stack growth on the parliament-sized
// (~3.14M element) lists.
let rec list_rev_append (xs:list 'a) (acc:list 'a)
  : Tot (list 'a) (decreases xs) =
  match xs with
  | [] -> acc
  | hd :: tl -> list_rev_append tl (hd :: acc)

let list_rev (xs:list 'a) : Tot (list 'a) =
  list_rev_append xs []

// Walk row groups [rg_index .. rg_count) and accumulate each row group's
// decoded column into `acc_rev` in REVERSE row order. Caller flips at the end.
//
// We carry an explicit fuel parameter equal to `rg_count` so the F* totality
// checker accepts the recursion (decreases on fuel).
let rec collect_row_group_columns
  (path:string) (col_index:nat)
  (rg_index:nat) (rg_count:nat) (fuel:nat) (acc_rev:list (option string))
  : Tot (option (list (option string))) (decreases fuel) =
  if fuel = 0 then Some acc_rev
  else if rg_index >= rg_count then Some acc_rev
  else
    match probe_parquet_column_decode_in_row_group path rg_index col_index with
    | None -> None
    | Some this_rg ->
      // this_rg is in row order; prepend reversed onto acc_rev.
      let acc_rev' = list_rev_append this_rg acc_rev in
      collect_row_group_columns path col_index (rg_index + 1) rg_count
        (fuel - 1) acc_rev'

// Walk every row group in order and return the concatenation of column
// decodes. Eager — for the ~3M-row parliament COTTAS this is the path the
// existing in-memory loader uses.
let probe_parquet_column_decode_all_row_groups
  (path:string) (col_index:nat)
  : option (list (option string)) =
  match probe_parquet_row_group_count path with
  | None -> None
  | Some rg_count ->
    match collect_row_group_columns path col_index 0 rg_count rg_count [] with
    | None -> None
    | Some acc_rev -> Some (list_rev acc_rev)

// ---------------------------------------------------------------------------
// Tsade2 (issue #100 Phase D): per-row-group dictionary decode (data-page
// SKIPPED).
//
// For column-prune query planning we need each row group's predicate (or
// subject / object) DICTIONARY only, not its data page. The dictionary is
// a small set of distinct strings — typically <1KB compressed; decompress
// + plain-decode is fast (microseconds per rg).
//
// Reuses existing primitives:
//   - probe_parquet_column_dictionary_page_offset_in_row_group
//   - parquet_decompressed_page_at
//   - parquet_dictionary_page_num_values_at
//   - decode_plain_dictionary
//
// Returns None if the column doesn't have a dictionary page (e.g.
// the column was encoded as DELTA_LENGTH_BYTE_ARRAY without a dict).
// In that case, the column-prune planner falls back to a full walk of
// that row group.
// ---------------------------------------------------------------------------

let probe_parquet_column_dictionary_in_row_group
  (path:string) (rg_index:nat) (col_index:nat) : option (list string) =
  match probe_parquet_column_dictionary_page_offset_in_row_group
          path rg_index col_index with
  | None -> None
  | Some dict_offset ->
    match parquet_decompressed_page_at path dict_offset with
    | None -> None
    | Some dict_payload_hex ->
      match parquet_dictionary_page_num_values_at path dict_offset with
      | None -> None
      | Some dict_num_values ->
        decode_plain_dictionary dict_payload_hex dict_num_values
