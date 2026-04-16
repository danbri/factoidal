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
        let field_id_opt =
          if delta = 0 then
            match decode_varint_hex (pos + 2) 0 0 (fuel - 1) with
            | None -> None
            | Some (fid, _) -> Some fid
          else Some (prev_id + delta)
        in
        let value_pos_opt =
          if delta = 0 then
            match decode_varint_hex (pos + 2) 0 0 (fuel - 1) with
            | None -> None
            | Some (_, p) -> Some p
          else Some (pos + 2)
        in
        (match field_id_opt, value_pos_opt with
         | Some field_id, Some value_pos ->
           (match skip_compact_value_hex hex ftype value_pos (fuel - 1) with
            | None -> None
            | Some next ->
              if field_id = target_id then
                Some { cf_id = field_id; cf_type = ftype; cf_value_start = value_pos; cf_next = next }
              else
                nth_field_hex hex target_id next field_id (fuel - 1))
         | _ -> None)

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
