open Parquet_Footer

let () =
  if Array.length Sys.argv <> 2 then begin
    Printf.eprintf "usage: parquet_probe FILE\n";
    exit 1
  end;
  match probe_parquet_footer Sys.argv.(1) with
  | FStar_Pervasives_Native.None ->
      Printf.printf "not-parquet\n"
  | FStar_Pervasives_Native.Some footer ->
      Printf.printf "magic=%s\n" footer.pf_magic;
      Printf.printf "metadata_len=%s\n" (Z.to_string footer.pf_metadata_len);
      Printf.printf "footer_len=%s\n" (Z.to_string footer.pf_footer_len);
      (match probe_parquet_num_rows Sys.argv.(1) with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some n ->
           Printf.printf "num_rows=%s\n" (Z.to_string n));
      (match probe_parquet_row_group_count Sys.argv.(1) with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some n ->
           Printf.printf "row_groups=%s\n" (Z.to_string n));
      (match probe_parquet_first_row_group_num_rows Sys.argv.(1) with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some n ->
           Printf.printf "row_group0_num_rows=%s\n" (Z.to_string n));
      (match probe_parquet_first_row_group_column_count Sys.argv.(1) with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some n ->
           Printf.printf "row_group0_columns=%s\n" (Z.to_string n));
      (match probe_parquet_first_column_name Sys.argv.(1) with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some s ->
           Printf.printf "row_group0_col0_name=%s\n" s);
      (match probe_parquet_first_column_data_page_offset Sys.argv.(1) with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some n ->
           Printf.printf "row_group0_col0_data_page_offset=%s\n" (Z.to_string n));
      List.iter (fun idx ->
        match probe_parquet_column_name Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_name=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_data_page_offset Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_data_page_offset=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_compression_codec Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_compression=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_num_values Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_num_values=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_total_compressed_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_total_compressed_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_total_uncompressed_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_total_uncompressed_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_type Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_page_header_type=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_uncompressed_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_page_header_uncompressed_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_compressed_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_page_header_compressed_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_num_values Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_page_header_num_values=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_length Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_page_header_length=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_payload_offset Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_page_payload_offset=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_data_encoding Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_page_data_encoding=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_definition_level_encoding Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_page_definition_level_encoding=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_header_repetition_level_encoding Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_page_repetition_level_encoding=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_page_payload_magic_hex Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_page_payload_magic=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_frame_header_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_zstd_frame_header_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_first_block_type Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_zstd_first_block_type=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_first_block_last_flag Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_zstd_first_block_last_flag=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_first_block_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_zstd_first_block_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_first_block_header_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_zstd_first_block_header_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_first_block_payload_offset Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_zstd_first_block_payload_offset=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_frame_accounted_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_zstd_frame_accounted_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_zstd_frame_size_matches_page Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_zstd_frame_size_matches_page=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_decompressed_payload_hex_length Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_decompressed_payload_len=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_decompressed_payload_prefix_hex Sys.argv.(1) (Z.of_int idx) (Z.of_int 32) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_decompressed_payload_prefix=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_first_level_section_length Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_first_level_section_len=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_values_offset Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_values_offset=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_values_prefix_hex Sys.argv.(1) (Z.of_int idx) (Z.of_int 24) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some s ->
            Printf.printf "row_group0_col%d_dlba_values_prefix=%s\n" idx s
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_block_size Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_block_size=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_miniblock_count Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_miniblocks=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_value_count Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_value_count=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_first_length Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_first_length=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_first_min_delta Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_first_min_delta=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_first_bit_width Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_first_bit_width=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        List.iter (fun value_idx ->
          match probe_parquet_column_delta_length_byte_array_length_at Sys.argv.(1) (Z.of_int idx) (Z.of_int value_idx) with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some n ->
              Printf.printf "row_group0_col%d_dlba_length_%d=%s\n" idx value_idx (Z.to_string n)
        ) [0; 1; 2; 3; 4]
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        match probe_parquet_column_delta_length_byte_array_value_data_offset Sys.argv.(1) (Z.of_int idx) with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some n ->
            Printf.printf "row_group0_col%d_dlba_value_data_offset=%s\n" idx (Z.to_string n)
      ) [0; 1; 2; 3];
      List.iter (fun idx ->
        List.iter (fun value_idx ->
          match probe_parquet_column_delta_length_byte_array_value_string_at Sys.argv.(1) (Z.of_int idx) (Z.of_int value_idx) with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some s ->
              Printf.printf "row_group0_col%d_dlba_value_%d=%s\n" idx value_idx s
        ) [0; 1; 2; 3; 4]
      ) [0; 1; 2; 3];
      (match probe_parquet_metadata_strings Sys.argv.(1) with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some strings ->
           List.iter (fun s -> Printf.printf "meta_string=%s\n" s) strings)
