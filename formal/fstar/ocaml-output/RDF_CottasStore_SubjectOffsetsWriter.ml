open Prims
let cots_magic : Prims.nat= (Prims.parse_int "0x53544f43")
let cots_version : Prims.nat= Prims.int_one
let header_size : Prims.nat= (Prims.of_int (16))
let build_header (num_subjects : Prims.nat) (num_rows_total : Prims.nat) :
  RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le cots_magic)
    (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le cots_version)
       (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le num_subjects)
          (RDF_Bytes.write_u32_le num_rows_total)))
let serialize_subject_offsets_header (num_subjects : Prims.nat)
  (num_rows_total : Prims.nat) : RDF_Bytes.bytes=
  if num_subjects >= (Prims.parse_int "4294967296")
  then []
  else
    if num_rows_total >= (Prims.parse_int "4294967296")
    then []
    else build_header num_subjects num_rows_total
let rec flatten_ranges (rs : (Prims.nat * Prims.nat) Prims.list) :
  Prims.nat Prims.list=
  match rs with | [] -> [] | (s, e)::tl -> s :: e :: (flatten_ranges tl)
let rec unflatten_ranges (xs : Prims.nat Prims.list) :
  (Prims.nat * Prims.nat) Prims.list FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.Some []
  | s::e::tl ->
      (match unflatten_ranges tl with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some rest ->
           FStar_Pervasives_Native.Some ((s, e) :: rest))
  | uu___::[] -> FStar_Pervasives_Native.None
let rec ranges_all_lt (rs : (Prims.nat * Prims.nat) Prims.list)
  (bound : Prims.nat) : Prims.bool=
  match rs with
  | [] -> true
  | (s, e)::tl -> ((s < bound) && (e < bound)) && (ranges_all_lt tl bound)
let serialize_subject_offsets (num_subjects : Prims.nat)
  (num_rows_total : Prims.nat) (ranges : (Prims.nat * Prims.nat) Prims.list)
  : RDF_Bytes.bytes=
  if num_subjects >= (Prims.parse_int "4294967296")
  then []
  else
    if num_rows_total >= (Prims.parse_int "4294967296")
    then []
    else
      (let header = build_header num_subjects num_rows_total in
       let flat = flatten_ranges ranges in
       RDF_List_Helpers.append_tr header
         (RDF_CottasStore_OffsetsWriter.serialize_u64_list flat))
let parse_subject_offsets (bs : RDF_Bytes.bytes) :
  (Prims.nat * Prims.nat * (Prims.nat * Prims.nat) Prims.list)
    FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (m, after_magic) ->
      if Prims.op_Negation (m = cots_magic)
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (v, after_version) ->
             if Prims.op_Negation (v = cots_version)
             then FStar_Pervasives_Native.None
             else
               (match RDF_Bytes.parse_u32_le after_version with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (num_subjects, after_ns) ->
                    (match RDF_Bytes.parse_u32_le after_ns with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some
                         (num_rows_total, after_header) ->
                         let n_flat = (Prims.of_int (2)) * num_subjects in
                         (match RDF_CottasStore_OffsetsWriter.parse_n_u64s
                                  n_flat after_header
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (flat, _trailing) ->
                              (match unflatten_ranges flat with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some ranges ->
                                   FStar_Pervasives_Native.Some
                                     (num_subjects, num_rows_total, ranges))))))
