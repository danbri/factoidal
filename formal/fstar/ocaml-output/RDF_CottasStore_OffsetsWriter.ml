open Prims
let coto_magic : Prims.nat= (Prims.parse_int "0x4f544f43")
let coto_version : Prims.nat= Prims.int_one
let header_size : Prims.nat= (Prims.of_int (16))
let build_header (num_rgs : Prims.nat) (num_preds : Prims.nat) :
  RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le coto_magic)
    (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le coto_version)
       (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le num_rgs)
          (RDF_Bytes.write_u32_le num_preds)))
let serialize_offsets_header (num_rgs : Prims.nat) (num_preds : Prims.nat) :
  RDF_Bytes.bytes=
  if num_rgs >= (Prims.parse_int "4294967296")
  then []
  else
    if num_preds >= (Prims.parse_int "4294967296")
    then []
    else build_header num_rgs num_preds
let rec serialize_u32_list (xs : Prims.nat Prims.list) : RDF_Bytes.bytes=
  match xs with
  | [] -> []
  | x::rest ->
      if x >= (Prims.parse_int "4294967296")
      then []
      else
        RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le x)
          (serialize_u32_list rest)
let rec parse_n_u32s (k : Prims.nat) (bs : RDF_Bytes.bytes) :
  (Prims.nat Prims.list * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  if k = Prims.int_zero
  then FStar_Pervasives_Native.Some ([], bs)
  else
    (match RDF_Bytes.parse_u32_le bs with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (v, rest) ->
         (match parse_n_u32s (k - Prims.int_one) rest with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (xs, after) ->
              FStar_Pervasives_Native.Some ((v :: xs), after)))
let rec serialize_u64_list (xs : Prims.nat Prims.list) : RDF_Bytes.bytes=
  match xs with
  | [] -> []
  | x::rest ->
      if x >= (Prims.parse_int "18446744073709551616")
      then []
      else
        RDF_List_Helpers.append_tr (RDF_Bytes.write_u64_le x)
          (serialize_u64_list rest)
let rec parse_n_u64s (k : Prims.nat) (bs : RDF_Bytes.bytes) :
  (Prims.nat Prims.list * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  if k = Prims.int_zero
  then FStar_Pervasives_Native.Some ([], bs)
  else
    (match RDF_Bytes.parse_u64_le bs with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (v, rest) ->
         (match parse_n_u64s (k - Prims.int_one) rest with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (xs, after) ->
              FStar_Pervasives_Native.Some ((v :: xs), after)))
let rec last_of_or (xs : Prims.nat Prims.list) (default_ : Prims.nat) :
  Prims.nat=
  match xs with
  | [] -> default_
  | x::[] -> x
  | uu___::t -> last_of_or t default_
let serialize_offsets (num_rgs : Prims.nat) (num_preds : Prims.nat)
  (rg_offsets : Prims.nat Prims.list) (subject_ids : Prims.nat Prims.list) :
  RDF_Bytes.bytes=
  if num_rgs >= (Prims.parse_int "4294967296")
  then []
  else
    if num_preds >= (Prims.parse_int "4294967296")
    then []
    else
      (let header = build_header num_rgs num_preds in
       let off_b = serialize_u64_list rg_offsets in
       let subj_b = serialize_u32_list subject_ids in
       RDF_List_Helpers.append_tr header
         (RDF_List_Helpers.append_tr off_b subj_b))
let parse_offsets (bs : RDF_Bytes.bytes) :
  (Prims.nat * Prims.nat * Prims.nat Prims.list * Prims.nat Prims.list)
    FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (m, after_magic) ->
      if Prims.op_Negation (m = coto_magic)
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (v, after_version) ->
             if Prims.op_Negation (v = coto_version)
             then FStar_Pervasives_Native.None
             else
               (match RDF_Bytes.parse_u32_le after_version with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (num_rgs, after_rgs) ->
                    (match RDF_Bytes.parse_u32_le after_rgs with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (num_preds, after_header)
                         ->
                         let n_offsets =
                           (num_rgs * num_preds) + Prims.int_one in
                         (match parse_n_u64s n_offsets after_header with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some
                              (rg_offsets, after_offsets) ->
                              let total_subjs =
                                last_of_or rg_offsets Prims.int_zero in
                              (match parse_n_u32s total_subjs after_offsets
                               with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some
                                   (subject_ids, _trailing) ->
                                   FStar_Pervasives_Native.Some
                                     (num_rgs, num_preds, rg_offsets,
                                       subject_ids))))))
