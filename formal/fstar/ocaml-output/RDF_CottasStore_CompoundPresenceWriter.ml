open Prims
let copo_magic : Prims.nat= (Prims.parse_int "0x4f504f43")
let copo_version : Prims.nat= Prims.int_one
let header_size : Prims.nat= (Prims.of_int (20))
let build_header (num_rgs : Prims.nat) (pred_dict_size : Prims.nat)
  (obj_dict_size : Prims.nat) : RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le copo_magic)
    (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le copo_version)
       (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le num_rgs)
          (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le pred_dict_size)
             (RDF_Bytes.write_u32_le obj_dict_size))))
let serialize_compound_presence_header (num_rgs : Prims.nat)
  (pred_dict_size : Prims.nat) (obj_dict_size : Prims.nat) : RDF_Bytes.bytes=
  if num_rgs >= (Prims.parse_int "4294967296")
  then []
  else
    if pred_dict_size >= (Prims.parse_int "4294967296")
    then []
    else
      if obj_dict_size >= (Prims.parse_int "4294967296")
      then []
      else build_header num_rgs pred_dict_size obj_dict_size
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
let serialize_compound_presence (num_rgs : Prims.nat)
  (pred_dict_size : Prims.nat) (obj_dict_size : Prims.nat)
  (rg_offsets : Prims.nat Prims.list) (pairs : Prims.nat Prims.list) :
  RDF_Bytes.bytes=
  if num_rgs >= (Prims.parse_int "4294967296")
  then []
  else
    if pred_dict_size >= (Prims.parse_int "4294967296")
    then []
    else
      if obj_dict_size >= (Prims.parse_int "4294967296")
      then []
      else
        (let header = build_header num_rgs pred_dict_size obj_dict_size in
         let off_b = serialize_u64_list rg_offsets in
         let pair_b = serialize_u64_list pairs in
         RDF_List_Helpers.append_tr header
           (RDF_List_Helpers.append_tr off_b pair_b))
let parse_compound_presence (bs : RDF_Bytes.bytes) :
  (Prims.nat * Prims.nat * Prims.nat * Prims.nat Prims.list * Prims.nat
    Prims.list) FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (m, after_magic) ->
      if Prims.op_Negation (m = copo_magic)
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (v, after_version) ->
             if Prims.op_Negation (v = copo_version)
             then FStar_Pervasives_Native.None
             else
               (match RDF_Bytes.parse_u32_le after_version with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (num_rgs, after_rgs) ->
                    (match RDF_Bytes.parse_u32_le after_rgs with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (pred_size, after_pred)
                         ->
                         (match RDF_Bytes.parse_u32_le after_pred with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some
                              (obj_size, after_header) ->
                              (match parse_n_u64s (num_rgs + Prims.int_one)
                                       after_header
                               with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some
                                   (rg_offsets, after_offsets) ->
                                   let total_pairs =
                                     last_of_or rg_offsets Prims.int_zero in
                                   (match parse_n_u64s total_pairs
                                            after_offsets
                                    with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.None
                                    | FStar_Pervasives_Native.Some
                                        (pairs, _trailing) ->
                                        FStar_Pervasives_Native.Some
                                          (num_rgs, pred_size, obj_size,
                                            rg_offsets, pairs)))))))
