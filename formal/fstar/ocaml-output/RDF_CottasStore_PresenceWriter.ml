open Prims
let presence_magic : Prims.nat= (Prims.parse_int "0x50544f43")
let presence_version : Prims.nat= Prims.int_one
let header_size : Prims.nat= (Prims.of_int (16))
let build_header (num_rgs : Prims.nat) (num_tokens : Prims.nat) :
  RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le presence_magic)
    (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le presence_version)
       (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le num_rgs)
          (RDF_Bytes.write_u32_le num_tokens)))
let serialize_presence_header (num_rgs : Prims.nat) (num_tokens : Prims.nat)
  : RDF_Bytes.bytes=
  if num_rgs >= (Prims.parse_int "4294967296")
  then []
  else
    if num_tokens >= (Prims.parse_int "4294967296")
    then []
    else build_header num_rgs num_tokens
let serialize_presence (num_rgs : Prims.nat) (num_tokens : Prims.nat)
  (bitmap : RDF_Bytes.bytes) : RDF_Bytes.bytes=
  if num_rgs >= (Prims.parse_int "4294967296")
  then []
  else
    if num_tokens >= (Prims.parse_int "4294967296")
    then []
    else
      (let header = build_header num_rgs num_tokens in
       RDF_List_Helpers.append_tr header bitmap)
let parse_presence (bs : RDF_Bytes.bytes) :
  (Prims.nat * Prims.nat * RDF_Bytes.bytes) FStar_Pervasives_Native.option=
  match RDF_Bytes.parse_u32_le bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (m, after_magic) ->
      if Prims.op_Negation (m = presence_magic)
      then FStar_Pervasives_Native.None
      else
        (match RDF_Bytes.parse_u32_le after_magic with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (v, after_version) ->
             if Prims.op_Negation (v = presence_version)
             then FStar_Pervasives_Native.None
             else
               (match RDF_Bytes.parse_u32_le after_version with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (num_rgs, after_rgs) ->
                    (match RDF_Bytes.parse_u32_le after_rgs with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some
                         (num_tokens, after_header) ->
                         let bits = num_rgs * num_tokens in
                         let needed =
                           (bits + (Prims.of_int (7))) / (Prims.of_int (8)) in
                         (match RDF_Bytes.parse_n_bytes needed after_header
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (bitmap, _trailing)
                              ->
                              FStar_Pervasives_Native.Some
                                (num_rgs, num_tokens, bitmap)))))
