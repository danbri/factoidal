open Prims
let dict_magic : Prims.nat= (Prims.parse_int "0x444b4f43")
let dict_version : Prims.nat= Prims.int_one
let header_size : Prims.nat= (Prims.of_int (32))
let id_size : Prims.nat= (Prims.of_int (4))
let offset_size : Prims.nat= (Prims.of_int (8))
let rec build_ids_acc (i : Prims.nat) (n : Prims.nat) : RDF_Bytes.bytes=
  if i = n
  then []
  else
    RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le i)
      (build_ids_acc (i + Prims.int_one) n)
let build_ids (n : Prims.nat) : RDF_Bytes.bytes=
  build_ids_acc Prims.int_zero n
let rec build_offs_acc (cur : Prims.nat) (tokens : Prims.string Prims.list) :
  (Prims.nat, RDF_Bytes.bytes) Prims.dtuple2=
  match tokens with
  | [] -> Prims.Mkdtuple2 (cur, [])
  | t::rest ->
      if cur >= (Prims.parse_int "18446744073709551616")
      then Prims.Mkdtuple2 (cur, [])
      else
        (let cur' = cur + (FStar_String.strlen t) in
         let uu___1 = build_offs_acc cur' rest in
         match uu___1 with
         | Prims.Mkdtuple2 (cur'', rest_bytes) ->
             let head = RDF_Bytes.write_u64_le cur in
             Prims.Mkdtuple2
               (cur'', (RDF_List_Helpers.append_tr head rest_bytes)))
let build_offs (token_data_offset : Prims.nat)
  (tokens : Prims.string Prims.list) : RDF_Bytes.bytes=
  if token_data_offset >= (Prims.parse_int "18446744073709551616")
  then []
  else
    (let uu___1 = build_offs_acc token_data_offset tokens in
     match uu___1 with
     | Prims.Mkdtuple2 (final, body) ->
         if final >= (Prims.parse_int "18446744073709551616")
         then body
         else RDF_List_Helpers.append_tr body (RDF_Bytes.write_u64_le final))
let rec build_data (tokens : Prims.string Prims.list) : RDF_Bytes.bytes=
  match tokens with
  | [] -> []
  | t::rest ->
      RDF_List_Helpers.append_tr (RDF_Bytes.bytes_of_string t)
        (build_data rest)
let build_header (n : Prims.nat) (ids_offset : Prims.nat)
  (tokens_offset : Prims.nat) : RDF_Bytes.bytes=
  RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le dict_magic)
    (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le dict_version)
       (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le n)
          (RDF_List_Helpers.append_tr (RDF_Bytes.write_u32_le Prims.int_zero)
             (RDF_List_Helpers.append_tr (RDF_Bytes.write_u64_le ids_offset)
                (RDF_Bytes.write_u64_le tokens_offset)))))
let serialize_dict (sorted_tokens : Prims.string Prims.list) :
  RDF_Bytes.bytes=
  let n = FStar_List_Tot_Base.length sorted_tokens in
  if n >= (Prims.parse_int "4294967296")
  then []
  else
    (let ids_offset = header_size in
     let tokens_offset = ids_offset + (id_size * n) in
     let data_offset = tokens_offset + (offset_size * (n + Prims.int_one)) in
     if data_offset >= (Prims.parse_int "18446744073709551616")
     then []
     else
       (let header = build_header n ids_offset tokens_offset in
        let ids = build_ids n in
        let offs = build_offs data_offset sorted_tokens in
        let data = build_data sorted_tokens in
        RDF_List_Helpers.append_tr header
          (RDF_List_Helpers.append_tr ids
             (RDF_List_Helpers.append_tr offs data))))
