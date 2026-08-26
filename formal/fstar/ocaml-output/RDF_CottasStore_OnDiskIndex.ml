open Prims

(* vav3: companion mmap implementations installed (issue #100, 2026-04-26).
   Per-path mmap'd Bigarray.Array1.t bytes for each .dict + .presence
   companion file. Held for the lifetime of the process. *)
module Vav3_mmap = struct
  open Stdlib
  (* `open Prims` at the top of this file (via `let cotd_magic_u32 : Prims.nat`)
     shadows `int` with `Prims.int = Z.t`. We need plain machine ints here
     for offsets, so alias them. *)
  type pint = Stdlib.Int.t

  type mmap_view = {
    mv_path : string;
    mv_size : pint;
    mv_data : (Stdlib.Char.t, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t;
    mv_fd   : Unix.file_descr;
  }

  let views : (string, mmap_view) Hashtbl.t = Hashtbl.create 17

  (* Open a path read-only and mmap the whole file. Returns Some size on
     success. None if the file doesn't exist or is empty. *)
  let try_open_mmap (path : string) : pint option =
    match Hashtbl.find_opt views path with
    | Some v -> Some v.mv_size
    | None ->
      try
        let fd = Unix.openfile path [Unix.O_RDONLY] 0 in
        let st = Unix.fstat fd in
        let size = st.Unix.st_size in
        if size = 0 then begin Unix.close fd; None end
        else begin
          (* Bigarray.array1_of_genarray + Unix.map_file mmaps into a
             Bigarray. We then keep the genarray-derived array1 alive in
             the views hashtbl. *)
          let ga = Unix.map_file fd Bigarray.Char Bigarray.c_layout false [|size|] in
          let a1 = Bigarray.array1_of_genarray ga in
          let v : mmap_view = {
            mv_path = path;
            mv_size = size;
            mv_data = a1;
            mv_fd = fd;
          } in
          Hashtbl.replace views path v;
          Some size
        end
      with _ -> None

  let close_mmap (path : string) : unit =
    match Hashtbl.find_opt views path with
    | None -> ()
    | Some v ->
      (try Unix.close v.mv_fd with _ -> ());
      Hashtbl.remove views path

  let view_for (path : string) : mmap_view option =
    match Hashtbl.find_opt views path with
    | Some v -> Some v
    | None ->
      (* Open lazily: F* may call read_companion_* without an explicit open. *)
      match try_open_mmap path with
      | None -> None
      | Some _ -> Hashtbl.find_opt views path

  let read_byte_int (path : string) (offset : pint) : pint option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || offset >= v.mv_size then None
      else Some (Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data offset))

  let read_u32_le_int (path : string) (offset : pint) : pint option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || offset + 4 > v.mv_size then None
      else
        let b0 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data offset) in
        let b1 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 1)) in
        let b2 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 2)) in
        let b3 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 3)) in
        Some (b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24))

  (* Note: u64 read assumes the value fits in OCaml's native int (63-bit
     on 64-bit). Our companion files are <= a few hundred MB so all u64
     fields (token byte offsets) are well below 2^62. We sanity-check
     and return None if the high bit looks set. *)
  let read_u64_le_int (path : string) (offset : pint) : pint option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || offset + 8 > v.mv_size then None
      else
        let b0 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data offset) in
        let b1 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 1)) in
        let b2 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 2)) in
        let b3 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 3)) in
        let b4 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 4)) in
        let b5 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 5)) in
        let b6 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 6)) in
        let b7 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 7)) in
        if b7 >= 0x80 then None  (* would not fit in 63-bit int *)
        else
          let lo = b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
          let hi = b4 lor (b5 lsl 8) lor (b6 lsl 16) lor (b7 lsl 24) in
          Some (lo lor (hi lsl 32))

  let read_string (path : string) (offset : pint) (count : pint) : string option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || count < 0 || offset + count > v.mv_size then None
      else
        let buf = Stdlib.Bytes.create count in
        for i = 0 to count - 1 do
          Stdlib.Bytes.unsafe_set buf i (Bigarray.Array1.unsafe_get v.mv_data (offset + i))
        done;
        Some (Stdlib.Bytes.unsafe_to_string buf)

  let file_size (path : string) : pint option =
    if not (Sys.file_exists path) then None
    else try
      let st = Unix.stat path in
      if st.Unix.st_size <= 0 then None else Some st.Unix.st_size
    with _ -> None
end


let cotd_magic_u32 : Prims.nat= (Prims.parse_int "0x44544f43")
let cotp_magic_u32 : Prims.nat= (Prims.parse_int "0x50544f43")
let layout_version : Prims.nat= Prims.int_one
let mmap_companion_open (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.try_open_mmap path with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)
let read_companion_u32_le (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.read_u32_le_int path (Z.to_int offset) with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)
let read_companion_u64_le (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.read_u64_le_int path (Z.to_int offset) with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)
let read_companion_byte (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.read_byte_int path (Z.to_int offset) with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)
let read_companion_string (path : Prims.string) (offset : Prims.nat)
  (count : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match Vav3_mmap.read_string path (Z.to_int offset) (Z.to_int count) with
  | None -> FStar_Pervasives_Native.None
  | Some s -> FStar_Pervasives_Native.Some s
let companion_file_size (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.file_size path with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)
type dict_header =
  {
  dh_magic: Prims.nat ;
  dh_version: Prims.nat ;
  dh_num_tokens: Prims.nat ;
  dh_ids_offset: Prims.nat ;
  dh_tokens_offset: Prims.nat }
let __proj__Mkdict_header__item__dh_magic (projectee : dict_header) :
  Prims.nat=
  match projectee with
  | { dh_magic; dh_version; dh_num_tokens; dh_ids_offset; dh_tokens_offset;_}
      -> dh_magic
let __proj__Mkdict_header__item__dh_version (projectee : dict_header) :
  Prims.nat=
  match projectee with
  | { dh_magic; dh_version; dh_num_tokens; dh_ids_offset; dh_tokens_offset;_}
      -> dh_version
let __proj__Mkdict_header__item__dh_num_tokens (projectee : dict_header) :
  Prims.nat=
  match projectee with
  | { dh_magic; dh_version; dh_num_tokens; dh_ids_offset; dh_tokens_offset;_}
      -> dh_num_tokens
let __proj__Mkdict_header__item__dh_ids_offset (projectee : dict_header) :
  Prims.nat=
  match projectee with
  | { dh_magic; dh_version; dh_num_tokens; dh_ids_offset; dh_tokens_offset;_}
      -> dh_ids_offset
let __proj__Mkdict_header__item__dh_tokens_offset (projectee : dict_header) :
  Prims.nat=
  match projectee with
  | { dh_magic; dh_version; dh_num_tokens; dh_ids_offset; dh_tokens_offset;_}
      -> dh_tokens_offset
type presence_header =
  {
  ph_magic: Prims.nat ;
  ph_version: Prims.nat ;
  ph_num_rgs: Prims.nat ;
  ph_num_tokens: Prims.nat }
let __proj__Mkpresence_header__item__ph_magic (projectee : presence_header) :
  Prims.nat=
  match projectee with
  | { ph_magic; ph_version; ph_num_rgs; ph_num_tokens;_} -> ph_magic
let __proj__Mkpresence_header__item__ph_version (projectee : presence_header)
  : Prims.nat=
  match projectee with
  | { ph_magic; ph_version; ph_num_rgs; ph_num_tokens;_} -> ph_version
let __proj__Mkpresence_header__item__ph_num_rgs (projectee : presence_header)
  : Prims.nat=
  match projectee with
  | { ph_magic; ph_version; ph_num_rgs; ph_num_tokens;_} -> ph_num_rgs
let __proj__Mkpresence_header__item__ph_num_tokens
  (projectee : presence_header) : Prims.nat=
  match projectee with
  | { ph_magic; ph_version; ph_num_rgs; ph_num_tokens;_} -> ph_num_tokens
let dict_header_size : Prims.nat= (Prims.of_int (32))
let read_dict_header (path : Prims.string) :
  dict_header FStar_Pervasives_Native.option=
  match read_companion_u32_le path Prims.int_zero with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some magic ->
      (match read_companion_u32_le path (Prims.of_int (4)) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some version ->
           (match read_companion_u32_le path (Prims.of_int (8)) with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some num_tokens ->
                (match read_companion_u64_le path (Prims.of_int (16)) with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some ids_offset ->
                     (match read_companion_u64_le path (Prims.of_int (24))
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some tokens_offset ->
                          FStar_Pervasives_Native.Some
                            {
                              dh_magic = magic;
                              dh_version = version;
                              dh_num_tokens = num_tokens;
                              dh_ids_offset = ids_offset;
                              dh_tokens_offset = tokens_offset
                            }))))
let presence_header_size : Prims.nat= (Prims.of_int (16))
let read_presence_header (path : Prims.string) :
  presence_header FStar_Pervasives_Native.option=
  match read_companion_u32_le path Prims.int_zero with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some magic ->
      (match read_companion_u32_le path (Prims.of_int (4)) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some version ->
           (match read_companion_u32_le path (Prims.of_int (8)) with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some num_rgs ->
                (match read_companion_u32_le path (Prims.of_int (12)) with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some num_tokens ->
                     FStar_Pervasives_Native.Some
                       {
                         ph_magic = magic;
                         ph_version = version;
                         ph_num_rgs = num_rgs;
                         ph_num_tokens = num_tokens
                       })))
let dict_header_ok (h : dict_header) : Prims.bool=
  (h.dh_magic = cotd_magic_u32) && (h.dh_version = layout_version)
let presence_header_ok (h : presence_header) : Prims.bool=
  (h.ph_magic = cotp_magic_u32) && (h.ph_version = layout_version)
let dict_decode_token (path : Prims.string) (h : dict_header)
  (id : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  if id >= h.dh_num_tokens
  then FStar_Pervasives_Native.None
  else
    (let eight = (Prims.of_int (8)) in
     let off_pos_start = h.dh_tokens_offset + (eight * id) in
     let off_pos_end = h.dh_tokens_offset + (eight * (id + Prims.int_one)) in
     match read_companion_u64_le path off_pos_start with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some token_start ->
         (match read_companion_u64_le path off_pos_end with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some token_end ->
              if token_end < token_start
              then FStar_Pervasives_Native.None
              else
                (let len = token_end - token_start in
                 read_companion_string path token_start len)))
let read_id_at (path : Prims.string) (h : dict_header) (i : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if i >= h.dh_num_tokens
  then FStar_Pervasives_Native.None
  else
    (let four = (Prims.of_int (4)) in
     let pos = h.dh_ids_offset + (four * i) in read_companion_u32_le path pos)
let compare_string (a : Prims.string) (b : Prims.string) : Prims.int=
  let la = FStar_String.strlen a in
  let lb = FStar_String.strlen b in
  let rec loop i =
    if (i >= la) && (i >= lb)
    then Prims.int_zero
    else
      if i >= la
      then (Prims.of_int (-1))
      else
        if i >= lb
        then Prims.int_one
        else
          (let ca = FStar_Char.int_of_char (FStar_String.index a i) in
           let cb = FStar_Char.int_of_char (FStar_String.index b i) in
           if ca < cb
           then (Prims.of_int (-1))
           else
             if ca > cb
             then Prims.int_one
             else
               if (i + Prims.int_one) > (la + lb)
               then Prims.int_zero
               else loop (i + Prims.int_one)) in
  if (la + lb) = Prims.int_zero then Prims.int_zero else loop Prims.int_zero
let rec bsearch_loop (path : Prims.string) (h : dict_header)
  (query : Prims.string) (lo : Prims.nat) (hi : Prims.nat) (fuel : Prims.nat)
  : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if lo > hi
    then FStar_Pervasives_Native.None
    else
      (let mid = lo + ((hi - lo) / (Prims.of_int (2))) in
       match read_id_at path h mid with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some id_at_mid ->
           (match dict_decode_token path h id_at_mid with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some tok ->
                let c = compare_string query tok in
                if c = Prims.int_zero
                then FStar_Pervasives_Native.Some id_at_mid
                else
                  if c < Prims.int_zero
                  then
                    (if mid = Prims.int_zero
                     then FStar_Pervasives_Native.None
                     else
                       bsearch_loop path h query lo (mid - Prims.int_one)
                         (fuel - Prims.int_one))
                  else
                    bsearch_loop path h query (mid + Prims.int_one) hi
                      (fuel - Prims.int_one)))
let dict_encode_token (path : Prims.string) (h : dict_header)
  (query : Prims.string) : Prims.nat FStar_Pervasives_Native.option=
  if h.dh_num_tokens = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    bsearch_loop path h query Prims.int_zero
      (h.dh_num_tokens - Prims.int_one) (h.dh_num_tokens + Prims.int_one)
let presence_test_bit (path : Prims.string) (h : presence_header)
  (rg : Prims.nat) (tok : Prims.nat) : Prims.bool=
  if (rg >= h.ph_num_rgs) || (tok >= h.ph_num_tokens)
  then false
  else
    (let nt = h.ph_num_tokens in
     let bit_index = (rg * nt) + tok in
     let eight = (Prims.of_int (8)) in
     let byte_index = bit_index / eight in
     let bit_in_byte = (mod) bit_index eight in
     let off = presence_header_size + byte_index in
     match read_companion_byte path off with
     | FStar_Pervasives_Native.None -> true
     | FStar_Pervasives_Native.Some b ->
         let mask =
           if bit_in_byte = Prims.int_zero
           then Prims.int_one
           else
             if bit_in_byte = Prims.int_one
             then (Prims.of_int (2))
             else
               if bit_in_byte = (Prims.of_int (2))
               then (Prims.of_int (4))
               else
                 if bit_in_byte = (Prims.of_int (3))
                 then (Prims.of_int (8))
                 else
                   if bit_in_byte = (Prims.of_int (4))
                   then (Prims.of_int (16))
                   else
                     if bit_in_byte = (Prims.of_int (5))
                     then (Prims.of_int (32))
                     else
                       if bit_in_byte = (Prims.of_int (6))
                       then (Prims.of_int (64))
                       else (Prims.of_int (128)) in
         ((mod) (b / mask) (Prims.of_int (2))) = Prims.int_one)
type companion_status =
  {
  cs_dict_path: Prims.string ;
  cs_presence_path: Prims.string ;
  cs_dict_header: dict_header FStar_Pervasives_Native.option ;
  cs_presence_header: presence_header FStar_Pervasives_Native.option }
let __proj__Mkcompanion_status__item__cs_dict_path
  (projectee : companion_status) : Prims.string=
  match projectee with
  | { cs_dict_path; cs_presence_path; cs_dict_header; cs_presence_header;_}
      -> cs_dict_path
let __proj__Mkcompanion_status__item__cs_presence_path
  (projectee : companion_status) : Prims.string=
  match projectee with
  | { cs_dict_path; cs_presence_path; cs_dict_header; cs_presence_header;_}
      -> cs_presence_path
let __proj__Mkcompanion_status__item__cs_dict_header
  (projectee : companion_status) :
  dict_header FStar_Pervasives_Native.option=
  match projectee with
  | { cs_dict_path; cs_presence_path; cs_dict_header; cs_presence_header;_}
      -> cs_dict_header
let __proj__Mkcompanion_status__item__cs_presence_header
  (projectee : companion_status) :
  presence_header FStar_Pervasives_Native.option=
  match projectee with
  | { cs_dict_path; cs_presence_path; cs_dict_header; cs_presence_header;_}
      -> cs_presence_header
let companion_status_ok (cs : companion_status) : Prims.bool=
  match ((cs.cs_dict_header), (cs.cs_presence_header)) with
  | (FStar_Pervasives_Native.Some dh, FStar_Pervasives_Native.Some ph) ->
      ((dict_header_ok dh) && (presence_header_ok ph)) &&
        (dh.dh_num_tokens = ph.ph_num_tokens)
  | uu___ -> false
let load_companion_status (dict_path : Prims.string)
  (presence_path : Prims.string) : companion_status=
  {
    cs_dict_path = dict_path;
    cs_presence_path = presence_path;
    cs_dict_header = (read_dict_header dict_path);
    cs_presence_header = (read_presence_header presence_path)
  }
let companion_encode (cs : companion_status) (tok : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs.cs_dict_header with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dh ->
      if Prims.op_Negation (dict_header_ok dh)
      then FStar_Pervasives_Native.None
      else dict_encode_token cs.cs_dict_path dh tok
let companion_decode (cs : companion_status) (id : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match cs.cs_dict_header with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dh ->
      if Prims.op_Negation (dict_header_ok dh)
      then FStar_Pervasives_Native.None
      else dict_decode_token cs.cs_dict_path dh id
let companion_rg_could_contain (cs : companion_status) (rg : Prims.nat)
  (tok_id : Prims.nat) : Prims.bool=
  match cs.cs_presence_header with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some ph ->
      if Prims.op_Negation (presence_header_ok ph)
      then true
      else presence_test_bit cs.cs_presence_path ph rg tok_id
