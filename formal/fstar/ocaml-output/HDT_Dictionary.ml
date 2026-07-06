open Prims
let crc8_step (c : FStar_UInt32.t) : FStar_UInt32.t=
  if
    (FStar_UInt32.v (FStar_UInt32.logand c (Stdint.Uint32.of_int (0x80)))) <>
      Prims.int_zero
  then
    FStar_UInt32.logand
      (FStar_UInt32.logxor (FStar_UInt32.shift_left c Stdint.Uint32.one)
         (Stdint.Uint32.of_int (0x07))) (Stdint.Uint32.of_int (0xFF))
  else
    FStar_UInt32.logand (FStar_UInt32.shift_left c Stdint.Uint32.one)
      (Stdint.Uint32.of_int (0xFF))
let crc8_byte (crc : FStar_UInt32.t) (b : Prims.nat) : FStar_UInt32.t=
  let c0 = FStar_UInt32.logxor crc (FStar_UInt32.uint_to_t b) in
  crc8_step
    (crc8_step
       (crc8_step
          (crc8_step (crc8_step (crc8_step (crc8_step (crc8_step c0)))))))
let rec crc8_range (s : Prims.string) (pos : Prims.nat) (count : Prims.nat)
  (crc : FStar_UInt32.t) : FStar_UInt32.t FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then FStar_Pervasives_Native.Some crc
  else
    (match HDT_Container.hex_byte s pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         crc8_range s (pos + Prims.int_one) (count - Prims.int_one)
           (crc8_byte crc b))
let crc32c_step (c : FStar_UInt32.t) : FStar_UInt32.t=
  if
    (FStar_UInt32.v (FStar_UInt32.logand c Stdint.Uint32.one)) =
      Prims.int_one
  then
    FStar_UInt32.logxor (FStar_UInt32.shift_right c Stdint.Uint32.one)
      (Stdint.Uint32.of_string "0x82F63B78")
  else FStar_UInt32.shift_right c Stdint.Uint32.one
let crc32c_byte (crc : FStar_UInt32.t) (b : Prims.nat) : FStar_UInt32.t=
  let c0 = FStar_UInt32.logxor crc (FStar_UInt32.uint_to_t b) in
  crc32c_step
    (crc32c_step
       (crc32c_step
          (crc32c_step
             (crc32c_step (crc32c_step (crc32c_step (crc32c_step c0)))))))
let rec crc32c_range (s : Prims.string) (pos : Prims.nat) (count : Prims.nat)
  (crc : FStar_UInt32.t) : FStar_UInt32.t FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then FStar_Pervasives_Native.Some crc
  else
    (match HDT_Container.hex_byte s pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         crc32c_range s (pos + Prims.int_one) (count - Prims.int_one)
           (crc32c_byte crc b))
let crc32c_of_range (s : Prims.string) (pos : Prims.nat) (count : Prims.nat)
  : FStar_UInt32.t FStar_Pervasives_Native.option=
  match crc32c_range s pos count (Stdint.Uint32.of_string "0xFFFFFFFF") with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some c ->
      FStar_Pervasives_Native.Some
        (FStar_UInt32.logxor c (Stdint.Uint32.of_string "0xFFFFFFFF"))
let read_u8 (s : Prims.string) (pos : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match HDT_Container.hex_byte s pos with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
let read_u32_le (s : Prims.string) (pos : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((HDT_Container.hex_byte s pos),
          (HDT_Container.hex_byte s (pos + Prims.int_one)),
          (HDT_Container.hex_byte s (pos + (Prims.of_int (2)))),
          (HDT_Container.hex_byte s (pos + (Prims.of_int (3)))))
  with
  | (FStar_Pervasives_Native.Some b0, FStar_Pervasives_Native.Some b1,
     FStar_Pervasives_Native.Some b2, FStar_Pervasives_Native.Some b3) ->
      FStar_Pervasives_Native.Some
        (((b0 + ((Prims.of_int (256)) * b1)) +
            ((Prims.parse_int "65536") * b2))
           + ((Prims.parse_int "16777216") * b3))
  | uu___ -> FStar_Pervasives_Native.None
let nat_sub (a : Prims.nat) (b : Prims.nat) : Prims.nat=
  if a >= b then a - b else Prims.int_zero
let la_preamble_len (la : HDT_Container.hdt_log_array_info) : Prims.nat=
  nat_sub (nat_sub la.HDT_Container.la_data_start Prims.int_one)
    la.HDT_Container.la_start
let la_preamble_crc8_pos (la : HDT_Container.hdt_log_array_info) : Prims.nat=
  nat_sub la.HDT_Container.la_data_start Prims.int_one
let la_crc32_pos (la : HDT_Container.hdt_log_array_info) : Prims.nat=
  nat_sub la.HDT_Container.la_end (Prims.of_int (4))
let la_preamble_crc8_ok (s : Prims.string)
  (la : HDT_Container.hdt_log_array_info) : Prims.bool=
  match ((crc8_range s la.HDT_Container.la_start (la_preamble_len la)
            Stdint.Uint32.zero), (read_u8 s (la_preamble_crc8_pos la)))
  with
  | (FStar_Pervasives_Native.Some c, FStar_Pervasives_Native.Some stored) ->
      (FStar_UInt32.v c) = stored
  | (uu___, uu___1) -> false
let la_data_crc32_ok (s : Prims.string)
  (la : HDT_Container.hdt_log_array_info) : Prims.bool=
  match ((crc32c_of_range s la.HDT_Container.la_data_start
            la.HDT_Container.la_data_bytes),
          (read_u32_le s (la_crc32_pos la)))
  with
  | (FStar_Pervasives_Native.Some c, FStar_Pervasives_Native.Some stored) ->
      (FStar_UInt32.v c) = stored
  | (uu___, uu___1) -> false
let pfc_preamble_len (sec : HDT_Container.hdt_pfc_section) : Prims.nat=
  nat_sub
    (nat_sub (sec.HDT_Container.pfc_blocks).HDT_Container.la_start
       Prims.int_one) sec.HDT_Container.pfc_start
let pfc_preamble_crc8_pos (sec : HDT_Container.hdt_pfc_section) : Prims.nat=
  nat_sub (sec.HDT_Container.pfc_blocks).HDT_Container.la_start Prims.int_one
let pfc_preamble_crc8_ok (s : Prims.string)
  (sec : HDT_Container.hdt_pfc_section) : Prims.bool=
  match ((crc8_range s sec.HDT_Container.pfc_start (pfc_preamble_len sec)
            Stdint.Uint32.zero), (read_u8 s (pfc_preamble_crc8_pos sec)))
  with
  | (FStar_Pervasives_Native.Some c, FStar_Pervasives_Native.Some stored) ->
      (FStar_UInt32.v c) = stored
  | (uu___, uu___1) -> false
let pfc_packed_crc32_ok (s : Prims.string)
  (sec : HDT_Container.hdt_pfc_section) : Prims.bool=
  match ((crc32c_of_range s sec.HDT_Container.pfc_packed_start
            sec.HDT_Container.pfc_packed_bytes),
          (read_u32_le s
             (nat_sub sec.HDT_Container.pfc_end (Prims.of_int (4)))))
  with
  | (FStar_Pervasives_Native.Some c, FStar_Pervasives_Native.Some stored) ->
      (FStar_UInt32.v c) = stored
  | (uu___, uu___1) -> false
let pfc_section_crc_ok (s : Prims.string)
  (sec : HDT_Container.hdt_pfc_section) : Prims.bool=
  (((pfc_preamble_crc8_ok s sec) &&
      (la_preamble_crc8_ok s sec.HDT_Container.pfc_blocks))
     && (la_data_crc32_ok s sec.HDT_Container.pfc_blocks))
    && (pfc_packed_crc32_ok s sec)
let bit_divisor (b : Prims.nat) : Prims.pos=
  if b = Prims.int_zero
  then Prims.int_one
  else
    if b = Prims.int_one
    then (Prims.of_int (2))
    else
      if b = (Prims.of_int (2))
      then (Prims.of_int (4))
      else
        if b = (Prims.of_int (3))
        then (Prims.of_int (8))
        else
          if b = (Prims.of_int (4))
          then (Prims.of_int (16))
          else
            if b = (Prims.of_int (5))
            then (Prims.of_int (32))
            else
              if b = (Prims.of_int (6))
              then (Prims.of_int (64))
              else (Prims.of_int (128))
let rec la_bits_acc (s : Prims.string) (data_start : Prims.nat)
  (bitpos : Prims.nat) (nbits : Prims.nat) (mult : Prims.pos)
  (acc : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if nbits = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    (let byte_idx = data_start + (bitpos / (Prims.of_int (8))) in
     let shift = (mod) bitpos (Prims.of_int (8)) in
     match HDT_Container.hex_byte s byte_idx with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         let bitval = (mod) (b / (bit_divisor shift)) (Prims.of_int (2)) in
         la_bits_acc s data_start (bitpos + Prims.int_one)
           (nbits - Prims.int_one) (mult * (Prims.of_int (2)))
           (acc + (bitval * mult)))
let la_entry (s : Prims.string) (la : HDT_Container.hdt_log_array_info)
  (idx : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  la_bits_acc s la.HDT_Container.la_data_start
    (idx * la.HDT_Container.la_numbits) la.HDT_Container.la_numbits
    Prims.int_one Prims.int_zero
let hdt_pfc_num_blocks (sec : HDT_Container.hdt_pfc_section) : Prims.nat=
  if
    (sec.HDT_Container.pfc_blocks).HDT_Container.la_numentries =
      Prims.int_zero
  then Prims.int_zero
  else
    (sec.HDT_Container.pfc_blocks).HDT_Container.la_numentries -
      Prims.int_one
let pfc_block_abs_start (s : Prims.string)
  (sec : HDT_Container.hdt_pfc_section) (b : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match la_entry s sec.HDT_Container.pfc_blocks b with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rel ->
      FStar_Pervasives_Native.Some (sec.HDT_Container.pfc_packed_start + rel)
let pfc_read_first (s : Prims.string) (pos : Prims.nat) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  match HDT_Container.scan_nul s pos (FStar_String.strlen s) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some nul_pos ->
      (match HDT_Container.bytes_to_string s pos (nul_pos - pos) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some str ->
           FStar_Pervasives_Native.Some (str, (nul_pos + Prims.int_one)))
let pfc_read_suffix (s : Prims.string) (pos : Prims.nat)
  (prev : Prims.string) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  match HDT_Container.vbyte_decode s pos with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (plen, p1) ->
      if plen > (FStar_String.strlen prev)
      then FStar_Pervasives_Native.None
      else
        (match HDT_Container.scan_nul s p1 (FStar_String.strlen s) with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some nul_pos ->
             (match HDT_Container.bytes_to_string s p1 (nul_pos - p1) with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some suffix ->
                  let prefix = FStar_String.sub prev Prims.int_zero plen in
                  FStar_Pervasives_Native.Some
                    ((Prims.strcat prefix suffix), (nul_pos + Prims.int_one))))
let rec pfc_walk_suffixes (s : Prims.string) (at : Prims.nat)
  (prev : Prims.string) (remaining : Prims.pos) :
  Prims.string FStar_Pervasives_Native.option=
  match pfc_read_suffix s at prev with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (str, at') ->
      if remaining = Prims.int_one
      then FStar_Pervasives_Native.Some str
      else pfc_walk_suffixes s at' str (remaining - Prims.int_one)
let rec decode_block_acc (s : Prims.string) (pos : Prims.nat)
  (prev : Prims.string) (remaining : Prims.nat)
  (acc : Prims.string Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
  else
    (match pfc_read_suffix s pos prev with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (str, pos') ->
         decode_block_acc s pos' str (remaining - Prims.int_one) (str :: acc))
let decode_block (s : Prims.string) (block_start : Prims.nat)
  (count : Prims.nat) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match pfc_read_first s block_start with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (first, pos1) ->
         decode_block_acc s pos1 first (count - Prims.int_one) [first])
let block_string_count (sec : HDT_Container.hdt_pfc_section)
  (numblocks : Prims.nat) (b : Prims.nat) : Prims.nat=
  if (b + Prims.int_one) = numblocks
  then
    nat_sub sec.HDT_Container.pfc_numstrings
      (b * sec.HDT_Container.pfc_blocksize)
  else sec.HDT_Container.pfc_blocksize
let rec decode_section_acc (s : Prims.string)
  (sec : HDT_Container.hdt_pfc_section) (block_idx : Prims.nat)
  (numblocks : Prims.nat) (acc : Prims.string Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  if block_idx >= numblocks
  then FStar_Pervasives_Native.Some acc
  else
    (match pfc_block_abs_start s sec block_idx with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some bstart ->
         let count = block_string_count sec numblocks block_idx in
         (match decode_block s bstart count with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some strs ->
              decode_section_acc s sec (block_idx + Prims.int_one) numblocks
                (FStar_List_Tot_Base.op_At acc strs)))
let decode_section (s : Prims.string) (sec : HDT_Container.hdt_pfc_section) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  if sec.HDT_Container.pfc_numstrings = Prims.int_zero
  then FStar_Pervasives_Native.Some []
  else decode_section_acc s sec Prims.int_zero (hdt_pfc_num_blocks sec) []
let pfc_extract (s : Prims.string) (sec : HDT_Container.hdt_pfc_section)
  (id : Prims.pos) : Prims.string FStar_Pervasives_Native.option=
  if
    (id > sec.HDT_Container.pfc_numstrings) ||
      (sec.HDT_Container.pfc_blocksize = Prims.int_zero)
  then FStar_Pervasives_Native.None
  else
    (let rank = id - Prims.int_one in
     let block_idx = rank / sec.HDT_Container.pfc_blocksize in
     let offset = (mod) rank sec.HDT_Container.pfc_blocksize in
     match pfc_block_abs_start s sec block_idx with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some bstart ->
         (match pfc_read_first s bstart with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (first, pos1) ->
              if offset = Prims.int_zero
              then FStar_Pervasives_Native.Some first
              else pfc_walk_suffixes s pos1 first offset))
let pfc_block_first_string (s : Prims.string)
  (sec : HDT_Container.hdt_pfc_section) (block_idx : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match pfc_block_abs_start s sec block_idx with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some bstart ->
      (match pfc_read_first s bstart with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (first, uu___) ->
           FStar_Pervasives_Native.Some first)
let rec pfc_index_of (target : Prims.string) (strs : Prims.string Prims.list)
  (idx : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match strs with
  | [] -> FStar_Pervasives_Native.None
  | x::rest ->
      if x = target
      then FStar_Pervasives_Native.Some idx
      else pfc_index_of target rest (idx + Prims.int_one)
let rec pfc_find_block (s : Prims.string)
  (sec : HDT_Container.hdt_pfc_section) (target : Prims.string)
  (lo : Prims.nat) (hi : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if lo >= hi
  then FStar_Pervasives_Native.Some lo
  else
    (let mid = ((lo + hi) + Prims.int_one) / (Prims.of_int (2)) in
     match pfc_block_first_string s sec mid with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some head ->
         if (head = target) || (RDF_Graph_Executable.string_lt head target)
         then pfc_find_block s sec target mid hi
         else pfc_find_block s sec target lo (mid - Prims.int_one))
let pfc_locate (s : Prims.string) (sec : HDT_Container.hdt_pfc_section)
  (target : Prims.string) : Prims.pos FStar_Pervasives_Native.option=
  let numblocks = hdt_pfc_num_blocks sec in
  if numblocks = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match pfc_find_block s sec target Prims.int_zero
             (numblocks - Prims.int_one)
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some block_idx ->
         let count = block_string_count sec numblocks block_idx in
         (match pfc_block_abs_start s sec block_idx with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some bstart ->
              (match decode_block s bstart count with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some strs ->
                   (match pfc_index_of target strs Prims.int_zero with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some k ->
                        FStar_Pervasives_Native.Some
                          (((block_idx * sec.HDT_Container.pfc_blocksize) + k)
                             + Prims.int_one)))))
let hdt_term_of_string (s : Prims.string) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let c0 = FStar_String.index s Prims.int_zero in
     if
       (((FStar_Char.int_of_char c0) = (Prims.of_int (0x5F))) &&
          (len > Prims.int_one))
         &&
         ((FStar_Char.int_of_char (FStar_String.index s Prims.int_one)) =
            (Prims.of_int (0x3A)))
     then
       match Parser_NTriples.parse_bnode s Prims.int_zero with
       | Parser_Combinators.ParseOk (b, pos) ->
           (if pos = len
            then FStar_Pervasives_Native.Some (RDF_Term.T_BNode b)
            else FStar_Pervasives_Native.None)
       | Parser_Combinators.ParseFail (uu___1, uu___2) ->
           FStar_Pervasives_Native.None
     else
       if (FStar_Char.int_of_char c0) = (Prims.of_int (0x22))
       then
         (match Parser_NTriples.parse_literal s Prims.int_zero with
          | Parser_Combinators.ParseOk (l, pos) ->
              if pos = len
              then FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
              else FStar_Pervasives_Native.None
          | Parser_Combinators.ParseFail (uu___2, uu___3) ->
              FStar_Pervasives_Native.None)
       else
         if RDF_Term.is_iri s
         then FStar_Pervasives_Native.Some (RDF_Term.T_IRI s)
         else FStar_Pervasives_Native.None)
let hdt_string_of_term (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> i
  | uu___ -> RDF_NQuads_Serialize.nq_term_to_string t
type hdt_role =
  | Role_Subject 
  | Role_Predicate 
  | Role_Object 
let uu___is_Role_Subject (projectee : hdt_role) : Prims.bool=
  match projectee with | Role_Subject -> true | uu___ -> false
let uu___is_Role_Predicate (projectee : hdt_role) : Prims.bool=
  match projectee with | Role_Predicate -> true | uu___ -> false
let uu___is_Role_Object (projectee : hdt_role) : Prims.bool=
  match projectee with | Role_Object -> true | uu___ -> false
let hdt_id_to_term (s : Prims.string) (inv : HDT_Container.hdt_inventory)
  (role : hdt_role) (id : Prims.pos) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  let nshared =
    (inv.HDT_Container.inv_dict_shared).HDT_Container.pfc_numstrings in
  let extracted =
    match role with
    | Role_Predicate ->
        pfc_extract s inv.HDT_Container.inv_dict_predicates id
    | Role_Subject ->
        if id <= nshared
        then pfc_extract s inv.HDT_Container.inv_dict_shared id
        else pfc_extract s inv.HDT_Container.inv_dict_subjects (id - nshared)
    | Role_Object ->
        if id <= nshared
        then pfc_extract s inv.HDT_Container.inv_dict_shared id
        else pfc_extract s inv.HDT_Container.inv_dict_objects (id - nshared) in
  match extracted with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some str -> hdt_term_of_string str
let hdt_term_to_id (s : Prims.string) (inv : HDT_Container.hdt_inventory)
  (role : hdt_role) (term : RDF_Term.rdf_term) :
  Prims.pos FStar_Pervasives_Native.option=
  let dstr = hdt_string_of_term term in
  let nshared =
    (inv.HDT_Container.inv_dict_shared).HDT_Container.pfc_numstrings in
  match role with
  | Role_Predicate -> pfc_locate s inv.HDT_Container.inv_dict_predicates dstr
  | Role_Subject ->
      (match pfc_locate s inv.HDT_Container.inv_dict_shared dstr with
       | FStar_Pervasives_Native.Some id -> FStar_Pervasives_Native.Some id
       | FStar_Pervasives_Native.None ->
           (match pfc_locate s inv.HDT_Container.inv_dict_subjects dstr with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some id ->
                FStar_Pervasives_Native.Some (nshared + id)))
  | Role_Object ->
      (match pfc_locate s inv.HDT_Container.inv_dict_shared dstr with
       | FStar_Pervasives_Native.Some id -> FStar_Pervasives_Native.Some id
       | FStar_Pervasives_Native.None ->
           (match pfc_locate s inv.HDT_Container.inv_dict_objects dstr with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some id ->
                FStar_Pervasives_Native.Some (nshared + id)))
let hdt_role_max_id (inv : HDT_Container.hdt_inventory) (role : hdt_role) :
  Prims.nat=
  let nshared =
    (inv.HDT_Container.inv_dict_shared).HDT_Container.pfc_numstrings in
  match role with
  | Role_Predicate ->
      (inv.HDT_Container.inv_dict_predicates).HDT_Container.pfc_numstrings
  | Role_Subject ->
      nshared +
        (inv.HDT_Container.inv_dict_subjects).HDT_Container.pfc_numstrings
  | Role_Object ->
      nshared +
        (inv.HDT_Container.inv_dict_objects).HDT_Container.pfc_numstrings
