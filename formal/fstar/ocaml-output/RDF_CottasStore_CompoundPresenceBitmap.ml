open Prims
let copo_magic_u32 : Prims.nat= (Prims.parse_int "0x4f504f43")
let compound_layout_version : Prims.nat= Prims.int_one
let compound_header_size : Prims.nat= (Prims.of_int (20))
type compound_header =
  {
  ch_magic: Prims.nat ;
  ch_version: Prims.nat ;
  ch_num_rgs: Prims.nat ;
  ch_pred_dict_size: Prims.nat ;
  ch_obj_dict_size: Prims.nat }
let __proj__Mkcompound_header__item__ch_magic (projectee : compound_header) :
  Prims.nat=
  match projectee with
  | { ch_magic; ch_version; ch_num_rgs; ch_pred_dict_size;
      ch_obj_dict_size;_} -> ch_magic
let __proj__Mkcompound_header__item__ch_version (projectee : compound_header)
  : Prims.nat=
  match projectee with
  | { ch_magic; ch_version; ch_num_rgs; ch_pred_dict_size;
      ch_obj_dict_size;_} -> ch_version
let __proj__Mkcompound_header__item__ch_num_rgs (projectee : compound_header)
  : Prims.nat=
  match projectee with
  | { ch_magic; ch_version; ch_num_rgs; ch_pred_dict_size;
      ch_obj_dict_size;_} -> ch_num_rgs
let __proj__Mkcompound_header__item__ch_pred_dict_size
  (projectee : compound_header) : Prims.nat=
  match projectee with
  | { ch_magic; ch_version; ch_num_rgs; ch_pred_dict_size;
      ch_obj_dict_size;_} -> ch_pred_dict_size
let __proj__Mkcompound_header__item__ch_obj_dict_size
  (projectee : compound_header) : Prims.nat=
  match projectee with
  | { ch_magic; ch_version; ch_num_rgs; ch_pred_dict_size;
      ch_obj_dict_size;_} -> ch_obj_dict_size
let compound_header_ok (h : compound_header) : Prims.bool=
  (h.ch_magic = copo_magic_u32) && (h.ch_version = compound_layout_version)
let read_compound_header (path : Prims.string) :
  compound_header FStar_Pervasives_Native.option=
  match RDF_CottasStore_OnDiskIndex.read_companion_u32_le path Prims.int_zero
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some magic ->
      (match RDF_CottasStore_OnDiskIndex.read_companion_u32_le path
               (Prims.of_int (4))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some version ->
           (match RDF_CottasStore_OnDiskIndex.read_companion_u32_le path
                    (Prims.of_int (8))
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some num_rgs ->
                (match RDF_CottasStore_OnDiskIndex.read_companion_u32_le path
                         (Prims.of_int (12))
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some pred_dict_size ->
                     (match RDF_CottasStore_OnDiskIndex.read_companion_u32_le
                              path (Prims.of_int (16))
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some obj_dict_size ->
                          FStar_Pervasives_Native.Some
                            {
                              ch_magic = magic;
                              ch_version = version;
                              ch_num_rgs = num_rgs;
                              ch_pred_dict_size = pred_dict_size;
                              ch_obj_dict_size = obj_dict_size
                            }))))
type compound_handle = {
  ph_path: Prims.string ;
  ph_header: compound_header }
let __proj__Mkcompound_handle__item__ph_path (projectee : compound_handle) :
  Prims.string= match projectee with | { ph_path; ph_header;_} -> ph_path
let __proj__Mkcompound_handle__item__ph_header (projectee : compound_handle)
  : compound_header=
  match projectee with | { ph_path; ph_header;_} -> ph_header
let compound_handle_ok (h : compound_handle) : Prims.bool=
  compound_header_ok h.ph_header
type valid_compound_handle = compound_handle
let open_compound (path : Prims.string) :
  compound_handle FStar_Pervasives_Native.option=
  match RDF_CottasStore_OnDiskIndex.mmap_companion_open path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some _file_size ->
      (match read_compound_header path with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some h ->
           if compound_header_ok h
           then
             FStar_Pervasives_Native.Some { ph_path = path; ph_header = h }
           else FStar_Pervasives_Native.None)
let read_rg_start_offset (h : valid_compound_handle) (rg : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if rg >= (h.ph_header).ch_num_rgs
  then FStar_Pervasives_Native.None
  else
    (let eight = (Prims.of_int (8)) in
     let pos = compound_header_size + (eight * rg) in
     RDF_CottasStore_OnDiskIndex.read_companion_u64_le h.ph_path pos)
let read_rg_end_offset (h : valid_compound_handle) (rg : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if rg >= (h.ph_header).ch_num_rgs
  then FStar_Pervasives_Native.None
  else
    (let eight = (Prims.of_int (8)) in
     let pos = compound_header_size + (eight * (rg + Prims.int_one)) in
     RDF_CottasStore_OnDiskIndex.read_companion_u64_le h.ph_path pos)
let read_pair_code_at (path : Prims.string) (pair_off : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  RDF_CottasStore_OnDiskIndex.read_companion_u64_le path pair_off
let pair_code (p : Prims.nat) (o : Prims.nat) : Prims.nat=
  let two_pow_32 = (Prims.parse_int "4294967296") in (p * two_pow_32) + o
let rec compound_bsearch (path : Prims.string) (start_off : Prims.nat)
  (npairs : Prims.nat) (target : Prims.nat) (lo : Prims.nat) (hi : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    if lo > hi
    then false
    else
      (let mid = lo + ((hi - lo) / (Prims.of_int (2))) in
       if mid >= npairs
       then true
       else
         (let eight = (Prims.of_int (8)) in
          let pair_off = start_off + (eight * mid) in
          match read_pair_code_at path pair_off with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some code ->
              if code = target
              then true
              else
                if code > target
                then
                  (if mid = Prims.int_zero
                   then false
                   else
                     compound_bsearch path start_off npairs target lo
                       (mid - Prims.int_one) (fuel - Prims.int_one))
                else
                  compound_bsearch path start_off npairs target
                    (mid + Prims.int_one) hi (fuel - Prims.int_one)))
let rg_could_contain_pair (h : valid_compound_handle) (rg : Prims.nat)
  (p : Prims.nat) (o : Prims.nat) : Prims.bool=
  if rg >= (h.ph_header).ch_num_rgs
  then false
  else
    if p >= (h.ph_header).ch_pred_dict_size
    then false
    else
      if o >= (h.ph_header).ch_obj_dict_size
      then false
      else
        (match read_rg_start_offset h rg with
         | FStar_Pervasives_Native.None -> true
         | FStar_Pervasives_Native.Some start_off ->
             (match read_rg_end_offset h rg with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some end_off ->
                  if end_off < start_off
                  then true
                  else
                    (let eight = (Prims.of_int (8)) in
                     let span = end_off - start_off in
                     let npairs = span / eight in
                     if npairs = Prims.int_zero
                     then false
                     else
                       (let target = pair_code p o in
                        compound_bsearch h.ph_path start_off npairs target
                          Prims.int_zero (npairs - Prims.int_one)
                          (npairs + Prims.int_one)))))
let rg_passes_pair (h : valid_compound_handle) (rg : Prims.nat)
  (bound_p : Prims.nat FStar_Pervasives_Native.option)
  (bound_o : Prims.nat FStar_Pervasives_Native.option) : Prims.bool=
  match (bound_p, bound_o) with
  | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.Some o) ->
      rg_could_contain_pair h rg p o
  | (uu___, uu___1) -> true
let compound_rg_passes_pair
  (oh : compound_handle FStar_Pervasives_Native.option) (rg : Prims.nat)
  (bound_p : Prims.nat FStar_Pervasives_Native.option)
  (bound_o : Prims.nat FStar_Pervasives_Native.option) : Prims.bool=
  match oh with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some h ->
      if compound_handle_ok h
      then rg_passes_pair h rg bound_p bound_o
      else true
let rg_passes_compound_and_per_column (rg : Prims.nat)
  (oh_compound : compound_handle FStar_Pervasives_Native.option)
  (oh_s :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (bound_s : Prims.nat FStar_Pervasives_Native.option)
  (oh_p :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (bound_p : Prims.nat FStar_Pervasives_Native.option)
  (oh_o :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (bound_o : Prims.nat FStar_Pervasives_Native.option) : Prims.bool=
  (RDF_CottasStore_PresenceBitmap.rg_passes_all rg oh_s bound_s oh_p bound_p
     oh_o bound_o)
    && (compound_rg_passes_pair oh_compound rg bound_p bound_o)
type pair_occurs_pred_t = Prims.nat -> Prims.nat -> Prims.nat -> Prims.bool
type ('h, 'pairuoccurs) compound_built_correctly = unit
let compound_num_rgs (h : valid_compound_handle) : Prims.nat=
  (h.ph_header).ch_num_rgs
let compound_pred_dict_size (h : valid_compound_handle) : Prims.nat=
  (h.ph_header).ch_pred_dict_size
let compound_obj_dict_size (h : valid_compound_handle) : Prims.nat=
  (h.ph_header).ch_obj_dict_size
