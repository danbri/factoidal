open Prims
type bitmap_handle =
  {
  bh_path: Prims.string ;
  bh_header: RDF_CottasStore_OnDiskIndex.presence_header }
let __proj__Mkbitmap_handle__item__bh_path (projectee : bitmap_handle) :
  Prims.string= match projectee with | { bh_path; bh_header;_} -> bh_path
let __proj__Mkbitmap_handle__item__bh_header (projectee : bitmap_handle) :
  RDF_CottasStore_OnDiskIndex.presence_header=
  match projectee with | { bh_path; bh_header;_} -> bh_header
let bitmap_handle_ok (h : bitmap_handle) : Prims.bool=
  RDF_CottasStore_OnDiskIndex.presence_header_ok h.bh_header
type valid_bitmap_handle = bitmap_handle
let open_bitmap (path : Prims.string) :
  bitmap_handle FStar_Pervasives_Native.option=
  match RDF_CottasStore_OnDiskIndex.mmap_companion_open path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some _file_size ->
      (match RDF_CottasStore_OnDiskIndex.read_presence_header path with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some h ->
           if RDF_CottasStore_OnDiskIndex.presence_header_ok h
           then
             FStar_Pervasives_Native.Some { bh_path = path; bh_header = h }
           else FStar_Pervasives_Native.None)
let rg_contains_token (h : valid_bitmap_handle) (rg : Prims.nat)
  (tok : Prims.nat) : Prims.bool=
  RDF_CottasStore_OnDiskIndex.presence_test_bit h.bh_path h.bh_header rg tok
let rg_could_contain (oh : bitmap_handle FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_tok_id : Prims.nat FStar_Pervasives_Native.option)
  : Prims.bool=
  match bound_tok_id with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some tok ->
      (match oh with
       | FStar_Pervasives_Native.None -> true
       | FStar_Pervasives_Native.Some h ->
           if bitmap_handle_ok h then rg_contains_token h rg tok else true)
type occurs_pred_t = Prims.nat -> Prims.nat -> Prims.bool
type ('h, 'occurs) bitmap_built_correctly = unit
let bitmap_num_rgs (h : valid_bitmap_handle) : Prims.nat=
  (h.bh_header).RDF_CottasStore_OnDiskIndex.ph_num_rgs
let bitmap_num_tokens (h : valid_bitmap_handle) : Prims.nat=
  (h.bh_header).RDF_CottasStore_OnDiskIndex.ph_num_tokens
let rg_passes_all (rg : Prims.nat)
  (oh_s : bitmap_handle FStar_Pervasives_Native.option)
  (bound_s : Prims.nat FStar_Pervasives_Native.option)
  (oh_p : bitmap_handle FStar_Pervasives_Native.option)
  (bound_p : Prims.nat FStar_Pervasives_Native.option)
  (oh_o : bitmap_handle FStar_Pervasives_Native.option)
  (bound_o : Prims.nat FStar_Pervasives_Native.option) : Prims.bool=
  ((rg_could_contain oh_s rg bound_s) && (rg_could_contain oh_p rg bound_p))
    && (rg_could_contain oh_o rg bound_o)
