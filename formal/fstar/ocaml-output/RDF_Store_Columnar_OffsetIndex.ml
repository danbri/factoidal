open Prims
let coto_magic_u32 : Prims.nat= (Prims.parse_int "0x4f544f43")
let offsets_layout_version : Prims.nat= Prims.int_one
let offset_header_size : Prims.nat= (Prims.of_int (16))
let offset_index_entry_size : Prims.nat= (Prims.of_int (8))
let offset_row_position_size : Prims.nat= (Prims.of_int (4))
type offset_header =
  {
  oh_magic: Prims.nat ;
  oh_version: Prims.nat ;
  oh_num_rgs: Prims.nat ;
  oh_num_preds: Prims.nat }
let __proj__Mkoffset_header__item__oh_magic (projectee : offset_header) :
  Prims.nat=
  match projectee with
  | { oh_magic; oh_version; oh_num_rgs; oh_num_preds;_} -> oh_magic
let __proj__Mkoffset_header__item__oh_version (projectee : offset_header) :
  Prims.nat=
  match projectee with
  | { oh_magic; oh_version; oh_num_rgs; oh_num_preds;_} -> oh_version
let __proj__Mkoffset_header__item__oh_num_rgs (projectee : offset_header) :
  Prims.nat=
  match projectee with
  | { oh_magic; oh_version; oh_num_rgs; oh_num_preds;_} -> oh_num_rgs
let __proj__Mkoffset_header__item__oh_num_preds (projectee : offset_header) :
  Prims.nat=
  match projectee with
  | { oh_magic; oh_version; oh_num_rgs; oh_num_preds;_} -> oh_num_preds
let offset_header_ok (h : offset_header) : Prims.bool=
  (h.oh_magic = coto_magic_u32) && (h.oh_version = offsets_layout_version)
let read_offset_header (path : Prims.string) :
  offset_header FStar_Pervasives_Native.option=
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
                 | FStar_Pervasives_Native.Some num_preds ->
                     FStar_Pervasives_Native.Some
                       {
                         oh_magic = magic;
                         oh_version = version;
                         oh_num_rgs = num_rgs;
                         oh_num_preds = num_preds
                       })))
type offset_handle = {
  oih_path: Prims.string ;
  oih_header: offset_header }
let __proj__Mkoffset_handle__item__oih_path (projectee : offset_handle) :
  Prims.string= match projectee with | { oih_path; oih_header;_} -> oih_path
let __proj__Mkoffset_handle__item__oih_header (projectee : offset_handle) :
  offset_header=
  match projectee with | { oih_path; oih_header;_} -> oih_header
let offset_handle_ok (h : offset_handle) : Prims.bool=
  offset_header_ok h.oih_header
type valid_offset_handle = offset_handle
let open_offsets (path : Prims.string) :
  offset_handle FStar_Pervasives_Native.option=
  match RDF_CottasStore_OnDiskIndex.mmap_companion_open path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some _file_size ->
      (match read_offset_header path with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some h ->
           if offset_header_ok h
           then
             FStar_Pervasives_Native.Some { oih_path = path; oih_header = h }
           else FStar_Pervasives_Native.None)
let cell_index (h : offset_header) (rg : Prims.nat) (pred_id : Prims.nat) :
  Prims.nat= (rg * h.oh_num_preds) + pred_id
let index_entry_offset (h : offset_header) (rg : Prims.nat)
  (pred_id : Prims.nat) : Prims.nat=
  offset_header_size + (offset_index_entry_size * (cell_index h rg pred_id))
let read_cell_start (h : valid_offset_handle) (rg : Prims.nat)
  (pred_id : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if
    (rg >= (h.oih_header).oh_num_rgs) ||
      (pred_id >= (h.oih_header).oh_num_preds)
  then FStar_Pervasives_Native.None
  else
    RDF_CottasStore_OnDiskIndex.read_companion_u64_le h.oih_path
      (index_entry_offset h.oih_header rg pred_id)
let read_cell_end (h : valid_offset_handle) (rg : Prims.nat)
  (pred_id : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if
    (rg >= (h.oih_header).oh_num_rgs) ||
      (pred_id >= (h.oih_header).oh_num_preds)
  then FStar_Pervasives_Native.None
  else
    RDF_CottasStore_OnDiskIndex.read_companion_u64_le h.oih_path
      (offset_header_size +
         (offset_index_entry_size *
            ((cell_index h.oih_header rg pred_id) + Prims.int_one)))
let row_positions_count_from_bounds (start_off : Prims.nat)
  (end_off : Prims.nat) : Prims.nat=
  if end_off < start_off
  then Prims.int_zero
  else (end_off - start_off) / offset_row_position_size
let read_row_position_at (h : valid_offset_handle) (start_off : Prims.nat)
  (i : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  RDF_CottasStore_OnDiskIndex.read_companion_u32_le h.oih_path
    (start_off + (offset_row_position_size * i))
type cell_view = {
  cv_start: Prims.nat ;
  cv_count: Prims.nat }
let __proj__Mkcell_view__item__cv_start (projectee : cell_view) : Prims.nat=
  match projectee with | { cv_start; cv_count;_} -> cv_start
let __proj__Mkcell_view__item__cv_count (projectee : cell_view) : Prims.nat=
  match projectee with | { cv_start; cv_count;_} -> cv_count
let row_positions_for (h : valid_offset_handle) (rg : Prims.nat)
  (pred_id : Prims.nat) : cell_view FStar_Pervasives_Native.option=
  if
    (rg >= (h.oih_header).oh_num_rgs) ||
      (pred_id >= (h.oih_header).oh_num_preds)
  then FStar_Pervasives_Native.None
  else
    (match read_cell_start h rg pred_id with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some start_off ->
         (match read_cell_end h rg pred_id with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some end_off ->
              if end_off < start_off
              then FStar_Pervasives_Native.None
              else
                FStar_Pervasives_Native.Some
                  {
                    cv_start = start_off;
                    cv_count =
                      (row_positions_count_from_bounds start_off end_off)
                  }))
type cell_decision =
  | CD_NoInfo 
  | CD_Empty 
  | CD_Use of cell_view 
let uu___is_CD_NoInfo (projectee : cell_decision) : Prims.bool=
  match projectee with | CD_NoInfo -> true | uu___ -> false
let uu___is_CD_Empty (projectee : cell_decision) : Prims.bool=
  match projectee with | CD_Empty -> true | uu___ -> false
let uu___is_CD_Use (projectee : cell_decision) : Prims.bool=
  match projectee with | CD_Use _0 -> true | uu___ -> false
let __proj__CD_Use__item___0 (projectee : cell_decision) : cell_view=
  match projectee with | CD_Use _0 -> _0
let row_positions_for_opt (oh : offset_handle FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_pred_id : Prims.nat FStar_Pervasives_Native.option)
  : cell_decision=
  match bound_pred_id with
  | FStar_Pervasives_Native.None -> CD_NoInfo
  | FStar_Pervasives_Native.Some p ->
      (match oh with
       | FStar_Pervasives_Native.None -> CD_NoInfo
       | FStar_Pervasives_Native.Some h ->
           if offset_handle_ok h
           then
             (match row_positions_for h rg p with
              | FStar_Pervasives_Native.None -> CD_NoInfo
              | FStar_Pervasives_Native.Some cv ->
                  if cv.cv_count = Prims.int_zero
                  then CD_Empty
                  else CD_Use cv)
           else CD_NoInfo)
let offset_num_rgs (h : valid_offset_handle) : Prims.nat=
  (h.oih_header).oh_num_rgs
let offset_num_preds (h : valid_offset_handle) : Prims.nat=
  (h.oih_header).oh_num_preds
let offsets_path_of (corpus_path : Prims.string) : Prims.string=
  Prims.strcat corpus_path ".p.offsets"
type rows_with_pred_t = Prims.nat -> Prims.nat -> Prims.nat Prims.list
type ('h, 'rowsuwithupred) offsets_built_correctly = unit
