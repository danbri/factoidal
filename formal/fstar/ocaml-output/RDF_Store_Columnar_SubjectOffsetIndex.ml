open Prims
let cots_magic_u32 : Prims.nat= (Prims.parse_int "0x53544f43")
let subject_offsets_layout_version : Prims.nat= Prims.int_one
let subject_offset_header_size : Prims.nat= (Prims.of_int (16))
let subject_offset_entry_size : Prims.nat= (Prims.of_int (16))
type subject_offset_header =
  {
  soh_magic: Prims.nat ;
  soh_version: Prims.nat ;
  soh_num_subjects: Prims.nat ;
  soh_num_rows_total: Prims.nat }
let __proj__Mksubject_offset_header__item__soh_magic
  (projectee : subject_offset_header) : Prims.nat=
  match projectee with
  | { soh_magic; soh_version; soh_num_subjects; soh_num_rows_total;_} ->
      soh_magic
let __proj__Mksubject_offset_header__item__soh_version
  (projectee : subject_offset_header) : Prims.nat=
  match projectee with
  | { soh_magic; soh_version; soh_num_subjects; soh_num_rows_total;_} ->
      soh_version
let __proj__Mksubject_offset_header__item__soh_num_subjects
  (projectee : subject_offset_header) : Prims.nat=
  match projectee with
  | { soh_magic; soh_version; soh_num_subjects; soh_num_rows_total;_} ->
      soh_num_subjects
let __proj__Mksubject_offset_header__item__soh_num_rows_total
  (projectee : subject_offset_header) : Prims.nat=
  match projectee with
  | { soh_magic; soh_version; soh_num_subjects; soh_num_rows_total;_} ->
      soh_num_rows_total
let subject_offset_header_ok (h : subject_offset_header) : Prims.bool=
  (h.soh_magic = cots_magic_u32) &&
    (h.soh_version = subject_offsets_layout_version)
let read_subject_offset_header (path : Prims.string) :
  subject_offset_header FStar_Pervasives_Native.option=
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
            | FStar_Pervasives_Native.Some num_subjects ->
                (match RDF_CottasStore_OnDiskIndex.read_companion_u32_le path
                         (Prims.of_int (12))
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some num_rows_total ->
                     FStar_Pervasives_Native.Some
                       {
                         soh_magic = magic;
                         soh_version = version;
                         soh_num_subjects = num_subjects;
                         soh_num_rows_total = num_rows_total
                       })))
type subject_offset_handle =
  {
  soih_path: Prims.string ;
  soih_header: subject_offset_header }
let __proj__Mksubject_offset_handle__item__soih_path
  (projectee : subject_offset_handle) : Prims.string=
  match projectee with | { soih_path; soih_header;_} -> soih_path
let __proj__Mksubject_offset_handle__item__soih_header
  (projectee : subject_offset_handle) : subject_offset_header=
  match projectee with | { soih_path; soih_header;_} -> soih_header
let subject_offset_handle_ok (h : subject_offset_handle) : Prims.bool=
  subject_offset_header_ok h.soih_header
type valid_subject_offset_handle = subject_offset_handle
let open_subject_offsets (path : Prims.string) :
  subject_offset_handle FStar_Pervasives_Native.option=
  match RDF_CottasStore_OnDiskIndex.mmap_companion_open path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some _file_size ->
      (match read_subject_offset_header path with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some h ->
           if subject_offset_header_ok h
           then
             FStar_Pervasives_Native.Some
               { soih_path = path; soih_header = h }
           else FStar_Pervasives_Native.None)
type subject_range = {
  sr_start: Prims.nat ;
  sr_end: Prims.nat }
let __proj__Mksubject_range__item__sr_start (projectee : subject_range) :
  Prims.nat= match projectee with | { sr_start; sr_end;_} -> sr_start
let __proj__Mksubject_range__item__sr_end (projectee : subject_range) :
  Prims.nat= match projectee with | { sr_start; sr_end;_} -> sr_end
let subject_range_count (r : subject_range) : Prims.nat=
  if r.sr_end < r.sr_start then Prims.int_zero else r.sr_end - r.sr_start
let entry_offset (h : subject_offset_header) (subject_id : Prims.nat) :
  Prims.nat=
  subject_offset_header_size + (subject_offset_entry_size * subject_id)
let range_for_subject (h : valid_subject_offset_handle)
  (subject_id : Prims.nat) : subject_range FStar_Pervasives_Native.option=
  if subject_id >= (h.soih_header).soh_num_subjects
  then FStar_Pervasives_Native.None
  else
    (match RDF_CottasStore_OnDiskIndex.read_companion_u64_le h.soih_path
             (entry_offset h.soih_header subject_id)
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some start_row ->
         (match RDF_CottasStore_OnDiskIndex.read_companion_u64_le h.soih_path
                  ((entry_offset h.soih_header subject_id) +
                     (Prims.of_int (8)))
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some end_row ->
              FStar_Pervasives_Native.Some
                { sr_start = start_row; sr_end = end_row }))
type subject_range_decision =
  | SRD_NoInfo 
  | SRD_Use of subject_range 
let uu___is_SRD_NoInfo (projectee : subject_range_decision) : Prims.bool=
  match projectee with | SRD_NoInfo -> true | uu___ -> false
let uu___is_SRD_Use (projectee : subject_range_decision) : Prims.bool=
  match projectee with | SRD_Use _0 -> true | uu___ -> false
let __proj__SRD_Use__item___0 (projectee : subject_range_decision) :
  subject_range= match projectee with | SRD_Use _0 -> _0
let range_for_subject_opt
  (oh : subject_offset_handle FStar_Pervasives_Native.option)
  (subject_id : Prims.nat FStar_Pervasives_Native.option) :
  subject_range_decision=
  match subject_id with
  | FStar_Pervasives_Native.None -> SRD_NoInfo
  | FStar_Pervasives_Native.Some sid ->
      (match oh with
       | FStar_Pervasives_Native.None -> SRD_NoInfo
       | FStar_Pervasives_Native.Some h ->
           if subject_offset_handle_ok h
           then
             (match range_for_subject h sid with
              | FStar_Pervasives_Native.None -> SRD_NoInfo
              | FStar_Pervasives_Native.Some r -> SRD_Use r)
           else SRD_NoInfo)
let subject_offset_num_subjects (h : valid_subject_offset_handle) :
  Prims.nat= (h.soih_header).soh_num_subjects
let subject_offsets_path_of (corpus_path : Prims.string) : Prims.string=
  Prims.strcat corpus_path ".s.offsets"
type rows_with_subject_t = Prims.nat -> Prims.nat Prims.list
type ('h, 'rowsuwithusubject) subject_offsets_built_correctly = unit
