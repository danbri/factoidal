open Prims
type hdt_triples_info =
  {
  tri_bitmap_y: HDT_Container.hdt_bitmap_info ;
  tri_bitmap_z: HDT_Container.hdt_bitmap_info ;
  tri_array_y: HDT_Container.hdt_log_array_info ;
  tri_array_z: HDT_Container.hdt_log_array_info }
let __proj__Mkhdt_triples_info__item__tri_bitmap_y
  (projectee : hdt_triples_info) : HDT_Container.hdt_bitmap_info=
  match projectee with
  | { tri_bitmap_y; tri_bitmap_z; tri_array_y; tri_array_z;_} -> tri_bitmap_y
let __proj__Mkhdt_triples_info__item__tri_bitmap_z
  (projectee : hdt_triples_info) : HDT_Container.hdt_bitmap_info=
  match projectee with
  | { tri_bitmap_y; tri_bitmap_z; tri_array_y; tri_array_z;_} -> tri_bitmap_z
let __proj__Mkhdt_triples_info__item__tri_array_y
  (projectee : hdt_triples_info) : HDT_Container.hdt_log_array_info=
  match projectee with
  | { tri_bitmap_y; tri_bitmap_z; tri_array_y; tri_array_z;_} -> tri_array_y
let __proj__Mkhdt_triples_info__item__tri_array_z
  (projectee : hdt_triples_info) : HDT_Container.hdt_log_array_info=
  match projectee with
  | { tri_bitmap_y; tri_bitmap_z; tri_array_y; tri_array_z;_} -> tri_array_z
let parse_triples_info (s : Prims.string) (pos : Prims.nat) :
  hdt_triples_info FStar_Pervasives_Native.option=
  match HDT_Container.parse_bitmap_info s pos with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some bmy ->
      (match HDT_Container.parse_bitmap_info s bmy.HDT_Container.bm_end with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some bmz ->
           (match HDT_Container.parse_log_array_info s
                    bmz.HDT_Container.bm_end
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some lay ->
                (match HDT_Container.parse_log_array_info s
                         lay.HDT_Container.la_end
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some laz ->
                     FStar_Pervasives_Native.Some
                       {
                         tri_bitmap_y = bmy;
                         tri_bitmap_z = bmz;
                         tri_array_y = lay;
                         tri_array_z = laz
                       })))
let hdt_read_triples (s : Prims.string) (inv : HDT_Container.hdt_inventory) :
  hdt_triples_info FStar_Pervasives_Native.option=
  parse_triples_info s inv.HDT_Container.inv_triples_data_start
let bm_preamble_len (bm : HDT_Container.hdt_bitmap_info) : Prims.nat=
  HDT_Dictionary.nat_sub
    (HDT_Dictionary.nat_sub bm.HDT_Container.bm_data_start Prims.int_one)
    bm.HDT_Container.bm_start
let bm_preamble_crc8_pos (bm : HDT_Container.hdt_bitmap_info) : Prims.nat=
  HDT_Dictionary.nat_sub bm.HDT_Container.bm_data_start Prims.int_one
let bm_preamble_crc8_ok (s : Prims.string)
  (bm : HDT_Container.hdt_bitmap_info) : Prims.bool=
  match ((HDT_Dictionary.crc8_range s bm.HDT_Container.bm_start
            (bm_preamble_len bm) Prims.int_zero),
          (HDT_Dictionary.read_u8 s (bm_preamble_crc8_pos bm)))
  with
  | (FStar_Pervasives_Native.Some c, FStar_Pervasives_Native.Some stored) ->
      c = stored
  | (uu___, uu___1) -> false
let bm_data_crc32_ok (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info)
  : Prims.bool=
  match ((HDT_Dictionary.crc32c_of_range s bm.HDT_Container.bm_data_start
            bm.HDT_Container.bm_data_bytes),
          (HDT_Dictionary.read_u32_le s
             (HDT_Dictionary.nat_sub bm.HDT_Container.bm_end
                (Prims.of_int (4)))))
  with
  | (FStar_Pervasives_Native.Some c, FStar_Pervasives_Native.Some stored) ->
      c = stored
  | (uu___, uu___1) -> false
let bitmap_crc_ok (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info) :
  Prims.bool= (bm_preamble_crc8_ok s bm) && (bm_data_crc32_ok s bm)
let triples_crc_ok (s : Prims.string) (t : hdt_triples_info) : Prims.bool=
  (((((bitmap_crc_ok s t.tri_bitmap_y) && (bitmap_crc_ok s t.tri_bitmap_z))
       && (HDT_Dictionary.la_preamble_crc8_ok s t.tri_array_y))
      && (HDT_Dictionary.la_data_crc32_ok s t.tri_array_y))
     && (HDT_Dictionary.la_preamble_crc8_ok s t.tri_array_z))
    && (HDT_Dictionary.la_data_crc32_ok s t.tri_array_z)
let bit_at (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info)
  (i : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if i >= bm.HDT_Container.bm_numbits
  then FStar_Pervasives_Native.None
  else
    (match HDT_Dictionary.la_bits_acc s bm.HDT_Container.bm_data_start i
             Prims.int_one Prims.int_one Prims.int_zero
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some v ->
         FStar_Pervasives_Native.Some (v = Prims.int_one))
let rec rank1_upto (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info)
  (pos : Prims.nat) (fuel : Prims.nat) (acc : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    (match bit_at s bm pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         rank1_upto s bm (pos + Prims.int_one) (fuel - Prims.int_one)
           (if b then acc + Prims.int_one else acc))
let rank1 (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info)
  (i : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if i >= bm.HDT_Container.bm_numbits
  then FStar_Pervasives_Native.None
  else rank1_upto s bm Prims.int_zero (i + Prims.int_one) Prims.int_zero
let rec select1_scan (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info)
  (pos : Prims.nat) (fuel : Prims.nat) (target : Prims.nat)
  (seen : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match bit_at s bm pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         let seen' = if b then seen + Prims.int_one else seen in
         if b && (seen' = target)
         then FStar_Pervasives_Native.Some pos
         else
           select1_scan s bm (pos + Prims.int_one) (fuel - Prims.int_one)
             target seen')
let select1 (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info)
  (k : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  select1_scan s bm Prims.int_zero bm.HDT_Container.bm_numbits
    (k + Prims.int_one) Prims.int_zero
let children_range (s : Prims.string) (bm : HDT_Container.hdt_bitmap_info)
  (idx : Prims.nat) : (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  match select1 s bm idx with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some hi ->
      if idx = Prims.int_zero
      then FStar_Pervasives_Native.Some (Prims.int_zero, hi)
      else
        (match select1 s bm (idx - Prims.int_one) with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some prev ->
             FStar_Pervasives_Native.Some ((prev + Prims.int_one), hi))
let rec collect_range (s : Prims.string)
  (la : HDT_Container.hdt_log_array_info) (pos : Prims.nat)
  (count : Prims.nat) (acc : Prims.nat Prims.list) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
  else
    (match HDT_Dictionary.la_entry s la pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some v ->
         collect_range s la (pos + Prims.int_one) (count - Prims.int_one) (v
           :: acc))
let range_count (lo : Prims.nat) (hi : Prims.nat) : Prims.nat=
  if hi >= lo then (hi - lo) + Prims.int_one else Prims.int_zero
let rec walk_y_positions (s : Prims.string) (t : hdt_triples_info)
  (y : Prims.nat) (count : Prims.nat)
  (acc : (Prims.nat * Prims.nat) Prims.list) :
  (Prims.nat * Prims.nat) Prims.list FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    (match HDT_Dictionary.la_entry s t.tri_array_y y with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some p ->
         (match children_range s t.tri_bitmap_z y with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (zlo, zhi) ->
              (match collect_range s t.tri_array_z zlo (range_count zlo zhi)
                       []
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some objs ->
                   let pairs = FStar_List_Tot_Base.map (fun o -> (p, o)) objs in
                   walk_y_positions s t (y + Prims.int_one)
                     (count - Prims.int_one)
                     (FStar_List_Tot_Base.op_At acc pairs))))
let hdt_triples_for_subject (s : Prims.string) (t : hdt_triples_info)
  (subj : Prims.pos) :
  (Prims.nat * Prims.nat) Prims.list FStar_Pervasives_Native.option=
  match children_range s t.tri_bitmap_y (subj - Prims.int_one) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ylo, yhi) ->
      walk_y_positions s t ylo (range_count ylo yhi) []
let hdt_triple_count (t : hdt_triples_info) : Prims.nat=
  (t.tri_array_z).HDT_Container.la_numentries
let hdt_num_subjects (s : Prims.string) (t : hdt_triples_info) :
  Prims.nat FStar_Pervasives_Native.option=
  let bm = t.tri_bitmap_y in
  if bm.HDT_Container.bm_numbits = Prims.int_zero
  then FStar_Pervasives_Native.Some Prims.int_zero
  else rank1 s bm (bm.HDT_Container.bm_numbits - Prims.int_one)
type hdt_id_triple = {
  it_s: Prims.nat ;
  it_p: Prims.nat ;
  it_o: Prims.nat }
let __proj__Mkhdt_id_triple__item__it_s (projectee : hdt_id_triple) :
  Prims.nat= match projectee with | { it_s; it_p; it_o;_} -> it_s
let __proj__Mkhdt_id_triple__item__it_p (projectee : hdt_id_triple) :
  Prims.nat= match projectee with | { it_s; it_p; it_o;_} -> it_p
let __proj__Mkhdt_id_triple__item__it_o (projectee : hdt_id_triple) :
  Prims.nat= match projectee with | { it_s; it_p; it_o;_} -> it_o
let rec hdt_enumerate_subjects (s : Prims.string) (t : hdt_triples_info)
  (subj : Prims.pos) (fuel : Prims.nat) (acc : hdt_id_triple Prims.list) :
  hdt_id_triple Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    (match hdt_triples_for_subject s t subj with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some pairs ->
         let new_triples =
           FStar_List_Tot_Base.map
             (fun uu___1 ->
                match uu___1 with
                | (p, o) -> { it_s = subj; it_p = p; it_o = o }) pairs in
         hdt_enumerate_subjects s t (subj + Prims.int_one)
           (fuel - Prims.int_one) (FStar_List_Tot_Base.op_At acc new_triples))
let hdt_enumerate_all (s : Prims.string) (t : hdt_triples_info) :
  hdt_id_triple Prims.list FStar_Pervasives_Native.option=
  match hdt_num_subjects s t with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some uu___ when uu___ = Prims.int_zero ->
      FStar_Pervasives_Native.Some []
  | FStar_Pervasives_Native.Some n ->
      hdt_enumerate_subjects s t Prims.int_one n []
