open Prims
type pattern_bound_ids =
  {
  pbi_s: Prims.nat FStar_Pervasives_Native.option ;
  pbi_p: Prims.nat FStar_Pervasives_Native.option ;
  pbi_o: Prims.nat FStar_Pervasives_Native.option }
let (__proj__Mkpattern_bound_ids__item__pbi_s :
  pattern_bound_ids -> Prims.nat FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { pbi_s; pbi_p; pbi_o;_} -> pbi_s
let (__proj__Mkpattern_bound_ids__item__pbi_p :
  pattern_bound_ids -> Prims.nat FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { pbi_s; pbi_p; pbi_o;_} -> pbi_p
let (__proj__Mkpattern_bound_ids__item__pbi_o :
  pattern_bound_ids -> Prims.nat FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { pbi_s; pbi_p; pbi_o;_} -> pbi_o
let (no_bounds : pattern_bound_ids) =
  {
    pbi_s = FStar_Pervasives_Native.None;
    pbi_p = FStar_Pervasives_Native.None;
    pbi_o = FStar_Pervasives_Native.None
  }
let (mk_bounds :
  Prims.nat FStar_Pervasives_Native.option ->
    Prims.nat FStar_Pervasives_Native.option ->
      Prims.nat FStar_Pervasives_Native.option -> pattern_bound_ids)
  = fun s -> fun p -> fun o -> { pbi_s = s; pbi_p = p; pbi_o = o }
let (predicate_can_match :
  RDF_CottasStore_PresenceBitmap.bitmap_handle FStar_Pervasives_Native.option
    -> Prims.nat -> Prims.nat FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun oh_p ->
    fun rg ->
      fun bound_p ->
        RDF_CottasStore_PresenceBitmap.rg_could_contain oh_p rg bound_p
let (subject_can_match :
  RDF_CottasStore_PresenceBitmap.bitmap_handle FStar_Pervasives_Native.option
    -> Prims.nat -> Prims.nat FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun oh_s ->
    fun rg ->
      fun bound_s ->
        RDF_CottasStore_PresenceBitmap.rg_could_contain oh_s rg bound_s
let (object_can_match :
  RDF_CottasStore_PresenceBitmap.bitmap_handle FStar_Pervasives_Native.option
    -> Prims.nat -> Prims.nat FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun oh_o ->
    fun rg ->
      fun bound_o ->
        RDF_CottasStore_PresenceBitmap.rg_could_contain oh_o rg bound_o
let (compound_po_can_match :
  RDF_CottasStore_CompoundPresenceBitmap.compound_handle
    FStar_Pervasives_Native.option ->
    Prims.nat ->
      Prims.nat FStar_Pervasives_Native.option ->
        Prims.nat FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun oh_compound ->
    fun rg ->
      fun bound_p ->
        fun bound_o ->
          RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair
            oh_compound rg bound_p bound_o
let (compound_sp_can_match :
  RDF_CottasStore_CompoundPresenceBitmap.compound_handle
    FStar_Pervasives_Native.option ->
    Prims.nat ->
      Prims.nat FStar_Pervasives_Native.option ->
        Prims.nat FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun oh_compound ->
    fun rg ->
      fun bound_s ->
        fun bound_p ->
          RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair
            oh_compound rg bound_s bound_p
let (rg_can_match :
  Prims.nat ->
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option ->
      Prims.nat FStar_Pervasives_Native.option ->
        RDF_CottasStore_PresenceBitmap.bitmap_handle
          FStar_Pervasives_Native.option ->
          Prims.nat FStar_Pervasives_Native.option ->
            RDF_CottasStore_PresenceBitmap.bitmap_handle
              FStar_Pervasives_Native.option ->
              Prims.nat FStar_Pervasives_Native.option ->
                RDF_CottasStore_CompoundPresenceBitmap.compound_handle
                  FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun rg ->
    fun oh_s ->
      fun bound_s ->
        fun oh_p ->
          fun bound_p ->
            fun oh_o ->
              fun bound_o ->
                fun oh_compound_po ->
                  (RDF_CottasStore_PresenceBitmap.rg_passes_all rg oh_s
                     bound_s oh_p bound_p oh_o bound_o)
                    &&
                    (RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair
                       oh_compound_po rg bound_p bound_o)
let (rg_can_match_for_pattern :
  Prims.nat ->
    pattern_bound_ids ->
      RDF_CottasStore_PresenceBitmap.bitmap_handle
        FStar_Pervasives_Native.option ->
        RDF_CottasStore_PresenceBitmap.bitmap_handle
          FStar_Pervasives_Native.option ->
          RDF_CottasStore_PresenceBitmap.bitmap_handle
            FStar_Pervasives_Native.option ->
            RDF_CottasStore_CompoundPresenceBitmap.compound_handle
              FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun rg ->
    fun bounds ->
      fun oh_s ->
        fun oh_p ->
          fun oh_o ->
            fun oh_compound_po ->
              rg_can_match rg oh_s bounds.pbi_s oh_p bounds.pbi_p oh_o
                bounds.pbi_o oh_compound_po
let rec (filter_candidates_by_prune :
  Prims.nat Prims.list ->
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option ->
      Prims.nat FStar_Pervasives_Native.option ->
        RDF_CottasStore_PresenceBitmap.bitmap_handle
          FStar_Pervasives_Native.option ->
          Prims.nat FStar_Pervasives_Native.option ->
            RDF_CottasStore_PresenceBitmap.bitmap_handle
              FStar_Pervasives_Native.option ->
              Prims.nat FStar_Pervasives_Native.option ->
                RDF_CottasStore_CompoundPresenceBitmap.compound_handle
                  FStar_Pervasives_Native.option -> Prims.nat Prims.list)
  =
  fun candidates ->
    fun oh_s ->
      fun bound_s ->
        fun oh_p ->
          fun bound_p ->
            fun oh_o ->
              fun bound_o ->
                fun oh_compound_po ->
                  match candidates with
                  | [] -> []
                  | rg::rest ->
                      let surviving_rest =
                        filter_candidates_by_prune rest oh_s bound_s oh_p
                          bound_p oh_o bound_o oh_compound_po in
                      if
                        rg_can_match rg oh_s bound_s oh_p bound_p oh_o
                          bound_o oh_compound_po
                      then rg :: surviving_rest
                      else surviving_rest
