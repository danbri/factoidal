open Prims
type pattern_bound_ids =
  {
  pbi_s: Prims.nat FStar_Pervasives_Native.option ;
  pbi_p: Prims.nat FStar_Pervasives_Native.option ;
  pbi_o: Prims.nat FStar_Pervasives_Native.option }
let __proj__Mkpattern_bound_ids__item__pbi_s (projectee : pattern_bound_ids)
  : Prims.nat FStar_Pervasives_Native.option=
  match projectee with | { pbi_s; pbi_p; pbi_o;_} -> pbi_s
let __proj__Mkpattern_bound_ids__item__pbi_p (projectee : pattern_bound_ids)
  : Prims.nat FStar_Pervasives_Native.option=
  match projectee with | { pbi_s; pbi_p; pbi_o;_} -> pbi_p
let __proj__Mkpattern_bound_ids__item__pbi_o (projectee : pattern_bound_ids)
  : Prims.nat FStar_Pervasives_Native.option=
  match projectee with | { pbi_s; pbi_p; pbi_o;_} -> pbi_o
let no_bounds : pattern_bound_ids=
  {
    pbi_s = FStar_Pervasives_Native.None;
    pbi_p = FStar_Pervasives_Native.None;
    pbi_o = FStar_Pervasives_Native.None
  }
let mk_bounds (s : Prims.nat FStar_Pervasives_Native.option)
  (p : Prims.nat FStar_Pervasives_Native.option)
  (o : Prims.nat FStar_Pervasives_Native.option) : pattern_bound_ids=
  { pbi_s = s; pbi_p = p; pbi_o = o }
let predicate_can_match
  (oh_p :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_p : Prims.nat FStar_Pervasives_Native.option) :
  Prims.bool= RDF_CottasStore_PresenceBitmap.rg_could_contain oh_p rg bound_p
let subject_can_match
  (oh_s :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_s : Prims.nat FStar_Pervasives_Native.option) :
  Prims.bool= RDF_CottasStore_PresenceBitmap.rg_could_contain oh_s rg bound_s
let object_can_match
  (oh_o :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_o : Prims.nat FStar_Pervasives_Native.option) :
  Prims.bool= RDF_CottasStore_PresenceBitmap.rg_could_contain oh_o rg bound_o
let compound_po_can_match
  (oh_compound :
    RDF_CottasStore_CompoundPresenceBitmap.compound_handle
      FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_p : Prims.nat FStar_Pervasives_Native.option)
  (bound_o : Prims.nat FStar_Pervasives_Native.option) : Prims.bool=
  RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair oh_compound
    rg bound_p bound_o
let compound_sp_can_match
  (oh_compound :
    RDF_CottasStore_CompoundPresenceBitmap.compound_handle
      FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_s : Prims.nat FStar_Pervasives_Native.option)
  (bound_p : Prims.nat FStar_Pervasives_Native.option) : Prims.bool=
  RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair oh_compound
    rg bound_s bound_p
let rg_can_match (rg : Prims.nat)
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
  (bound_o : Prims.nat FStar_Pervasives_Native.option)
  (oh_compound_po :
    RDF_CottasStore_CompoundPresenceBitmap.compound_handle
      FStar_Pervasives_Native.option)
  : Prims.bool=
  (RDF_CottasStore_PresenceBitmap.rg_passes_all rg oh_s bound_s oh_p bound_p
     oh_o bound_o)
    &&
    (RDF_CottasStore_CompoundPresenceBitmap.compound_rg_passes_pair
       oh_compound_po rg bound_p bound_o)
let rg_can_match_for_pattern (rg : Prims.nat) (bounds : pattern_bound_ids)
  (oh_s :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (oh_p :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (oh_o :
    RDF_CottasStore_PresenceBitmap.bitmap_handle
      FStar_Pervasives_Native.option)
  (oh_compound_po :
    RDF_CottasStore_CompoundPresenceBitmap.compound_handle
      FStar_Pervasives_Native.option)
  : Prims.bool=
  rg_can_match rg oh_s bounds.pbi_s oh_p bounds.pbi_p oh_o bounds.pbi_o
    oh_compound_po
let rec filter_candidates_by_prune (candidates : Prims.nat Prims.list)
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
  (bound_o : Prims.nat FStar_Pervasives_Native.option)
  (oh_compound_po :
    RDF_CottasStore_CompoundPresenceBitmap.compound_handle
      FStar_Pervasives_Native.option)
  : Prims.nat Prims.list=
  match candidates with
  | [] -> []
  | rg::rest ->
      let surviving_rest =
        filter_candidates_by_prune rest oh_s bound_s oh_p bound_p oh_o
          bound_o oh_compound_po in
      if
        rg_can_match rg oh_s bound_s oh_p bound_p oh_o bound_o oh_compound_po
      then rg :: surviving_rest
      else surviving_rest
