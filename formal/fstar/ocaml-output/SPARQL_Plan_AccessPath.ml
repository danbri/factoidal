open Prims
type access_path =
  | AP_Skip 
  | AP_OffsetJump of RDF_Store_Columnar_OffsetIndex.cell_view 
  | AP_FullScan 
let uu___is_AP_Skip (projectee : access_path) : Prims.bool=
  match projectee with | AP_Skip -> true | uu___ -> false
let uu___is_AP_OffsetJump (projectee : access_path) : Prims.bool=
  match projectee with | AP_OffsetJump _0 -> true | uu___ -> false
let __proj__AP_OffsetJump__item___0 (projectee : access_path) :
  RDF_Store_Columnar_OffsetIndex.cell_view=
  match projectee with | AP_OffsetJump _0 -> _0
let uu___is_AP_FullScan (projectee : access_path) : Prims.bool=
  match projectee with | AP_FullScan -> true | uu___ -> false
let access_path_eq (a : access_path) (b : access_path) : Prims.bool=
  match (a, b) with
  | (AP_Skip, AP_Skip) -> true
  | (AP_FullScan, AP_FullScan) -> true
  | (AP_OffsetJump cv1, AP_OffsetJump cv2) ->
      (cv1.RDF_Store_Columnar_OffsetIndex.cv_start =
         cv2.RDF_Store_Columnar_OffsetIndex.cv_start)
        &&
        (cv1.RDF_Store_Columnar_OffsetIndex.cv_count =
           cv2.RDF_Store_Columnar_OffsetIndex.cv_count)
  | (uu___, uu___1) -> false
let choose_access_path
  (oh_offsets :
    RDF_Store_Columnar_OffsetIndex.offset_handle
      FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bound_pred_id : Prims.nat FStar_Pervasives_Native.option)
  : access_path=
  match RDF_Store_Columnar_OffsetIndex.row_positions_for_opt oh_offsets rg
          bound_pred_id
  with
  | RDF_Store_Columnar_OffsetIndex.CD_NoInfo -> AP_FullScan
  | RDF_Store_Columnar_OffsetIndex.CD_Empty -> AP_Skip
  | RDF_Store_Columnar_OffsetIndex.CD_Use cv -> AP_OffsetJump cv
let choose_access_path_for_pattern
  (oh_offsets :
    RDF_Store_Columnar_OffsetIndex.offset_handle
      FStar_Pervasives_Native.option)
  (rg : Prims.nat) (bounds : SPARQL_Plan_Pruning.pattern_bound_ids) :
  access_path=
  choose_access_path oh_offsets rg bounds.SPARQL_Plan_Pruning.pbi_p
let rec choose_access_paths_for_rgs
  (oh_offsets :
    RDF_Store_Columnar_OffsetIndex.offset_handle
      FStar_Pervasives_Native.option)
  (candidates : Prims.nat Prims.list)
  (bounds : SPARQL_Plan_Pruning.pattern_bound_ids) :
  (Prims.nat * access_path) Prims.list=
  match candidates with
  | [] -> []
  | rg::rest ->
      let ap = choose_access_path_for_pattern oh_offsets rg bounds in
      (rg, ap) :: (choose_access_paths_for_rgs oh_offsets rest bounds)
let rec drop_skips (xs : (Prims.nat * access_path) Prims.list) :
  (Prims.nat * access_path) Prims.list=
  match xs with
  | [] -> []
  | (rg, ap)::tl ->
      (match ap with
       | AP_Skip -> drop_skips tl
       | uu___ -> (rg, ap) :: (drop_skips tl))
