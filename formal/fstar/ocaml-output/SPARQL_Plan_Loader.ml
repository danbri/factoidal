open Prims
type companion_file_status =
  | CFS_Present 
  | CFS_Missing 
  | CFS_Corrupt 
  | CFS_StaleSchema 
let uu___is_CFS_Present (projectee : companion_file_status) : Prims.bool=
  match projectee with | CFS_Present -> true | uu___ -> false
let uu___is_CFS_Missing (projectee : companion_file_status) : Prims.bool=
  match projectee with | CFS_Missing -> true | uu___ -> false
let uu___is_CFS_Corrupt (projectee : companion_file_status) : Prims.bool=
  match projectee with | CFS_Corrupt -> true | uu___ -> false
let uu___is_CFS_StaleSchema (projectee : companion_file_status) : Prims.bool=
  match projectee with | CFS_StaleSchema -> true | uu___ -> false
type load_strategy =
  | LS_Mmap 
  | LS_InRamFallback 
  | LS_Refuse 
let uu___is_LS_Mmap (projectee : load_strategy) : Prims.bool=
  match projectee with | LS_Mmap -> true | uu___ -> false
let uu___is_LS_InRamFallback (projectee : load_strategy) : Prims.bool=
  match projectee with | LS_InRamFallback -> true | uu___ -> false
let uu___is_LS_Refuse (projectee : load_strategy) : Prims.bool=
  match projectee with | LS_Refuse -> true | uu___ -> false
let choose_load_strategy (s : companion_file_status) : load_strategy=
  match s with
  | CFS_Present -> LS_Mmap
  | CFS_Missing -> LS_InRamFallback
  | CFS_Corrupt -> LS_InRamFallback
  | CFS_StaleSchema -> LS_InRamFallback
let is_warm_path (st : load_strategy) : Prims.bool=
  match st with
  | LS_Mmap -> true
  | LS_InRamFallback -> false
  | LS_Refuse -> false
let is_cold_path (st : load_strategy) : Prims.bool=
  match st with
  | LS_Mmap -> false
  | LS_InRamFallback -> true
  | LS_Refuse -> false
