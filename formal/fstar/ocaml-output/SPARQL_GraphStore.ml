open Prims
type graph_key = Prims.string
type gs_named =
  {
  gn_iri: graph_key ;
  gn_graph: RDF_Graph_Executable.rdf_graph }
let __proj__Mkgs_named__item__gn_iri (projectee : gs_named) : graph_key=
  match projectee with | { gn_iri; gn_graph;_} -> gn_iri
let __proj__Mkgs_named__item__gn_graph (projectee : gs_named) :
  RDF_Graph_Executable.rdf_graph=
  match projectee with | { gn_iri; gn_graph;_} -> gn_graph
type graph_store =
  {
  gs_default: RDF_Graph_Executable.rdf_graph ;
  gs_named: gs_named Prims.list }
let __proj__Mkgraph_store__item__gs_default (projectee : graph_store) :
  RDF_Graph_Executable.rdf_graph=
  match projectee with | { gs_default; gs_named = gs_named1;_} -> gs_default
let __proj__Mkgraph_store__item__gs_named (projectee : graph_store) :
  gs_named Prims.list=
  match projectee with | { gs_default; gs_named = gs_named1;_} -> gs_named1
let empty_store : graph_store=
  { gs_default = RDF_Graph_Executable.empty_graph; gs_named = [] }
let rec lookup_named (key : graph_key) (xs : gs_named Prims.list) :
  RDF_Graph_Executable.rdf_graph FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.None
  | hd::tl ->
      if hd.gn_iri = key
      then FStar_Pervasives_Native.Some (hd.gn_graph)
      else lookup_named key tl
let rec replace_named (key : graph_key) (g : RDF_Graph_Executable.rdf_graph)
  (xs : gs_named Prims.list) : gs_named Prims.list=
  match xs with
  | [] -> [{ gn_iri = key; gn_graph = g }]
  | hd::tl ->
      if hd.gn_iri = key
      then { gn_iri = key; gn_graph = g } :: tl
      else hd :: (replace_named key g tl)
let rec remove_named (key : graph_key) (xs : gs_named Prims.list) :
  gs_named Prims.list=
  match xs with
  | [] -> []
  | hd::tl -> if hd.gn_iri = key then tl else hd :: (remove_named key tl)
let rec named_exists (key : graph_key) (xs : gs_named Prims.list) :
  Prims.bool=
  match xs with
  | [] -> false
  | hd::tl -> if hd.gn_iri = key then true else named_exists key tl
type gs_target =
  | GT_Default 
  | GT_Named of graph_key 
let uu___is_GT_Default (projectee : gs_target) : Prims.bool=
  match projectee with | GT_Default -> true | uu___ -> false
let uu___is_GT_Named (projectee : gs_target) : Prims.bool=
  match projectee with | GT_Named _0 -> true | uu___ -> false
let __proj__GT_Named__item___0 (projectee : gs_target) : graph_key=
  match projectee with | GT_Named _0 -> _0
let gsp_get (t : gs_target) (s : graph_store) :
  RDF_Graph_Executable.rdf_graph FStar_Pervasives_Native.option=
  match t with
  | GT_Default -> FStar_Pervasives_Native.Some (s.gs_default)
  | GT_Named k -> lookup_named k s.gs_named
let gsp_head (t : gs_target) (s : graph_store) : Prims.bool=
  match t with
  | GT_Default -> Prims.uu___is_Cons s.gs_default
  | GT_Named k -> named_exists k s.gs_named
let gsp_put (t : gs_target) (g : RDF_Graph_Executable.rdf_graph)
  (s : graph_store) : (graph_store * Prims.bool)=
  match t with
  | GT_Default ->
      let did = Prims.uu___is_Cons s.gs_default in
      ({ gs_default = g; gs_named = (s.gs_named) }, did)
  | GT_Named k ->
      let did = named_exists k s.gs_named in
      ({
         gs_default = (s.gs_default);
         gs_named = (replace_named k g s.gs_named)
       }, did)
let gsp_post (t : gs_target) (g : RDF_Graph_Executable.rdf_graph)
  (s : graph_store) : (graph_store * Prims.bool)=
  match t with
  | GT_Default ->
      let did = Prims.uu___is_Cons s.gs_default in
      let merged = RDF_Graph_Executable.graph_union g s.gs_default in
      ({ gs_default = merged; gs_named = (s.gs_named) }, did)
  | GT_Named k ->
      let did = named_exists k s.gs_named in
      let prev =
        match lookup_named k s.gs_named with
        | FStar_Pervasives_Native.Some g0 -> g0
        | FStar_Pervasives_Native.None -> RDF_Graph_Executable.empty_graph in
      let merged = RDF_Graph_Executable.graph_union g prev in
      ({
         gs_default = (s.gs_default);
         gs_named = (replace_named k merged s.gs_named)
       }, did)
let gsp_delete (t : gs_target) (s : graph_store) :
  (graph_store * Prims.bool)=
  match t with
  | GT_Default ->
      let did = Prims.uu___is_Cons s.gs_default in
      ({
         gs_default = RDF_Graph_Executable.empty_graph;
         gs_named = (s.gs_named)
       }, did)
  | GT_Named k ->
      let did = named_exists k s.gs_named in
      ({ gs_default = (s.gs_default); gs_named = (remove_named k s.gs_named)
       }, did)
let status_put (did_replace : Prims.bool) : Prims.int=
  if did_replace then (Prims.of_int (204)) else (Prims.of_int (201))
let status_post (did_exist : Prims.bool) : Prims.int=
  if did_exist then (Prims.of_int (200)) else (Prims.of_int (201))
let status_delete (did_exist : Prims.bool) : Prims.int=
  if did_exist then (Prims.of_int (204)) else (Prims.of_int (404))
let status_get_named (found : Prims.bool) : Prims.int=
  if found then (Prims.of_int (200)) else (Prims.of_int (404))
let status_head_named (found : Prims.bool) : Prims.int=
  if found then (Prims.of_int (200)) else (Prims.of_int (404))
