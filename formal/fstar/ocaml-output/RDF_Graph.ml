open Prims
type rdf_graph = RDF_Triple.triple Prims.list
let empty_graph : rdf_graph= []
type named_graph = {
  ng_name: RDF_Term.iri ;
  ng_graph: rdf_graph }
let __proj__Mknamed_graph__item__ng_name (projectee : named_graph) :
  RDF_Term.iri= match projectee with | { ng_name; ng_graph;_} -> ng_name
let __proj__Mknamed_graph__item__ng_graph (projectee : named_graph) :
  rdf_graph= match projectee with | { ng_name; ng_graph;_} -> ng_graph
type rdf_dataset = {
  ds_default: rdf_graph ;
  ds_named: named_graph Prims.list }
let __proj__Mkrdf_dataset__item__ds_default (projectee : rdf_dataset) :
  rdf_graph= match projectee with | { ds_default; ds_named;_} -> ds_default
let __proj__Mkrdf_dataset__item__ds_named (projectee : rdf_dataset) :
  named_graph Prims.list=
  match projectee with | { ds_default; ds_named;_} -> ds_named
let empty_dataset : rdf_dataset= { ds_default = empty_graph; ds_named = [] }
let rec lookup_named_graph (name : RDF_Term.iri)
  (named : named_graph Prims.list) :
  rdf_graph FStar_Pervasives_Native.option=
  match named with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.ng_name = name
      then FStar_Pervasives_Native.Some (ng.ng_graph)
      else lookup_named_graph name rest
