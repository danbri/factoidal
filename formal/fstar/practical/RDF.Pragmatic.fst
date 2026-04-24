module RDF.Pragmatic

// Bucket: PRAGMATIC IMPLEMENTATION.
//
// This module sketches the executable representation boundary. It is where
// list-backed graphs, parser-oriented strings, extraction constraints, and
// storage/index choices belong. It should depend on the core spec, not define
// the core spec.

open RDF.CoreSpec

type graph_list = list triple
type byte_array = byte_string

let empty_graph_list : graph_list = []

let graph_of_list (g:graph_list) : graph =
  fun t -> FStar.List.Tot.mem t g

let data_item_from_bytes (bs:byte_array) (mt:option media_type) : data_item =
  {
    bytes = bs;
    media = mt;
    charset = None;
  }
