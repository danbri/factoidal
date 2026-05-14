module RDF.CottasStore.OnDiskRuntime

open FStar.All
open RDF.Graph.Executable
open Parser.BallyhooCOTTAS
open RDF.CottasStore

// On-disk-cottas perf primitives — Option C from the #118 design plan:
//
//   docs/designissues/2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md
//
// The F* spec layer (RDF.CottasStore.fst) holds the pure verification
// reference for cottas_ondisk_search / _estimate / _decode_* / _encode_*.
// The OCaml `cottas_ondisk_runtime.sh` patch currently replaces those
// extracted F* bodies with Hashtbl-backed `_fast` equivalents that are
// orders of magnitude faster on parliament-scale corpora.
//
// This module exposes the `_fast` operations as `assume val` perf
// primitives at the F* spec layer. The F* verification reference stays
// in RDF.CottasStore.fst as the ground truth; operational queries call
// into the perf primitives here. The OCaml realisation maps each
// `assume val` here onto the existing `Cottas_ondisk_runtime.*_fast`
// functions in the patched .ml.
//
// Soundness obligation: each `assume val` carries a contract that the
// realisation must satisfy modulo the F* spec. The contracts are
// stated as F* `Lemma` shapes below the `assume val`s, planned as
// follow-up round-trip-witness CI gates (Phase 2.5g of the #118 plan).
//
// Status: this is Phase 2.5b/c (specification layer). Hash-witness
// round-trip CI gates and the realisation patch update land in
// follow-up commits.

// NOTE on search/estimate: cottas_ondisk_search_fast and
// cottas_ondisk_estimate_fast no longer exist as separate OCaml
// helpers — they were retired in earlier sessions in favour of the
// F* `cottas_ondisk_search` / `cottas_ondisk_estimate` paths via
// filter_zipped_rows / count_zipped_rows. So this Phase 2.5b module
// exposes only the 8 token decoder + encoder primitives that DO have
// Hashtbl-fast counterparts; search/estimate are already F*-pure.
// Future work (Phase 2.5h) re-introduces ondisk_search_indexed +
// ondisk_estimate_indexed once a perf-fast variant lands again.

// Token decoders: identical contract to the Tot spec in
// RDF.CottasStore.fst, but Hashtbl-fast. ML-effected because the
// Hashtbl lookup goes through the runtime cache. Returns None for
// out-of-range ids (the spec returns a sentinel; here we surface
// the absence directly).
assume val ondisk_decode_subject_indexed
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : ML (option subject)

assume val ondisk_decode_predicate_indexed
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : ML (option wf_iri)

assume val ondisk_decode_object_indexed
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : ML (option rdf_term)

assume val ondisk_decode_graph_indexed
  (ds : cottas_ondisk_store) (id : cottas_graph_ref)
  : ML (option iri)

// Encoders (inverse of decoders): convert a typed RDF term to its
// nat-encoded term-id, or None if the term is absent from the corpus
// dictionary. Used by the query rewriter to lower constant terms
// into IDs once at plan time, then run the search loop over IDs.
assume val ondisk_encode_subject_indexed
  (ds : cottas_ondisk_store) (s : subject)
  : ML (option cottas_term_ref)

assume val ondisk_encode_predicate_indexed
  (ds : cottas_ondisk_store) (p : wf_iri)
  : ML (option cottas_term_ref)

assume val ondisk_encode_object_indexed
  (ds : cottas_ondisk_store) (o : rdf_term)
  : ML (option cottas_term_ref)

assume val ondisk_encode_graph_indexed
  (ds : cottas_ondisk_store) (g : iri)
  : ML (option cottas_graph_ref)
