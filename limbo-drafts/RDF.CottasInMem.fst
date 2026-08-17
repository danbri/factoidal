module RDF.CottasInMem

// In-memory COTTAS encoder — Phase A skeleton.
//
// Companion to RDF.CottasStore: produces a cottas_ondisk_store backed
// by an in-RAM Bytes.t buffer instead of an mmap'd file. Same F*-side
// search / estimate / decode path; only the byte source differs.
//
// Design note: docs/designissues/in-memory-cottas-encoder.md
// Branch: claude/inmem-cottas-phase-a (Phase A scaffold)
//
// PHASE A (this skeleton):
//   - declares cottas_inmem_open as assume val with rdf_graph input.
//   - returns option cottas_ondisk_store; F*-side type unchanged.
//   - identifier convention: the OCaml glue maps graph_id -> in-RAM
//     Bytes.t via a process-wide registry. The cods_artifact_path
//     string carries the graph_id (e.g. "inmem://lifesci-Q01") so
//     existing path-keyed side tables (Phase 2.7-mini token lookup
//     hashtbls in Cottas_ondisk_runtime) continue to work.
//
// PHASE A.5 (follow-up, NOT in this scaffold):
//   - actual byte-layout encoder in OCaml glue.
//   - wiring into factoidal_cli.ml so --inmem-cottas chooses this path
//     instead of indexed_graph_backend for Turtle-loaded data.
//   - rebench Q01 on lifesci demo.
//
// PHASE B / C (future):
//   - presence bitmaps for predicate-bound queries.
//   - compound (p,o) bitmap for joined queries.
//
// Rule #1 (F*-first): this module declares the public API in F*. The
// encoder body is pure I/O glue (rule #11 allowed: produces bytes,
// doesn't reinterpret them). All search / estimate / decode logic
// remains in RDF.CottasStore.fst, unchanged.

open RDF.Graph.Executable
open RDF.CottasStore

// Open an in-memory COTTAS store from an rdf_graph. The graph_id is
// an opaque caller-chosen tag used as the cods_artifact_path of the
// returned store; it must be unique within the process so that
// path-keyed side tables (token lookup hashtbls) don't collide with
// real on-disk handles.
//
// Phase A: the OCaml glue's body returns None (skeleton only). Once
// Phase A.5 lands, it will encode the graph to a Bytes.t, register
// the buffer under graph_id, and build a cottas_ondisk_store whose
// search path consults the in-RAM bytes. No semantic logic in the
// glue: the encoder just lays out the bytes the F* reader already
// knows how to parse.
assume val cottas_inmem_open :
  graph_id:string -> g:rdf_graph -> Tot (option cottas_ondisk_store)
