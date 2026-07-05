module SPARQL11.IRI.Resolve

// Thin re-export shim. This module used to carry its own independent
// RFC 3986 section 5.2 implementation (`jir_*`-prefixed helpers +
// `resolve_iri`/`resolve_query_iri`), deliberately duplicated from
// `Parser.IRI.fst` to stay dependency-free of `SPARQL11.Algebra.fst`
// (see this file's pre-2026-07-05 banner for the history: factored out
// of `SPARQL11.Algebra.fst` for #200/#65, then rewritten for #JSON-LD
// Phase 5 to fix a heuristic resolver's RFC 3986 gaps).
//
// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// section 2.7 / section 3.3 step 1, that duplication is now retired:
// `resolve_iri`/`resolve_query_iri` moved to `RDF.IRI.fst`, built on
// top of the SAME `resolve_iri_v2` core `Parser.IRI.fst` used to carry
// separately (see `RDF.IRI.fsti`'s banner for the differential-testing
// evidence that this is behavior-preserving). This module's own
// `list_is_prefix`/`list_contains_sublist`/`string_contains` helpers
// were dead code even before this change (defined, never called by
// this file's own `resolve_iri`/`resolve_query_iri`/`string_to_iri`,
// and grep across the tree found no external qualified reference to
// `SPARQL11.IRI.Resolve.string_contains` et al. -- other modules that
// use those names, e.g. `SPARQL11.Algebra.fst`, define their own local
// copies) and are not re-exported here.
//
// `resolve_iri` and `resolve_query_iri` are this module's only
// symbols with real dependents (`SPARQL11.Algebra.fst`,
// `JSONLD.Context.fst`, and the `tests/unit/iri_resolve_unit.ml` unit
// pins) and are re-exported below, byte-identical to the
// pre-consolidation behavior.

open RDF.Graph.Executable
open RDF.IRI

let resolve_iri (base : wf_iri) (relative : string) : wf_iri =
  RDF.IRI.resolve_iri base relative

let resolve_query_iri (base : option wf_iri) (rel : string) : option wf_iri =
  RDF.IRI.resolve_query_iri base rel
