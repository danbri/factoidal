module Parser.IRI

// Thin re-export shim. The real RFC 3986 section 5.2 implementation
// (`parse_iri`, `remove_dot_segments`, `merge_paths`,
// `transform_references`, `recompose`, `resolve_iri_v2`) moved to
// `RDF.IRI.fst` on 2026-07-05, per
// docs/designissues/2026-07-05-foundational-core-refactor.md section
// 2.7 / section 3.3 step 1 (consolidating this module and
// `SPARQL11.IRI.Resolve.fst`'s independent RFC 3986 implementations
// into one). `resolve_iri_v2` is the only symbol this module's
// dependents (`Parser.Turtle.fst`, `Parser.RDFXML.fst`,
// `ShEx.Schema.fst`) actually reference (confirmed by grep across the
// tree before this shim was written); it is re-exported here
// byte-identical to the pre-consolidation behavior so those
// dependents compile and run unchanged.
open RDF.IRI

let resolve_iri_v2 (base: string) (ref_: string) : string =
  RDF.IRI.resolve_iri_v2 base ref_
