module RDF.IRI

// RFC 3986/3987 IRI reference-resolution -- the tree's THIRD .fsti
// (after RDF.Vocabulary.fsti, RDF.Indexed.fsti), and unlike those two
// a real abstraction boundary: nothing outside this module inspects
// `iri_parts` or the byte-scanning helpers directly (confirmed by grep,
// 2026-07-05) -- only the resolution entry points below are consumed.
// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// section 2.7 / section 3.3 step 1. Full consolidation history +
// differential-testing evidence in RDF.IRI.fst's banner.

open RDF.Graph.Executable

/// RFC 3986 section 5.2 "Transform References", byte-level, over
/// plain strings. Total: never fails, always returns *some* string
/// (the concatenated result of the RFC 3986 section 5.2.2/5.2.3/
/// 5.2.4/5.3 algorithm), even when `base`/`ref_` are not well-formed
/// IRIs. This is the contract RDF parsers rely on: they call this
/// before any `wf_iri` check exists for the resolved value (e.g.
/// resolving a Turtle `@base` before the base itself has been
/// validated as absolute).
val resolve_iri_v2 (base: string) (ref_: string) : string

/// RFC 3986 resolution for the `wf_iri`-typed callers (SPARQL
/// query-IRI resolution, JSON-LD context `@base` processing). Built on
/// `resolve_iri_v2`; if the transformed-and-recomposed result does not
/// itself parse as an (RDF-sense) IRI, falls back to returning `base`
/// unchanged -- the same defensive contract `SPARQL11.IRI.Resolve.
/// resolve_iri` had before this consolidation.
val resolve_iri (base: wf_iri) (relative: string) : wf_iri

/// Resolve `rel` against an optional base (SPARQL prefixed-name /
/// query-IRI resolution): `Some b` resolves against `b`; `None`
/// returns `rel` itself if it is already a well-formed IRI, else
/// `None`.
val resolve_query_iri (base: option wf_iri) (rel: string) : option wf_iri
