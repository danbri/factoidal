module RDF.IRI

// RFC 3986/3987 IRI reference-resolution -- the tree's THIRD .fsti
// (after RDF.Vocabulary.fsti, RDF.Indexed.fsti). Unlike those two
// (transparent-by-design data/combinator modules), this one is a real
// abstraction boundary: nothing outside this module inspects
// `iri_parts` or calls `parse_iri`/`remove_dot_segments`/
// `merge_paths`/`transform_references`/`recompose` directly (confirmed
// by grep across the tree, 2026-07-05) -- only the resolution entry
// points below are consumed by callers (RDF parsers -- Turtle,
// RDFXML, ShEx `@base` handling -- via `resolve_iri_v2`; SPARQL /
// JSON-LD via the `wf_iri`-typed `resolve_iri`/`resolve_query_iri`).
// Hiding the byte-scanning machinery behind `val` (not transparent
// `let`) keeps this the one-screen surface the design doc asks for.
//
// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// section 2.7 / section 3.3 step 1: consolidates what were two
// independent RFC 3986 implementations (`Parser.IRI.fst`'s
// `resolve_iri_v2` and `SPARQL11.IRI.Resolve.fst`'s `jir_*`-based
// `resolve_iri`) into one. A differential harness (75 cases: the full
// RFC 3986 section 5.4 battery, the toRdf/0122-0125 dotted-base pins
// from tests/unit/iri_resolve_unit.ml, and 18 extra probes covering
// userinfo/port/IPv6 authorities, urn:/mailto:/file: schemes, unicode
// path segments, and malformed bases) found the two core algorithms
// byte-identical on every case; the only observed divergence was the
// `wf_iri`-typed entry point's defensive `is_iri` fallback-to-base
// guard for malformed/non-absolute bases, which `resolve_iri` below
// reproduces on top of the shared `resolve_iri_v2` core rather than
// duplicating the merge/dot-segment logic a second time (re-verified:
// the synthesized wrapper matched the original jir_*-based
// `resolve_iri` on all 75 differential cases, including the 3 where
// the two originals disagreed). See the design doc's step-1 row for
// the full investigation writeup.
//
// `Parser.IRI.fst` and `SPARQL11.IRI.Resolve.fst` remain as thin
// re-export shims at their old module paths so all existing
// dependents (`Parser.Turtle.fst`, `Parser.RDFXML.fst`,
// `ShEx.Schema.fst`, `SPARQL11.Algebra.fst`, `JSONLD.Context.fst`, plus
// their hand-written/extracted OCaml counterparts) compile and link
// unchanged.

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
