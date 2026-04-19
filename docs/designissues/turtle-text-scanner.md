# Turtle Text Scanner Architecture

> **Status note (2026-04-19):** steps 1–3 are partially done; steps 4 and 5
> are not started. The measured rate is still ~50–240 triples/s — scanner
> integration alone bought ~2–4×, not an order of magnitude. See the
> structural plan in
> [`2026-04-19-turtle-parser-speed.md`](2026-04-19-turtle-parser-speed.md).

## Priorities

The Turtle parsing architecture should optimize for:

1. speed
2. streaming
3. reliability
4. reasonable performance on non-western content

ASCII-heavy RDF can be faster than non-ASCII RDF, but non-ASCII content must
remain linear and predictable. Shared infrastructure across parsers is only a
goal when it does not harm deployability or hot-path performance.

## Problem

The current Turtle parser mixes:

- grammar decisions
- semantic actions
- character classification
- raw text scanning

in the same mutually recursive functions.

This is visible in:

- `parse_turtle_iri`
- `parse_prefixed_name`
- `parse_turtle_object`
- `parse_predicate_object_list_rev`

The result is that the textual hot path is not an explicit architectural
surface. That makes it difficult to reason about streaming, ASCII fast paths,
Unicode fallback behavior, and extraction costs in F*.

## Architectural Decision

Introduce a dedicated F* scanner layer for Turtle terminals.

The scanner layer should:

- operate on `string` plus offsets
- use ASCII-fast classification on the common path
- fall back cleanly for non-ASCII characters
- define explicit continuation state for chunked/streaming operation
- return spans or token-shaped results suitable for the grammar layer

The Turtle grammar layer should then consume scanner results rather than
re-deriving terminal structure directly from raw text.

## Non-Goals

- do not start with an OCaml-only prototype
- do not build a generic parser-combinator framework as the hot path
- do not force all RDF parsers to share the same scanner unless that later
  proves performance-neutral

## Initial F* Scope

The first step is a new `Parser.TurtleScanner` F* module that provides:

- scanner state types for streaming
- ASCII classification helpers
- offset/span-based terminal scanners for:
  - whitespace/comments
  - prefixed names
  - IRI references
  - punctuation

The existing `Parser.Turtle` module is not rewritten in the first change.
Instead, the new scanner module is added to the F* extraction/build pipeline so
that future parser refactoring can proceed inside the verified route.

## Expected Refactoring Path

1. add `Parser.TurtleScanner`
2. move hot textual recognizers out of `Parser.Turtle`
3. replace direct raw-text scanning in `Parser.Turtle` with scanner calls
4. add chunk-resumable scanning for string/IRI/comment contexts
5. revisit document-level parsing once scanner boundaries are stable
