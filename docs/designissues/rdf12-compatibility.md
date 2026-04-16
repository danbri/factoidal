# RDF 1.2 Compatibility

Factoidal should keep RDF/SPARQL 1.1 as the current normative target while
beginning to collect RDF 1.2-era examples and compatibility questions.

Why:

- RDF 1.2 examples are already appearing in documentation and discussion
- silently accepting new syntax without a policy is risky
- silently rejecting everything newer is also risky from a usability point of
  view

Current working approach:

1. Keep the main parser/engine target aligned with RDF/SPARQL 1.1.
2. Collect RDF 1.2 examples under `tests/compat/rdf12/`.
3. Classify each example as one of:
   - `1.1-compatible`
   - `recognized-not-supported`
   - `intentionally-rejected-in-1.1-mode`
4. Only promote behavior into the main supported path once syntax and semantics
   are both understood.

This keeps compatibility work visible without letting the project drift into an
accidental half-implemented RDF 1.2 mode.
