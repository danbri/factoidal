# RDF 1.2 Compatibility

> **SUPERSEDED (2026-07-16 un-park; do not act on the hold-the-line policy
> below).** This file set out a "keep 1.1 as the normative target, only
> collect 1.2 examples" stance from before RDF 1.2 / SPARQL 1.2 was
> un-parked. That stance is reversed: 1.2 is now an implemented target.
> The term model (`RDF.Term.T_TripleTerm`, `text_direction`,
> `rdf:dirLangString`) and all four text/line syntaxes (N-Triples,
> N-Quads, Turtle, TriG) landed and verified — **RDF 1.2 syntax/eval 212
> pass, 0 fail; SPARQL 1.2 248 pass, 6 fail (out of 254)**. The
> `rdf_syntax_mode = Mode_11 | Mode_12` parameter (Mode_11 default, so 1.1
> output is byte-identical) is the real compatibility mechanism — not the
> "collect-only" approach here. Live scoreboard:
> [`../claude-rules/w3c-completeness-ledger.md`](../claude-rules/w3c-completeness-ledger.md);
> design record:
> [`2026-07-16-rdf12-sparql12-impact-strategy.md`](2026-07-16-rdf12-sparql12-impact-strategy.md).
> Still open: RDF/XML 1.2, c14n-1.2 + entailment suites, and browser/npm-API
> + dashboard exposure (JS `parse`/`query` still default to Mode_11). The
> original text is kept below for provenance only.

---

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
