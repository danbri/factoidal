# 2026-09-20: triple provenance for the Turtle parser

Landed `L4Factoidal/Syntax/TurtleProvenance.lean` and its tests. Every
triple the Turtle reference parser emits can now be paired with the
statement it came from (ordinal, character span) and its position within
that statement, and the pairs can be materialised as RDF 1.2 reifiers.

Two theorems tie it to the reference parser: forgetting the span gives
back `parseStatementsFold`, and projecting the provenance away from
`parseTurtleProv` gives back `parseTurtle`. No new `partial def`, no new
axioms beyond the standard three.

Design and the not-done list: `designissues/2026-09-20-triple-provenance.md`.
