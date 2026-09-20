# 2026-09-20: triple provenance for the Turtle parser

Landed `L4Factoidal/Syntax/TurtleProvenance.lean` and its tests. Every
triple the Turtle reference parser emits can now be paired with the
statement it came from (ordinal, character span) and its position within
that statement. The pairs materialise either as a dataset with one named
graph per triple (`<graphBase><n>`, provenance facts in the default
graph, N-Quads out through `Dataset.toNQuads`), which is the primary
form after the owner's steer of 2026-09-20, or as RDF 1.2 reifiers.

Theorems tie it to the reference parser: forgetting the span gives
back `parseStatementsFold`, and projecting the provenance away from
`parseTurtleProv` gives back `parseTurtle`, and concatenating the
dataset's named graphs gives back the parse. No new `partial def`, no new
axioms beyond the standard three.

Design and the not-done list: `designissues/2026-09-20-triple-provenance.md`.
