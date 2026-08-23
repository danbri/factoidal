# Grammar-driven RDF test generation, W3C 1998

Retrieved 2026-08-23 from <https://www.w3.org/RDF/Test/Janne/>.
Author: Janne Saarela (jsaarela@w3.org). Page maintained by Dan
Brickley. Copyright notice in `runtests.pl`:
`(C)opyright 1998 Janne Saarela/World Wide Web Consortium`.

## Files

| File | Size | What it is |
|---|---|---|
| `rdf.pl` | 6854 B | The RDF 1.0 M&S XML grammar as Prolog clauses. |
| `rdf-test.pl` | 331 B | Perl. Splits the generator's output stream into one file per document. |
| `runtests.pl` | 613 B | Perl. Runs SiRPAC over each generated file and checks the output. |
| `error.rdf` | 1628 B | One document with several deliberate violations. |

The 534 generated `.rdf` files the page describes are no longer
retrievable; `https://www.w3.org/RDF/Test/Janne/1.rdf` answers 404.
The generator is here, so the corpus can be regenerated.

## How it works

`rdf.pl` transcribes the M&S productions as clauses — `description`,
`container`, `propertyElt`, `idAboutAttr`, `propAttr` and so on. The
driver is one line:

```prolog
g(B) :- rdf(A), flatten(A, B), format("~s", [B]), fail.
```

The trailing `fail` forces Prolog to backtrack through every
derivation, printing each one. That is the whole enumeration engine.

## Why it is here

Not to be run. It is the reference point for
`formal/lean4/L4Factoidal/Testing/Enumerate.lean`, which does the
same thing against a Lean inductive type, and it records two
constraints that turned out to be intrinsic rather than incidental.

**The two HACK comments in `rdf.pl`.** `bagIdAttr` is pinned to the
constant `bagID1` instead of enumerating `idsymbol`, and the
`parseResource` productions are commented out. Both are marked HACK.
They are there because unrestricted enumeration of a recursive
grammar does not terminate. The Lean version hit the same wall from
the other side — a total, depth-bounded enumeration whose count is
doubly exponential (2,470,586 nodes at depth 2; past 10¹³ at depth 3)
— and needed a cap for the same reason.

**The oracle in `runtests.pl`.** It runs SiRPAC, greps the output for
`null` and `Error`, and checks the file is non-empty. It separates a
crash from a non-crash. It cannot separate correct triples from
incorrect ones. That is the part a specification written as an
executable type improves on: the Lean version checks
`parseXML ∘ serialize = id`, which does distinguish them.

## Licence

W3C document, 1998. See <https://www.w3.org/Consortium/Legal/copyright-software>
for the W3C Software Notice and Licence of that era. Retained here as
a citation and a historical reference, unmodified.
