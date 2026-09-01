# Persisted SPARQL language-tag index safety

Date: 2026-09-01

## Finding

The first TLI1/OLI2 object route uses an exact serialized RDF-term key.  This
is a valid physical lookup for IRIs and for literals whose SPARQL identity is
byte-exact, but it is not complete for every `Term.eqb`-equivalence class.
In particular, SPARQL matches language tags case-insensitively, while the
first TLI1 layout orders and searches their serialized spellings exactly.

The approved W3C `expr-builtin/q-lang-3.rq` makes the difference observable:
the query asks for `"string"@EN`; `data-builtin-2.ttl` contains the matching
`"string"@en` value on `http://example/x3`.  The W3C result has one binding.
Before this guard, OLI2/TLI1 treated the exact key as absent and incorrectly
returned zero rows.

## Safe current behaviour

`Harness/IndexedBlockV3Query.lean` now admits the object-selective physical
route only when its term is safe for exact-key lookup:

- IRI objects remain OLI2/TLI1 selective.
- Literals with neither a language tag nor `rdf:XMLLiteral` remain selective.
- Language-tagged and `rdf:XMLLiteral` objects use the ordinary
  constant-predicate materialisation route, whose evaluator applies the
  existing SPARQL `Term.eqb` relation.

This is deliberately a completeness guard, not a claim that language-tagged
literals are unsupported.  It preserves correct results while avoiding a
false-negative index lookup.

`tools/blockengine-ibk3-w3c-disk-query-smoke.sh` includes the W3C case and
asserts one row for `http://example/x3` through persisted SBM6 artifacts.

## Follow-up design

A later index revision can recover selectivity by making its lookup key a
canonical representative of the SPARQL matching class (the existing
`Term.joinKey` defines that representative), while preserving all local IDs
which share the key.  That requires a multi-ID TLI posting representation or
an ingestion-level canonicalization rule with explicit proof and compatibility
policy.  It must not silently replace the present exact one-key/one-ID TLI1
assumption.

## Expression equality correction

The same W3C material also exercised a separate semantic seam: the SPARQL
`=` implementation compared literal language-tag fields structurally.  On
the W3C `lang-case-sensitivity` graph that made `@en = @EN` false, returning
two equal pairs instead of the approved four (and two unequal pairs instead
of none).  `Expr.valueCompare` now uses the existing RDF
`langTagOptionEq` relation for equal-datatype literals.  `sameTerm` remains
the separate strict-spelling operation.

`L4Factoidal/SPARQL/ExprTests.lean` has compile-time guards for `=` and `!=`;
the disk smoke packs the W3C graph and checks the four-row and zero-row
results through the persisted query path.  This is a Lean SPARQL semantic fix,
not merely a storage workaround.

## Rejected temporary index shortcut

On a freshly packed 65,475-triple `protein_family.ttl` SBM6 generation, the
object-driven `wdt:P31/wdt:P527` join returns 20,844 rows.  The current
materialise-then-read-ops evaluator took about 28 seconds in one local process
sample.  Replacing the base-only temporary read backend with the existing
Lean `OWL.RL.Index` reduced that sample to about 13 seconds, but it made the
persisted W3C `q-lang-3` case return zero rows again: the generic index also
uses an exact candidate key before the `Term.eqb` recheck.

That shortcut was rejected and removed.  The observation is still useful:
the next performance step is not an arbitrary cache, but an
equivalence-aware backend index whose candidate selection is complete for the
same language-tag and XMLLiteral relation as the SPARQL evaluator.  The
observed times are exploratory warm-cache local samples, not benchmark claims.
