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

## Equivalence-aware indexed backend (landed)

The required correction is now in the common Lean indexed backend rather than
as a query-command exception.  `RDF/StoreCapabilities.lean` exposes
`exactObjectIndexKeySafe`: exact object and predicate-object hash buckets are
used for IRIs, blank nodes and byte-exact literals, while language-tagged,
`rdf:XMLLiteral`, and RDF-star triple-term objects widen to a predicate bucket
or full graph before the ordinary `Term.eqb` filter.  A build-time guard keeps
both `"xyz"@en` and `"xyz"@EN` in the candidate set.

The base-only persisted reader can consequently build this Lean index over its
already materialised exact rows.  Delta overlays remain on the existing
read-ops backend until their indexed materialisation contract is separately
defined.  Both persisted smoke suites, including the W3C language cases,
pass.  Re-running the protein-family 20,844-row object-driven join produced
the same result in about 13.1 seconds in one warm-cache local sample.  This
removes the immediate quadratic rescan, though it is still far from the final
on-disk join architecture and is not presented as a general benchmark.

`tools/blockengine-sbm6-protein-family-benchmark.sh` makes this workload
repeatable against an activated store.  Its first fresh-process local sample
after the indexed-backend correction recorded 12.93 s wall time and 70.6 MiB
peak resident memory for the 20,844-row result.  The script emits JSON and
does not claim to clear the operating-system file cache.

### Contiguous selected-row reads

The SRI2/OLI2 row reader now coalesces adjacent fixed-width row offsets into
one Merkle-verified range and rechecks every decoded row against its sidecar
key.  This removes the avoidable one-I/O-call-per-row shape without weakening
the sidecar admission relation; the implementation is total, with explicit
posting-length fuel.

The persistent and W3C disk gates pass after this change.  It did not
materially reduce the broad protein-family join's first follow-up sample
(13.29 s): its single 44,631-row OLI2 scan completes in about 0.5 s, while
the two-pattern join spends its remaining time in generic Lean join/result
evaluation.  This directs the next optimisation toward a direct physical join
result path or a more efficient binding representation, not unsafe I/O claims.

### Direct OLI2-to-SRI2 SELECT bindings

That direct path is now implemented for the deliberately narrow existing
admission: two default-graph BGP triples sharing a subject variable; one has
a constant IRI predicate plus a safe constant IRI/literal object; the other
has a different constant predicate and a distinct object variable; no delta
or post-`VALUES`.  After OLI2 selects the driver and SRI2 selects its target
subjects, the reader constructs binding rows directly, preserving driver
multiplicity through a subject-count hash map, then passes them to the normal
Lean `selectPost` pipeline.  Thus projection, expressions, aggregation,
ordering, DISTINCT and slicing retain their established implementation.

The former `List.eraseDups` over a broad driver was quadratic.  Replacing it
with a first-seen `Std.HashSet Subject` accumulator reduced the checked
protein-family benchmark (65,475 triples, 20,844 result rows) to 3.79 s and
about 70.9 MiB peak RSS in a fresh local process.  The ordinary and reversed
BGP textual order both return 20,844 rows through
`ibk3-sri2-tli1-oli2-object-subject-direct-select`; persistent and W3C disk
smokes pass.  This is a concrete physical-plan specialisation, not a claim
that arbitrary joins bypass the general evaluator.

### Runtime ORDER BY without weakening DISTINCT proofs

The direct physical path still deliberately hands result rows to the ordinary
SPARQL post-processing pipeline.  That exposed an all-purpose runtime
bottleneck: `sortSolutions` is a small stable insertion sort, so an
`ORDER BY` over tens of thousands of rows is quadratic even when a following
`LIMIT` emits only a few rows.  Its simple definition is retained because
`QueryTheorems.lean` proves its permutation property and uses it in existing
proof exercises.

`Query.lean` now uses `List.mergeSort` through `sortSolutionsFast` at runtime
while retaining `sortSolutions` unchanged for those proofs.  The comparator
uses the same non-strict ordering convention; SPARQL does not prescribe the
relative order of equal sort keys.  `distinctSolutions` was explicitly left
unchanged: it remains the theorem-backed solution-mapping equivalence
implementation rather than an unproved hash shortcut.

On the activated 65,475-triple protein-family store, the previously
pathological query

```sparql
SELECT DISTINCT ?x {
  ?x wdt:P31 wd:Q417841 .
  ?x wdt:P527 ?part .
}
ORDER BY ?x LIMIT 3
```

now returns the ordered three-row result through the direct OLI2/SRI2 path in
an 8.2-second local process sample; the prior insertion-sort version did not
finish within a 30-second observation window.  The increment was checked with
`lake build L4Factoidal.SPARQL.QueryTheorems l4block-id-v3-query`,
`tools/blockengine-ibk3-persistent-smoke.sh`, and
`tools/blockengine-ibk3-w3c-disk-query-smoke.sh`.  This validates behavior but
does not yet prove `sortSolutionsFast`'s permutation/order properties; that
is the explicit remaining assurance gap before treating it as a fully proved
replacement for the retained specification sort.
