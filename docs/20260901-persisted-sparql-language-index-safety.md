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

### Direct DISTINCT subject projection

The same protein-family query still spent most of its time in the generic
`distinctSolutions` scan: although it emitted only three rows after `LIMIT`,
it first compared the 20,844 projected rows quadratically.  The physical
OLI2-to-SRI2 route now recognizes exactly one extra finishing shape:

```sparql
SELECT DISTINCT ?subject { ... } ORDER BY ?subject
```

or its descending form, with `?subject` the join subject and the sole selected
variable.  Its target rows already establish the set of admissible RDF
subjects.  It constructs one binding per structural `Subject`, disables only
the redundant generic DISTINCT flag on a reconstructed query, and still calls
the normal `selectPost` for ordering and slicing.  Any grouping, HAVING,
expression projection, another ordering expression, unprojected selected
variable, delta, or other physical-plan shape falls back unchanged.

The same activated protein-family query now completes in a 4.05-second local
process sample (from 8.2 seconds after the general ORDER BY improvement) and
returns the same ordered three IRIs.  The persistent smoke has explicit ASC
and DESC checks for this mode.  This is an executable, tightly stated
physical equivalence whose assumptions are regression-tested; a standalone
Lean refinement theorem for the finite subject-set transformation remains a
future assurance item.

### General runtime DISTINCT buckets

The generic `distinctSolutions` specification remains unchanged and retains
its existing theorems.  Runtime SELECT evaluation now uses
`distinctSolutionsFast`: process rows from right to left (preserving the
specification's last-occurrence result order), bucket each solution mapping by
one fixed-universe optional-`Term.joinKey` representation, and test every
bucket candidate with the established `Binding.equiv` before suppressing a
row.

`Term.joinKey_eq_of_eqb` is the key safety direction: SPARQL-equal terms,
including case variants of language tags and canonical XML literals, enter the
same candidate bucket.  A hash/key collision only costs an extra equivalence
test; it cannot remove a non-equivalent mapping.  The associated standalone
refinement theorem is now complete (see the later exact-refinement entry), and
the generic path passes both persisted and W3C disk-query suites.  Before the
fixed-universe refactor, a two-column 20,844-row protein-family
`SELECT DISTINCT ?x ?part ... ORDER BY ?x LIMIT 3`, which cannot use the
single-subject fast path, completed in a 4.00-second local sample.

The proof-oriented refactor keeps the tail-recursive
`distinctSolutionsFastGo` public and introduces `Binding.distinctKeyFor` over
a fixed variable universe.  `distinctSolutions` remains the independent
reference.  The completed theorem establishes exact list equality before
`DISTINCT` feeds ordering, slicing, or result serialization; downstream
semantics were not weakened to accommodate the optimization.

## Compaction continuity check

The current compactor is not an IBK2-only fallback: its IBK3 branch calls
`publishTriplesV3` with the compacted SBM6 `SRI2/TLI1/OLI2` layout, and
activation admits that layout.  On 2026-09-01 both
`tools/blockengine-shard-compact-smoke.sh` and
`tools/blockengine-ibk3-compact-smoke.sh` passed.  The IBK3 gate repacks a
generation after DLOG batches, activates it through `CURRENT`, queries the
new base, writes an epoch-2 DLOG update, and reads that update as
base-plus-delta.  Thus selective layout continuity and epoch-aware replay are
currently exercised across the immutable-generation transition.

## Decoder traversal repairs

Two shared full-artifact decoders no longer repeatedly convert their remaining
input to a list and `drop` page-sized prefixes.  SRI2/OLI2
`decodeAllPages` (commit `1d6cf5654`) and PTD1 `decodePagesGo` (commit
`863e2008a`) now carry a `ByteArray` plus an explicit offset, extracting and
validating each declared page once.  Their page-level term/pair decoders,
wire bytes, checksum rules, page-directory checks, and selective range-reader
contracts are unchanged.  Both changes passed the persisted SBM6 and W3C
disk-query gates.  IBK3 fixed-width row decoding was already offset-based;
its remaining list use is limited to small header/CRC framing.

## Merkle range-granularity observation

On the activated 889k-triple gene store, a five-row constant-predicate query
selected one IBK3 predicate artifact and reported 12,214 logical bytes versus
131,072 fetched bytes.  Publishing currently commits all primary and sidecar
artifacts in 65,536-byte Merkle chunks, so the reader correctly authenticated
two complete chunks.  This is not a read-buffer regression.  A later layout
experiment may compare a smaller chunk policy for small/selective artifacts
against the additional Merkle metadata and verification work; the policy must
remain an artifact-level declared/committed property, shared by file, PG,
TiKV, and WASM hosts.

## Three-way shared-subject physical plan

`IndexedBlockV3Query` now recognizes a deliberately narrow three-triple BGP:
one shared subject variable, three distinct constant IRI predicates, variable
objects, default graph, and no delta overlay.  It chooses the smallest
predicate artifact as driver, derives its subjects, SRI2-scans both remaining
predicate artifacts for exactly those subjects, then passes the three exact
fragments to the ordinary parsed SPARQL evaluator.  Missing artifacts safely
fall back to generic evaluation.  On the activated gene store, a P1057/P684/
P688 query selected `ibk3-sri2-tli1-subject-triple-join(3)` and returned five
rows.  The persisted and W3C disk-query suites pass after the addition.

On the same activated gene store, a fresh-process P1057/P684/P688 three-way
query with `LIMIT 5` took 8.71 seconds, reporting 27,165,589 logical bytes
and 29,927,832 fetched Merkle-chunk bytes.  This is a baseline, not a general
claim: the plan has eliminated unrelated predicates, but still materialises
the three exact fragments and lets the normal evaluator construct the join
result.  A later direct binding/result path must preserve that evaluator's
projection, filters, aggregation, ordering, DISTINCT, and slice semantics.

### Direct three-way SELECT bindings

The next increment supplies a direct result path for a still narrower,
auditable case: a **modifier-free** `SELECT` over exactly the admitted
three-triple BGP, where the shared subject and all three object variables are
distinct.  After the same smallest-driver and SRI2 selection work, it groups
each of the two target fragments by structural RDF `Subject` and emits the
Cartesian product of their values with every driver row.  This is the BGP's
ordinary bag semantics, rather than a set-oriented shortcut.  The result
sequence goes through the established `selectPost` only for ordinary
projection/expressions.

The persisted smoke fixture now has a subject with two `name` and two
`member` values.  Its three-pattern query returns six mappings (the original
two plus the four-value Cartesian product) through
`ibk3-sri2-tli1-subject-triple-direct-select(3)`.  A redundant `FILTER(?x =
?x)` forces the general persisted evaluator and returns the same six mappings.
The gate additionally establishes that `ORDER BY` falls back to the ordinary
three-way evaluator rather than exposing the physical driver's incidental
row order.

That restriction is deliberate.  The physical path chooses the smallest
predicate artifact as driver, whereas the reference evaluator follows BGP
source order.  The two are bag-equivalent but need not have the same list
order.  `ORDER BY` tie order, `DISTINCT`'s retained occurrence, grouping,
`OFFSET`, and `LIMIT` can observe list order in the present executable
model, so all such forms stay on the established evaluator.  The earlier
889k-gene `LIMIT 5` result consequently remains the 8.71-second generic
three-way baseline, not a direct-path benchmark.  A future pure Lean
refinement module should first prove bag equivalence under the exact
admission predicate, then add explicitly justified modifier refinements.

`L4Factoidal/SPARQL/SharedSubjectTripleRefinement.lean` now provides that
proof boundary without coupling it to the harness.  It defines pure
predicate-fragment and same-subject-object sequences, a canonical BGP-order
binding construction, and `BagEquivalent` in terms of `AlgebraSpec.mult`.
The pure semantic bridge is now proved without `sorry`: when the syntactically
first predicate supplies the driver rows and the four variables are pairwise
distinct, `sharedSubjectTripleSolutions_eq_evalBgp` establishes exact list
equality with the ordinary left-to-right evaluator.  Its bag-equivalence
corollary is therefore immediate.  The proof retains every duplicate and each
multi-value Cartesian product.  It is stronger than the originally sketched
claim and does not require the three predicates to be distinct; that is a
physical planner admission, not a semantic precondition.

The executable HashMap grouping obligation is now closed.  The production
finisher lives in `SharedSubjectTriple.lean`, rather than as private harness
code.  `objectsBySubject_getD` proves that each HashMap bucket is exactly the
source object sequence in reverse order, with no lost or duplicated
occurrence.  `subjectTripleSolutions_bag_refines_sharedSubjectTripleSolutions`
then proves that reversing the two buckets changes enumeration order only:
the production Cartesian finisher and the simple List reference have the same
solution multiplicities for every mapping.

Two physical obligations remain separate: prove that the Merkle-verified
SRI2 fragments are complete predicate fragments, and prove bag preservation
when the optimizer chooses the second or third predicate as physical driver.
Such a reordered driver need not be list-equal to source-order evaluation, so
order-sensitive modifiers remain on the ordinary path.  The axiom audit for
all four headline theorems reports only Lean's accepted `propext`,
`Classical.choice`, and `Quot.sound` foundations.

### Bounded three-way execution is a separate semantic contract

The natural next performance idea is to stop a three-way scan once `LIMIT n`
answers have been found.  That is **not** a safe drop-in optimisation for the
current list-valued Lean evaluator.  The physical plan chooses its smallest
predicate driver, SRI2 uses key/page order, and the direct HashMap path does
not preserve source-row order.  In contrast, `selectPost` currently gives
`OFFSET` and `LIMIT` their literal `List.drop`/`List.take` meaning.  A useful
nonzero limit could therefore change the observed result sequence.

The one immediately exact special case is `LIMIT 0`, which necessarily
returns no rows.  The useful general design is deliberately later: admit only
a default-graph, no-`VALUES`, modifier-free `SELECT *` over the distinct-var
three-predicate shape plus `LIMIT n`; define its result as any bag-subset of
at most `n` solutions, preserving RDF/SPARQL multiplicity; and prove that
contract rather than list equality.  It requires a resumable predicate cursor
and row-range APIs (`dictionaryPagesForRowRange?`, `scanRowRangePages`, and a
`scanEntriesPage`-style harness interface).  A driver page must be joined
completely against its two target fragments before stopping—reading merely
`n` driver rows is unsound because they may not join.  `ORDER BY`, `DISTINCT`,
`OFFSET`, grouping, and HAVING remain outside this first bounded admission.

`IndexedBlockV3Query` now performs that exact `LIMIT 0` case after manifest
and activation admission but before opening a primary artifact, sidecar, or
DLOG.  It reports `ibk3-limit-zero(0)` with zero logical/fetched bytes; the
persisted smoke covers this behavior.  It is intentionally not evidence for
nonzero early termination.

The first wire-layer prerequisite is now landed in
`IndexedBlockWireV3`: `rowRange?` validates an arbitrary `(start,count)`
within the declared fixed-width IBK3 row extent, while
`dictionaryPagesForRowRange?` and `scanRowRangePages` retain the existing
PTD1 page planning, absolute-range identity, term decoding, and predicate
checks for that checked slice.  The focused wire tests restore only Bob's
second row from a two-row block and reject a range extending beyond its
declared count.  `IndexedBlockV3Materialize.scanEntryRange` now carries that
same authenticated range through the file/Merkle reader into RDF triples.
Current query plans still use their existing prefix/selective routes; a
cursor executor will compose this primitive only together with the new
bounded-result contract.  The persisted smoke opens an activated SBM6 P31
artifact at row 1 for two rows and verifies that row 79 is rejected beyond
its declared 78-row extent (row 78 is the valid end cursor).

### Fast `DISTINCT` regression coverage

The normal query evaluator uses the tail-recursive, bucketed
`distinctSolutionsFast` implementation at runtime.  It traverses the input
from the end, uses a canonical binding key to restrict candidate comparisons,
and still performs full §18.3 binding equivalence before dropping a row.  The
reference `distinctSolutions` specifies that the last representative of each
equivalence class survives in original sequence order.

`QueryTests` now keeps a mixed-layout regression case in the ordinary Lean
build gate: repeated bindings in a different association-list order, repeated
single-variable mappings, and a separate two-variable/literal mapping must
produce exactly the same survivor sequence under the fast and reference
implementations.  This is useful executable protection for modifiers after a
persisted route has produced its rows; it is deliberately **not** the final
assurance claim.

The original runtime key independently collected, deduplicated, and sorted
the variables of every row.  That made the proof depend on a substantial
normalization theorem and repeated the same discovery/sort work per result.
The runtime now computes `distinctVariables` once for the whole solution
sequence.  `Binding.distinctKeyFor` aligns every row to that fixed universe as
a list of optional canonical term values: `none` means unbound, while a
present term is represented by `Term.joinKey`.  It then hashes this compact
aligned list.  The key is only a candidate partition; every match is still
confirmed by full `Binding.equiv`.

`QueryTheorems` now proves `Binding.equiv_distinctKeyFor`: equivalent mappings
have identical keys for *any* fixed variable universe.  Its supporting lemmas
prove successful-lookup transfer, canonical term-key equality, absence
transfer, and equality of the variable domains.  This closes the critical
bucket-safety direction—an equivalent row cannot be hidden in another
bucket—even for association lists with a shadowed duplicate variable and for
case-equivalent language tags.  Both cases are executable build guards.

The focused query/theorem builds and the complete persisted IBK3 smoke pass
with the new runtime representation.  No speed claim is recorded yet: the
expected gain is removal of per-row sorting, but it needs a repeatable
large-result benchmark.

The exact refinement is now complete.  `DistinctBucketWf` states that every
hash bucket is precisely the retained rows selected by that key, and its
empty/push theorems track the real worker updates.  `bucketAnyEq` proves that
probing one candidate bucket gives the same duplicate decision as scanning all
retained rows.  A separate shadow-removal lemma handles the subtle reverse
traversal case: if a mapping already has an equivalent later representative,
removing it cannot affect an earlier mapping because solution-map equality is
transitive.  These feed the accumulator theorem
`distinctSolutionsFastGo_eq` and the public result
`distinctSolutionsFast_eq`, which establishes exact list equality—not only
set or bag equality—with the simple reference implementation.  The axiom
audit reports only Lean's accepted `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry`, user axiom, `partial`, or native decision.
