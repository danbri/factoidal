# Planner soundness: a skipped entry cannot contribute a row

2026-09-06. Owner: "try theorem that a skipped entry cannot contribute a
row." Tracking: <https://github.com/danbri/factoidal/issues/658> (wire
version 10) and, for the evaluator side,
<https://github.com/danbri/factoidal/issues/614>.

## 1. Why this theorem and not another

The two real defects found in the persisted path this week were both in the
join between storage and query, not in either alone: a FILTER over an
extension function made the planner keep every block (issue 656, a
widening, harmless but slow), and duplicate rows across blocks became
duplicate triples in the dataset (a set-semantics fault, wrong answers).
The storage layer is proved to return the quads it was given; the
evaluator is proved at the basic-graph-pattern level and tested above it;
what has no theorem is the step in between: that reading ONLY the entries
`quadEntriesForQueryWithKeys` keeps answers the query as if every entry had
been read.

## 2. The statement

Let `M : Manifest`, `Q : Query`, `termKey : Term → Option (List UInt8)`.
Let `E = M.entries` and `S = quadEntriesForQueryWithKeys termKey M Q`.

Let `rows : Entry → List QuadRow` be the quads an entry's block denotes
(`IndexedBlockWireV5.resolveBlock` after `decode`, or the IBK4 form), and
`D(X) = QuadDataset.datasetOfQuads (X.flatMap rows)` the dataset a list of
entries denotes.

**Theorem (planner soundness).** For every `env`,

```
runSelectQueryBackendDataset env Q (indexedDatasetBackend (D S))
  = runSelectQueryBackendDataset env Q (indexedDatasetBackend (D E))
```

and the same for `runAskQueryBackendDataset`, under the hypotheses the
collectors already check at run time (they return `none` and keep every
entry otherwise, so the theorem is vacuous exactly when the planner is
conservative):

* `Query.expressionsOutsidePatternExistsFree Q = true`;
* `M.valid = true`, every entry of `E` decodes, and every entry's manifest
  fields agree with its block (this is what activation checks:
  `graphSet` equals the block's graph set, `subjectZone`/`objectZone`
  equal `BlockV5Plan.zones?`, `predicate` equals the block's predicate);
* `termKey t = TermWireV2.keyBytes (toWire h t)` for the `h` the packer used
  (the zone keys and the query keys come from the same function).

"A skipped entry cannot contribute a row" is the contrapositive read of
this equality: every row of the answer over `D E` is a row of the answer
over `D S`.

## 3. Decomposition, one lemma per collector

Each collector keeps an entry unless a syntactic property of `Q` lets it
exclude the entry. The proof is: (a) the property implies the evaluator
depends only on a RESTRICTION of the dataset; (b) the kept entries denote a
dataset whose restriction equals the full dataset's restriction.

**Lemma P (predicates).** If `queryQuadConstantPredicates? Q = some P`, then
for every dataset `D`, `eval Q D = eval Q (restrictPred P D)` where
`restrictPred` keeps the triples whose predicate is in `P`, in every graph.
Proof by induction on the pattern, using that every triple pattern and
path step has a constant predicate in `P` (that is what the collector
computed) and that the evaluator's BGP matching of a pattern with constant
predicate `p` touches only triples with predicate `p`. FILTER, BIND, ORDER,
projection never read the dataset when `expressionsOutsidePatternExistsFree`
holds and the collector refused patterns with EXISTS (it does).

Then (b): `restrictPred P (D E) = restrictPred P (D S)` because an entry
excluded by the predicate collector has `entry.predicate ∉ P` and, by the
activation invariant, every row of its block has that predicate.

**Lemma G (graphs).** If `queryGraphNames? Q = some G`, then
`eval Q D = eval Q (restrictGraphs G D)` where `restrictGraphs` keeps the
default graph and the named graphs in `G` (and, for a `GRAPH <g> {}`, the
graph name's presence is what the collector added `g` for). Proof by
induction on the pattern: the active graph of every triple pattern is a
constant in `G` or the default graph; no `FROM`; no `GRAPH ?v`.
Then (b) via `graphSet`: an excluded entry's graph set meets no name in
`G`, and every row of its block has a graph in its graph set.

**Lemma Z (zones).** If `queryQuadConstantSubjects? Q = some Ss` then every
triple pattern's subject is a constant in `Ss`, so
`eval Q D = eval Q (restrictSubj Ss D)`. Then (b) via `zoneMap_sound`
(already proved): a row whose subject key is `k` lies in an entry whose
subject zone may contain `k`; an entry with `zoneKeepsEntry = false` for
every `s ∈ Ss` therefore holds no row with a subject in `Ss`. Same for
objects. The hypothesis that the zone keys and the query keys use one
`termKey` is where `toWire`'s canonical choice matters.

**Composition.** The three restrictions commute (each is a filter on
triples by a different field), so `eval Q (D E) = eval Q (r (D E))` for the
composed restriction `r`, and `r (D E) = r (D S)` because `S` is exactly the
filter of `E` by the three predicates, and each excluded entry contributes
nothing to `r (D ·)`.

## 4. What the evaluator side needs

The restriction lemmas are statements about `SPARQL/Query.lean`'s
`evalSelect` (line 1704) through `StoreDataset.lean`'s
`indexedDatasetBackend` seam. The evaluator is fuel-bounded and
match-heavy; `skills/lean4-proof-patterns/SKILL.md` gives the theorem
shape for fuel independence and the splitting recipe. The natural first
target is the BGP fragment, where `unified_adequate_bgp` already exists,
then Join, Union, Filter, Optional in the order issue 614 lists. Whatever
fragment the lemma covers, the collector must REFUSE (return `none`) outside
it, so the theorem's hypothesis is exactly the collector's admission: the
proof and the run-time guard are one definition.

## 5. Gate

* `#print axioms` of each theorem: `propext`, `Classical.choice`,
  `Quot.sound` only.
* The two defects re-stated as `#guard`s: the extension-function FILTER
  (issue 656) is admitted by the theorem because the collector keeps every
  entry; the duplicate-row case is covered because `datasetOfQuads` builds
  a set (the theorem is over `D`, which is that set).
* No collector may be widened without extending the lemma: a `#guard` pins
  each collector's admitted fragment.
