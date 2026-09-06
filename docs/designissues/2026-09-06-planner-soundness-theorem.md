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

---

## 6. Status, 2026-09-06

Landed on branch `wt/planner-soundness`. `lake build` clean (1002 jobs),
`tools/lean-hygiene-audit.py` clean (0 `sorry`, 0 user `axiom`, 0
`native_decide`, 0 `unsafe`, 172 `partial def` at baseline),
`tools/blockengine-ibk5-quad-smoke.sh` and
`tools/blockengine-ibk4-quad-smoke.sh` pass, and the persisted census
(`tools/w3c-persisted-census.sh`) reports 501 executed / 491 matched /
**0 differed** on the default-graph path and 29 executed / 29 matched /
**0 differed** on the named-graph path.

### 6.1 What is proved

`formal/lean4/L4Factoidal/SPARQL/DatasetRestriction.lean`:

| Theorem | Statement |
|---|---|
| `igSearch_ofGraph_filter` | A bound whose every match survives a Boolean `keep` reads the same rows, in the same order, from `Index.ofGraph (g.filter keep)` as from `Index.ofGraph g`. This is what removes the hash index from the rest of the development: `Index.Wf` (`OWL/RLClosureIndexed.lean`) already proves each bucket lookup is a `List.filter`, so the six candidate sets commute with the restriction and `tripleMatchesBound` absorbs it. |
| `evalBgpBackend_restrict` | The BGP evaluator, planner included: equal estimates give the same plan in the same order, so the answer is the same LIST. |
| `evalPatternBackend_restrict` | The pattern induction over `plannerFragment`. |
| `evalSelectBackendOnGraph_restrict`, `evalSelectBackendDataset_restrict`, `evalAskBackend_restrict` | The four fast paths, branch by branch. |
| `runSelectQueryBackendDataset_restrict`, `runAskQueryBackendDataset_restrict` | The two query entry points, over `q.pattern.rewriteBnodes`. |

`formal/lean4/L4Factoidal/Storage/PlannerSoundness.lean`:

| Theorem | Statement |
|---|---|
| `datasetRestricted_restrictDataset` | The canonical restriction `restrictDataset keep d` satisfies `DatasetRestricted`, for a dataset whose named-graph keys are distinct and whose named graphs are non-empty — both of which `datasetOfQuads` gives. |
| `plannerSoundnessSelect`, `plannerSoundnessAsk` | Section 2's equality, with the storage side reduced to `restrictDataset keep (D S) = restrictDataset keep (D E)`. |
| `patternKept_of_queryPredicates` | `queryQuadConstantPredicates? q = some P` implies `PatternKept (keepPred P) q.pattern.rewriteBnodes` — the predicate collector establishes the evaluator theorem's hypothesis. The two zone collectors have the same shape and are not written. |

`#print axioms` of every theorem above: `propext`, `Classical.choice`,
`Quot.sound`.

### 6.2 The fragment

`SPARQL.DatasetRestriction.plannerFragment`, and all four collectors of
`Storage/ShardManifest.lean` now guard on it, over
`query.pattern.rewriteBnodes` — the pattern the evaluator runs — so the
run-time guard and the theorem's hypothesis are one expression, which is
section 4's rule.

Admitted: a BGP (empty or not), `JOIN`, `UNION`, `MINUS`, `OPTIONAL`,
`FILTER` and `BIND` with an `Expr.backendLocal` expression, `GRAPH <iri>`
and `GRAPH ?v` whose body carries no further `GRAPH`, and the empty group
pattern. The two empty leaves carry a side condition in `PatternKept`:
they answer one solution without reading the active graph, so the
restriction must keep every triple — which is what the collectors
establish for them, since all three return `none` on an empty leaf.

Refused: a `GRAPH` inside a `GRAPH`, a property path, a sub-SELECT,
`VALUES`, `SERVICE`, `LATERAL`, and a `FILTER`, `OPTIONAL` or `BIND` whose
expression is not `Expr.backendLocal`.

### 6.3 Two defects the proof found

Both are wrong answers, not slow ones, and both are repaired by the
narrowing rather than merely left unproved.

1. **A `GRAPH` inside a `GRAPH`.** Section 18.6 gives `GRAPH <n> { P }`
   no solutions when the dataset does not name `n`, whatever `P` is. The
   predicate collector drops every entry of graph `n` when no row of `n`
   carries a predicate the query names, and `n` then disappears from the
   materialised dataset — so
   `GRAPH <n> { GRAPH <m> { ?s :p ?o } }` answers rows over every entry
   and nothing over the selected ones, because the inner pattern reads
   `m` and never touches `n`. The zone collectors can drop `n`'s entries
   the same way.
2. **A language-tagged or `rdf:XMLLiteral` constant object.**
   `Term.eqb` folds language-tag CASE and canonicalises XML;
   a zone bound is the version-2 wire key, which does neither.
   `"chat"@en-US` and `"chat"@en-us` are one value with two keys, so an
   object-zone test on the query's key can drop a block that holds a
   matching row. `constantObjectOf` now applies
   `RDF.exactObjectIndexKeySafe`, the same condition the in-memory object
   index carries for the same reason.

### 6.4 What the narrowing costs

Measured, not estimated: both quad smoke scripts pass unchanged, so the
`shards=` counts they pin — including the `GRAPH ?g` predicate selection
and the `zone-excluded=2` subject-zone case — are unchanged, and the
census reports no answer difference.

The one shape that reads more than before is a `FILTER`, `OPTIONAL` or
`BIND` whose expression is not `Expr.backendLocal`: an extension function, REGEX,
REPLACE, `IRI()`, `NOW()`, an aggregate. The planner now keeps every
entry for those, which is the widening
<https://github.com/danbri/factoidal/issues/656> recorded. It is back
deliberately: `evalPatternBackend` materialises the whole dataset for
those arms and delegates to the algebra evaluator, which this theorem
does not reach. Removing it again means extending
`evalPatternBackend_restrict` to the delegating arms
(<https://github.com/danbri/factoidal/issues/614>).

### 6.5 Where section 3 was wrong, and the repair

Section 3 states the storage side as `D S = restrictPred P (D E)`. That
is not what the planner produces. An entry the planner KEEPS may hold
rows the restriction drops: a block selected by its predicate carries
rows whose subject lies outside the query's zone bounds, and the reader
reads them. `D S` therefore lies BETWEEN `restrict keep (D E)` and
`D E`, and is neither.

The repair is to apply the evaluator theorem to each side:

```
eval Q (D S) = eval Q (restrict keep (D S))
             = eval Q (restrict keep (D E))     -- the storage obligation
             = eval Q (D E)
```

which is `plannerSoundnessSelect`. The storage obligation is now an
equality of DATASETS — a statement about which quads survive, with no
evaluator in it.

### 6.6 Open

1. **The `datasetOfQuads` bridge.** `restrictDataset keep (D S) =
   restrictDataset keep (D E)` is not proved.
   `Storage/QuadDataset.lean`'s `datasetOfQuads` is a `foldl` over
   `Std.HashMap` accumulators, and the proof needs a `Index.Wf`-style
   characterisation of it against a specification (first-occurrence
   dedup per graph, graphs in first-occurrence order), and then the
   entry-level facts: an excluded entry's rows all fail `keep`, or lie
   in a graph the query cannot read. The activation invariants those
   entry-level facts need are what `GenerationVerify` checks —
   `graphSet` equals the block's graph set, `subjectZone`/`objectZone`
   equal `BlockV5Plan.zones?`, `predicate` equals the block's predicate
   — plus `zoneMap_sound` (`Storage/ShardManifestTheorems.lean`), which
   turns the packer's bounds into `zoneMayContain`.
2. **The two ZONE collectors' correspondence.** The predicate one is
   `patternKept_of_queryPredicates`. The subject and object analogues
   need one extra step each: the evaluator's `keep` compares terms with
   `Subject.eqb` / `Term.eqb` while a zone compares wire keys, so the
   bridge is that an `exactObjectIndexKeySafe` constant which is
   `Term.eqb`-equal to a row's object is EQUAL to it. That is why
   `constantObjectOf` now carries that test (6.3, defect 2).
3. **The delegating arms**, per 6.4.
4. **`env.dataset`.** The theorem is stated for a FIXED `env`, so it
   says nothing about a caller that builds `env.dataset` from the
   selected entries. The `Query.expressionsOutsidePatternExistsFree`
   guard stays on the collectors for that reason.


## 7. `BIND` enters the fragment, 2026-09-06 (second landing)

Branch `wt/planner-bind`. The first landing refused `BIND`, and that cost
two cases of `Wasm/native-smoke.sh` (104 pass to 102 pass, 2 fail out of
104). Both run

```
SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } BIND(STRLEN(?o) AS ?n) }
```

against a five-predicate IBK5 store and pin `shards == 1`. With `BIND`
outside `plannerFragment` the predicate collector kept all five entries,
and the second case then failed to resolve an out-of-line literal blob
the host had not supplied for the four entries it should never have
opened.

### 7.1 Why the proof needed an evaluator change first

`BIND` fell to `evalPatternBackend`'s materialise-and-delegate arm: it
rebuilt the whole dataset as lists and ran `GraphPattern.evalIn` on the
lowered pattern. Restriction does not commute through that path by any
argument this induction can make — the delegated evaluator is a second
evaluator, which is exactly why a non-`backendLocal` `FILTER` is refused.
Proving the `BIND` case "through that path" is therefore not available;
what is available is the same move the `FILTER` and `GRAPH ?v` arms
already made, and for the same two reasons (correctness of the planner
guard, and not rebuilding the dataset per query).

`SPARQL/StoreDataset.lean` now carries a backend-native `.bind` arm,
taken when the bound expression is `Expr.backendLocal`:

```lean
| .bind expression v pattern, gb =>
    if expression.backendLocal then
      bindRowsFresh (fun _ row => (Expr.evalIn env row expression).toTerm?)
        [] v (evalPatternBackend env dsb pattern gb) 0
    else <materialise and delegate, as before>
```

The row list, the freshness context, the row order and the
already-bound-variable rule are the reference's own `bindRowsFresh`,
applied to the rows this evaluator produced. Two things differ from
`QueryPattern.lowerWith`'s `.bind` arm, and both are the deviations the
`.filter` arm already carries: the binder reads the row rather than
`Binding.empty.merge row` (the same lookups), and it does not call
`substituteExistentials`, which is the identity on a `backendLocal`
expression — `Expr.backendLocal` admits neither `EXISTS` nor
`NOT EXISTS`. The `active` graph the reference binder receives is never
consulted by such a binder, so the native arm passes `[]` and reads no
triple.

### 7.2 What the proof is

`plannerFragment` gains `| .bind e _ p => e.backendLocal &&
plannerFragment p`, and `graphNamesIn`, `graphVarIn` and `PatternKept`
gain the matching recursive arm — without those three the theorem's
hypotheses would be vacuous on a `GRAPH` inside a `BIND` body. The
`evalPatternBackend_restrict` case is then the `.filter` case verbatim:
the arm's condition does not read the dataset, so restriction passes
through to the body. `evalPatternBackend_nil` gains the case that
`bindRowsFresh binder a v [] 0 = []`.

`Storage/PlannerSoundness.lean`'s `PatternKept_mono` and
`patternKept_of_quadPredicates` gain real `.bind` arms where they
previously closed by `trivial` on `PatternKept`'s `True`;
`quadNativeConstantPredicates?` already descended through `BIND` under
its `existsFree` guard, so no collector changed.

`#print axioms` of `evalPatternBackend_nil`,
`evalPatternBackend_restrict`, `runSelectQueryBackendDataset_restrict`,
`runAskQueryBackendDataset_restrict`, `PatternKept_mono`,
`patternKept_of_quadPredicates`, `patternKept_of_queryPredicates`,
`plannerSoundnessSelect` and `plannerSoundnessAsk`: `propext`,
`Classical.choice`, `Quot.sound` only.

### 7.3 Gates

`lake build` clean (1055 jobs), `tools/lean-hygiene-audit.py` clean
(0 `sorry`, 0 user `axiom`, 0 `native_decide`, 0 `unsafe`, 172
`partial def` at baseline), `tools/blockengine-ibk5-quad-smoke.sh` and
`tools/blockengine-ibk4-quad-smoke.sh` pass, `Wasm/native-smoke.sh` back
to 104 pass, 0 fail (out of 104).

Anti-pattern 34 applies to 7.1 — it moves a query shape from the
reference evaluator to the backend runner — so the persisted census is
the gate that can see a wrong answer from it, not the smoke scripts. Its
result is in 7.4.

### 7.4 The census, and what it says about 7.1

`tools/w3c-persisted-census.sh` after the change, run in this worktree
after `tools/ensure-test-env.sh` (a worktree inherits no test submodules,
and the first run reported 0 executed of 0 eligible):

* default graph (IBK3): 535 executed, 0 refused at pack/activate, 0
  refused at query, out of 535 eligible; of the 535 executed, **535
  matched the reference engine, 0 differed**, 0 not comparable.
* named graphs (IBK4): 29 executed, 0 refused at convert/pack/activate,
  6 refused at query, out of 35 eligible; of the 29 executed, **29
  matched, 0 differed**, 0 not comparable.

Section 6's record of the first landing quotes 501 executed / 491 matched
on the default-graph path. No pre-change baseline was measured IN THIS
WORKTREE, so the 501-to-535 difference is not attributed here; what the
run establishes is the property anti-pattern 34 asks for, that no query
the persisted path executes answers differently from the reference
evaluator after the routing change.

Four `#guard`s in `SPARQL/StoreDataset.lean` pin the native `.bind` arm
against the reference on the cases that separate it from a plain map: an
expression that errors on every row (§18.6 leaves the variable unbound
and keeps the row), one that errors on some rows only, a variable the row
already binds (the row's own value wins), and a non-`backendLocal`
expression (`NOW()`), which still delegates.
