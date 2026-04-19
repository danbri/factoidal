# Tableau-flavoured OWL reasoning for factoidal — scoping note

**Date:** 2026-04-19 (scoped from the session that landed the OWL 2 RL
Datalog subset in commit `909b1fb`).
**Author:** scoping sub-agent, read-only.
**Baseline:** `entailment` suite 47 pass / 23 fail after OWL 2 RL Datalog
rules layered on top of RDFS closure.

## 1. What "tableau OWL" means here

For the 23 currently-failing entailment tests we are not proposing to
embed a full OWL-DL tableau reasoner. We are scoping which OWL
constructs, when added to our existing **fuel-bounded forward-chaining
closure** in `RDF.Graph.Executable.fst` (or a thin extension), would
unlock how many tests — and where the wheels come off.

Architectural constraint: our closure is a pure F* function
`entailment_closure : graph -> nat -> graph` that loops over a finite
rule set until fixpoint or fuel. It does not introduce fresh terms
beyond what the rules produce from ground triples. That's the hard
boundary between "Datalog-style" (a) and everything else (b/c) below.

## 2. The 23 failing tests

From `.claude-runs/entailment-owl-rl-20260419-152749.log`:

| Test | Expected rows | Key OWL constructs that block us |
|---|---:|---|
| paper-sparqldl-Q1 | 3 | `owl:Nothing` as implicit subclass of every class (tableau) |
| paper-sparqldl-Q2 | 1 | anon-class via `owl:intersectionOf(Student,Employee)` **as query bnode**, plus type inference into it |
| paper-sparqldl-Q3 | 2 | `owl:complementOf` combined with `owl:someValuesFrom` restriction |
| parent3 | 3 | `owl:someValuesFrom owl:Thing` — anon restriction class membership |
| parent4 | 3 | `owl:minCardinality 1` — anon restriction class membership |
| parent5 | 1 | `owl:someValuesFrom :Female` — qualified value-existential |
| parent6 | 1 | `owl:minQualifiedCardinality 1` + `owl:onClass` |
| parent7 | 1 | `owl:maxQualifiedCardinality 1` + `owl:onClass` |
| parent8 | 1 | `owl:qualifiedCardinality 1` + `owl:onClass` |
| parent9 | 4 | subclass inference into anon `someValuesFrom owl:Thing` + `owl:Nothing` |
| parent10 | 3 | same as parent9 but excluding `owl:Nothing` |
| simple1 | 2 | anon query class via `owl:intersectionOf(A,B)` — class-expression query |
| simple2 | 1 | nested `intersectionOf + Restriction someValuesFrom` |
| simple3 | 1 | `someValuesFrom` over anon intersection (A∩B) |
| simple4 | 4 | `owl:unionOf(B,C)` — anon query class |
| simple5 | 2 | `someValuesFrom` over anon `unionOf(A,B)` |
| simple6 | 3 | `allValuesFrom` over anon `unionOf(A,B,C)` |
| simple7 | 2 | `intersectionOf(A, unionOf(B,C))` — nested boolean combinators |
| simple8 | 1 | `someValuesFrom [ someValuesFrom :B ]` — chained existential + `owl:FunctionalProperty` needed (uses `:p` functional) |
| sparqldl-11 | 2 | `rdfs:domain` inferred from `owl:inverseOf :child` + `:child rdfs:domain :Parent`, plus `owl:Thing` as ubiquitous class |
| sparqldl-12 | 2 | mirror of 11, using `rdfs:range` |
| rif01 | 1 | RIF rule (`ex:uncle` from `ex:parent` + `ex:brother`) — not OWL at all |
| rif03 | 1 | RIF frames rules — not OWL at all |

The RIF tests (rif01, rif03) are **not OWL**; they reference external
`.rif` documents and test RIF Core entailment. Including them here
only because they sit in the same manifest.

## 3. Grouping by construct

Grouped by the dominant OWL construct that, if handled, would unlock
the test. Tests often use two constructs; I score each to the one
likeliest to be the blocker, and flag multi-construct tests.

### Group A — anon class expressions as **query patterns**

**Tests:** simple1, simple2, simple3, simple4, simple5, simple6,
simple7, paper-sparqldl-Q2.
**Count:** 8 tests.

The query writes a class expression in-line using a blank node, e.g.:

```sparql
?x a [ owl:intersectionOf ( :A :B ) ] .
```

We currently resolve this triple pattern literally: "find `?x` whose
`rdf:type` is a bnode whose `owl:intersectionOf` is the list
`(:A :B)`." The data file rarely contains such a bnode verbatim — the
test expects OWL reasoning to recognise that any `?x` which is both
`:A` and `:B` **should satisfy** this anonymous class.

Two styles of fix:

1. **Class-expression rewriting in the query.** Pre-process the
   SPARQL query: when a bnode in the WHERE has `owl:intersectionOf
   (X Y)` binding, rewrite the pattern to `?x a X . ?x a Y .` (and
   substitute equivalent for unionOf, someValuesFrom, allValuesFrom,
   complementOf). This is effectively compiling OWL class expressions
   into SPARQL property paths + filters. Pure query transformation;
   no new term generation.

2. **Materialise anon classes in closure.** For every anon class bnode
   in the *data*, add forward rules that populate its
   instance-of triples. But the bnodes are in the **query**, not the
   data — so (1) is the right shape.

Verdict: **cheap (a)** — class-expression query rewriting. Estimate:
~200 LOC F*, operates on the parsed query AST. Unlocks ~8 tests.

### Group B — subclass axioms for anon restriction classes (parent9, parent10, parent3, parent4)

**Tests:** parent3, parent4, parent9, parent10.
**Count:** 4 tests.

The data defines `:Parent owl:equivalentClass [ Restriction onProperty
hasChild someValuesFrom owl:Thing ]`. Queries ask for things that are
instances of (parent3/4) or subclasses of (parent9/10) this anon
restriction.

For parent3: given `:hasChild` triples in the ABox, we need
"`?x has-some-hasChild` → `?x rdf:type <anon-restriction>`". For
parent9: `:Parent rdfs:subClassOf <anon>` plus `:Father rdfs:subClassOf
:Parent` (already handled) plus `owl:Nothing rdfs:subClassOf
<anything>`.

- The `someValuesFrom owl:Thing` rule is equivalent to
  `owl:minCardinality 1` with no class restriction. OWL 2 RL
  **does** include `cls-svf1`/`cls-svf2`/`cls-maxc2`/… but they apply
  to restrictions **named in the TBox**, not to a fresh query bnode.
- If we materialise the class-expression→anon-IRI mapping and apply
  `cls-svf1` / `cls-maxc2` etc. as extra Datalog rules, these pass.
- The `owl:Nothing` subclass-of-everything is a **single axiom**:
  `owl:Nothing rdfs:subClassOf ?C` for every class `?C`. Cheap.

Verdict: **cheap (a) + a schema-scan**. OWL 2 RL already has
`cls-svf1`, `cls-svf2`, `cls-maxc1`, `cls-maxc2`, `cls-avf` etc.; we
just haven't wired them. Estimate: ~150 LOC F* to materialise the
rules over existing `owl:Restriction` bnodes in the TBox. Unlocks ~4
tests (parent3, parent4, parent9, parent10).

### Group C — qualified cardinality (parent5, parent6, parent7, parent8, simple8)

**Tests:** parent5, parent6, parent7, parent8, simple8.
**Count:** 5 tests.

- parent5: `someValuesFrom :Female` — "exists hasChild which is Female".
- parent6: `minQualifiedCardinality 1` + `onClass :Female`.
- parent7: `maxQualifiedCardinality 1` + `onClass :Female`.
- parent8: `qualifiedCardinality 1` (equiv. to min1 ∧ max1).
- simple8: `p some (p some B)` — nested existential, plus `p` is
  `owl:FunctionalProperty` (which is Datalog-shaped and already in our
  rule set).

parent5/6 have the **same** expected answer (Dudley), because each
means "has at least one hasChild that is Female". Dudley has
`:hasChild :Alice` and Alice is `:Female`. Detection: if `?x p ?y` and
`?y a :C`, infer `?x a [someValuesFrom :C onProperty :p]`.
Datalog-expressible as a forward rule keyed on the TBox-known
restriction bnode. **Cheap (a)**.

parent7 is `max 1 Female`. "Dudley has at most 1 Female child" —
vacuously true for Dudley, who has 1 Female child. In open-world OWL,
this reverses the inference: we can only infer `?x ∈ max1Female` if
we know there aren't 2 distinct Females. This requires:
- either `owl:differentFrom` / `owl:AllDifferent` axioms, or
- UNA (Unique Name Assumption) — which OWL does not assume by default
  but **pragmatically** works in the W3C test's flat IRI set.

If we enable UNA-as-preprocessing (all named individuals distinct
unless `sameAs` is asserted), max-N-qualified becomes Datalog-shaped:
"if `?x p ?y1, ?x p ?y2, ..., ?x p ?yN+1` with yi all named and
Female, then `?x a owl:Nothing`. Contrapositive: we cannot prove
membership via a forward rule; we can only disprove. **parent7 and
parent8 need real tableau.** See §5.

Verdict: **parent5, parent6 cheap (a)** (~50 LOC each, shared
someValuesFrom machinery from Group B unlocks them). **parent7,
parent8 expensive (c)** — true `max`-cardinality reasoning requires
either UNA+contradiction-as-proof (fragile, not how OWL-RL is
specified) or a tableau branch. Skip. **simple8** is Group A + chain —
falls out of Group A's rewriting if we handle nested restriction
composition. **Cheap (a)**.

Net: 3 cheap passes (parent5, parent6, simple8), 2 skip
(parent7, parent8).

### Group D — `owl:complementOf`, `owl:disjointWith` (paper-sparqldl-Q3)

**Tests:** paper-sparqldl-Q3.
**Count:** 1 test.

Query asks for `?x` with `hasPublication` that is published at "not a
Workshop". Data has: `paper1` published implicitly via
`ConferencePaper ⊑ ∃ publishedAt.Conference`, and
`Conference owl:disjointWith Workshop`.

Three reasoning steps:
1. `paper1` ∈ ConferencePaper → ∃ Z. `paper1 publishedAt Z` ∧
   `Z ∈ Conference`. Here we'd need to skolemise an individual Z
   (bnode).
2. `Conference owl:disjointWith Workshop` → `Z ∉ Workshop`.
3. `Z ∉ Workshop` ⇒ `Z ∈ complementOf(Workshop)`.

Step 1 requires **term generation**: bounded skolemisation of
"someValuesFrom" into a fresh bnode. Step 3 requires **negation-as-
failure** or classical refutation. In a pure-forward Datalog setting
the closest we get is if we pre-materialise `¬Workshop` as an
explicit marker on named individuals not in Workshop (finite-domain
closed-world reading). That is **unsound relative to OWL** — OWL is
open-world — and would break other tests that rely on OWL's open-
world semantics.

Verdict: **expensive (c)**. Not reachable without a tableau or, at
minimum, a grounded bnode generator plus explicit complement
materialisation. Skip.

### Group E — `owl:Thing` as implicit universal class (sparqldl-11, sparqldl-12, paper-sparqldl-Q1, parent9)

**Tests:** sparqldl-11, sparqldl-12, paper-sparqldl-Q1, parent9
(already in B).
**Count:** 3 distinct (Q1 shared with A).

sparqldl-11 expects `?C ∈ {owl:Thing, :Parent}` for `:child
rdfs:domain ?C`. We infer `:Parent` from `:child rdfs:domain
:Parent` (explicit). We do not infer `owl:Thing` because we don't
axiomatise it.

Fix: add the OWL-RL axiom `?P rdfs:domain owl:Thing` and `?P
rdfs:range owl:Thing` for every property `?P`, and
`?X a owl:Thing` for every named individual `?X`. Plus `owl:Nothing
rdfs:subClassOf owl:Thing`, `?C rdfs:subClassOf owl:Thing` for every
class `?C`.

These are **single-pattern Datalog rules** over the existing closure.
Very cheap. Estimate: ~30 LOC F*.

paper-sparqldl-Q1 needs `owl:Nothing` to appear as a subclass of
`:Student`. Same story: axiom `owl:Nothing rdfs:subClassOf ?C` for
every `?C ∈ classes(G)`. Cheap.

Verdict: **cheap (a)**. Unlocks 3 tests.

### Group F — RIF (rif01, rif03)

Not OWL. These reference RIF-XML rule documents. Implementing RIF
Core entailment is a separate project. **Skip** (mark explicitly
unsupported).

## 4. Ordered shortlist: "next K tests per line of F* effort"

Rough effort estimates. "Cheap" means the rule is pure Datalog over
the existing closure; no fresh terms, no new fixpoint.

| # | Work item | LOC F* | Tests unlocked | Tests/LOC |
|---|---|---:|---:|---:|
| 1 | owl:Thing / owl:Nothing universal axioms (Group E) | ~30 | 3 (sparqldl-11, -12, paper-Q1) | 0.10 |
| 2 | Class-expression query rewriting: intersectionOf, unionOf as query bnodes (Group A subset) | ~200 | 5 (simple1, simple4, simple7, paper-Q2; simple8 partial) | 0.025 |
| 3 | `cls-svf1/2`, `cls-maxc1/2`, `cls-avf` OWL-RL rules over TBox restrictions (Group B) | ~150 | 4 (parent3, parent4, parent9, parent10) | 0.027 |
| 4 | Qualified someValuesFrom with `onClass` (Group C partial) | ~50 | 2 (parent5, parent6) | 0.04 |
| 5 | Nested class-expression rewriting (someValuesFrom over unionOf etc.) (Group A remainder) | ~100 | 3 (simple2, simple3, simple5, simple6 — overlap with #2) | 0.03 |

**Total cheap-Datalog wins:** ~17 of 23 tests (ignoring rif01/rif03
and the 4 hard-tableau tests). Call it **14 new passes** after
overlap and after being honest about which ones actually match.

**Recommended launch order:**
1. Group E (quick 3-for-30). Fastest win, exposes no new machinery.
2. Group B (parent3/4/9/10 via existing OWL-RL cls-* rules we haven't
   wired). Good ratio, confirms our existing closure infrastructure.
3. Group C partial (parent5, parent6). Small, builds on B.
4. Group A (simple1..7 + paper-Q2). Biggest single lift; moves class
   expressions into the *query preprocessor* rather than the closure
   — architecturally new and worth a design review before jumping in.

After steps 1–4: **entailment 47 → ~56 / 23 → ~14**.
After step 5: **entailment ~62 / 8 remaining**.

Remaining 8 = rif01, rif03, paper-sparqldl-Q3, parent7, parent8,
simple8-hard-edge, and 2 more that depend on whichever of the above
don't pan out cleanly.

## 5. What NOT to do

These are traps. Do not attempt them under the current
forward-chaining closure architecture.

### Max/exactly qualified cardinality (parent7, parent8)

`max N qualified` requires either:
- **Tableau branching on equality**: given N+1 hasChild's, try each
  pairwise `sameAs` assignment; if one leads to a consistent model,
  entailment holds. Exponential in N. Completely outside our pure-
  forward architecture.
- **UNA + contradiction-as-proof**: close the world on named
  individuals, refute by counting. Breaks OWL semantics for other
  tests; also requires finite-domain reasoning.

Adding this to factoidal would require a separate `tableau.fst` module
with backtracking search, integrated by a switch on the entailment
regime. That's a **multi-session project**, not an incremental fix.

### `owl:complementOf` / open-world negation (paper-sparqldl-Q3)

OWL's complementOf is a classical negation under open-world
assumption. Our closure is Datalog-positive (Horn). Adding classical
negation = stratified Datalog at best, full disjunctive Datalog at
worst — changes the complexity class and breaks the simple fuel
fixpoint. **Skip.**

### `owl:someValuesFrom` with bnode generation in the ABox

paper-sparqldl-Q3 also implicitly requires "ConferencePaper ⊑ ∃
publishedAt.Conference implies for each paper there exists a bnode Z
s.t. paper publishedAt Z and Z ∈ Conference." This is sound
skolemisation, but the generated Z is a **fresh term** which would
thread through the closure's bnode identity tracking. Our closure
does not generate fresh terms and doing so correctly (without
infinite loops on cyclic schema) requires a term-depth bound per
individual. **Moderate-difficulty (b)**; worth considering later but
unlocks only 1 test at high implementation cost.

### RIF (rif01, rif03)

Not OWL. Shipping a RIF Core interpreter is an entirely separate
project. **Mark unsupported, not failing.** A follow-up ticket can
propose reclassifying these from FAIL to SKIP on the basis that
we do not advertise RIF support.

### W3C tests that over-specify

- **paper-sparqldl-Q1** expects `owl:Nothing` in the answer set. Some
  reasoners (Pellet, HermiT) produce this; many reasonable
  implementations do not. Even after our Group E fix we will pass
  this, but the test is **semantically dubious** — `owl:Nothing`
  subclass-of-`:Student` is vacuously true but not useful. Not a
  reason to skip; just calling out that "correct" here is a tight
  reading.
- **parent9 / parent10 disagree on `owl:Nothing`**: parent9 includes
  it, parent10 filters it out. Both expect the `hasChild some Thing`
  restriction to be subclassed by Parent, Father, Mother. Good check
  that our Group B fix is correct for both polarities.

### OWL-DL tableau — NOW A COMMITTED PRIORITY (2026-04-19 evening update)

*Earlier drafts of this document treated a tableau reasoner as "out
of scope" or "multi-session project". **User direction 2026-04-19
reverses that.** A tableau implementation is now a committed goal for
factoidal. It belongs in a new `formal/fstar/Tableau.fst` module,
gated by the entailment regime (e.g. `OWL-Direct`, distinct from
`OWL-RL`), and is expected to take many sessions to land.*

Rough shape of the work, in order of session-sized chunks:

1. **Scoping commit**: add a new `OwlTableau.fst` skeleton with only
   the data types (tableau node, branch, status enum, blocking rule)
   and an `owl_tableau_entails` signature returning `option bool`.
   Wire it into `entailment_closure` for the `OWL-Direct` regime so
   the runner at least doesn't crash; return `None` = unknown.
2. **ABox + simple TBox**: handle explicit triples + `rdfs:subClassOf`
   already folded in. Extend to handle class-expression axioms (`∀`,
   `∃`, `⊓`, `⊔`, `¬`) as **syntactic tests only** — ask "does this
   specific individual satisfy this specific class expression?"
   without materialising. This unlocks Groups A/B/C from §5.
3. **Cardinality (`min/max/exact`)**: tableau branching on counts.
   Needs UNA/NUNA handling. Unlocks parent7, parent8.
4. **`owl:complementOf`** + consistent-model search: classical
   negation via dual-branch search. Unlocks paper-sparqldl-Q3.
5. **Fresh-individual skolemisation (`∃`-in-head)**: bnode generation
   with depth-bound blocking. Unlocks paper-sparqldl-Q3's ABox half.
6. **Optimisations**: blocking, absorption, pruning, ordering
   heuristics. Only once correctness is in place.

Rough sizing: 2–5k LOC F* once done. Termination proofs are the hard
part; we accept that some of this will use `--admit_smt_queries true`
initially and pay down the proof debt incrementally, clearly flagged.

**This item is now priority item #2 in the worklog priority queue**
(after the remaining in-flight subagent work lands).

## 6. Summary

- **23 failing entailment tests.**
- **~14 achievable via Datalog-style extensions** (Groups A, B, C-partial, E), estimated ~500 LOC F* spread across 4 subagent sessions.
- **~6 unsuitable for our architecture** (parent7, parent8, paper-Q3, rif01, rif03, and whichever Group A nested cases refuse to rewrite cleanly).
- **Recommended single next subagent:** implement Group E
  (`owl:Thing`/`owl:Nothing` universal axioms). 30 LOC F*, 3 tests
  unlocked, zero new machinery. Best ratio, lowest risk.
