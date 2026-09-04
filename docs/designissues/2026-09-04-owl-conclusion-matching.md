# The OWL probe's conclusion matcher: per-triple wildcard vs one mapping

Date: 2026-09-04. Raised in
<https://github.com/danbri/factoidal/issues/652>; it gates the goal in
<https://github.com/danbri/factoidal/issues/651>. Companion to
[`2026-09-04-owl-b1-class-expression-structure.md`](2026-09-04-owl-b1-class-expression-structure.md)
section 6, which recorded the defect and deferred its measurement to
this document, and to
[`2026-09-03-owl-failure-split.md`](2026-09-03-owl-failure-split.md).

Everything below is measured with
`formal/lean4/.lake/build/bin/l4owl-probe` against
`third_party/testing/owl`, per-closure cap 30000 ms, `cap_hits=0` in
every run quoted. Engine commit: `f2988f1e6`, which carries the
`cax-adc` distinct-cell narrowing (`06872bac0`) and the `scm-op` /
`scm-dp` rows (`e64411185`/`cb1883e0f`).

The same four runs were made twice: once on `0f0ad2b7d`, once after a
rebase onto `f2988f1e6`. The RL pair moved from 1158/1156 to 1160/1158
(the two `scm-op`/`scm-dp` units); the `--dl` pair did not move. The
exposure was 2 RL units and 3 `--dl` units in both, and the same two
cases.

## 1. The defect

`Harness/OwlProbe.lean` decided a PositiveEntailmentTest by
`inClosure`:

```lean
def tripleMatches (pat t : Triple) : Bool :=
  subjMatches pat.s t.s && pat.p == t.p && objMatches pat.o t.o
def inClosure (cl : Graph) (pat : Triple) : Bool := cl.any (tripleMatches pat)
```

A conclusion blank node matches ANY term, and the choice is made
independently for each triple. So a conclusion

```
_:x rdf:type C .
_:x rdf:type D .
```

held on a closure with `a rdf:type C` and `b rdf:type D`, with no `a`
that is both. That is not graph entailment.

## 2. What the specifications require

RDF 1.1 Semantics, §1.5, defines an instance with a single mapping:

> "Suppose that M is a functional mapping from a set of blank nodes to
> some set of literals, blank nodes and IRIs. Any graph obtained from a
> graph G by replacing some or all of the blank nodes N in G by M(N) is
> an instance of G."

The word that settles the question is **functional**: `M` gives one
value per blank node, for the whole graph. The same document's
interpolation lemma turns entailment into that search:

> "G simply entails a graph E if and only if a subgraph of G is an
> instance of E."

OWL 2 Conformance states what an entailment test asserts:

> "Entailment tests (or positive entailment tests) specify two ontology
> documents: a premise ontology document d1 and a conclusion ontology
> document d2 where Ont(d1) entails Ont(d2) with respect to the
> specified semantics."

Under the RDF-Based Semantics the conclusion document denotes a graph,
and a triple-containment engine can only demonstrate that entailment by
finding an instance of the conclusion inside the closure. The
per-triple rule does not do that.

**Direction of the correction.** Any single mapping is one of the
assignments the per-triple rule already admits, so the single-mapping
rule is strictly STRONGER. Correcting it can only REMOVE passes from
the positive path. For the negative path the implication runs the other
way: NegativeEntailmentTest passes when the entailment does NOT hold, so
a stronger entailment check can only ADD passes there. The two paths are
not duals and each is measured separately below.

## 3. What landed

`--strict-match` on `l4owl-probe` decides conclusion containment by
`graphInClosure?`: a backtracking search for one `CBind` (a partial map
from conclusion blank-node labels to closure terms) that makes every
conclusion triple a member of the closure. A conclusion blank node is a
variable, never a constant, so a label shared with the closure needs no
renaming.

Three properties of the implementation, none of which changes the
answer:

- If some conclusion triple has no witness at all, there is no mapping;
  the search is skipped.
- If the conclusion has no blank node, the two rules coincide.
- Search order is greedy: ground triples first, then the triple with
  the fewest still-unbound blank nodes and the most already-bound ones.

A step budget (`matchBudget = 100000`) bounds backtracking. Budget
exhaustion is reported as its own failure reason
(`match-budget: the single-mapping search ran out of steps`) rather
than scored as a pass or a silent fail. **It fired 0 times in every run
below**, so no number here is affected by it.

## 4. The exposure, measured

| Regime | Per-triple wildcard | One mapping | Delta |
|---|---|---|---|
| RL closure only | 1160 pass, 287 fail, 2 skip, 8 unsupported (out of 1457) | 1158 pass, 289 fail, 2 skip, 8 unsupported (out of 1457) | −2 units |
| `--dl` | 1294 pass, 153 fail, 2 skip, 8 unsupported (out of 1457) | 1291 pass, 156 fail, 2 skip, 8 unsupported (out of 1457) | −3 units |

The wildcard column is reproduced with `--wildcard-match` on the same
binary, so the delta is the matcher and nothing else.

`cap_hits=0` and `match-budget` hits 0 in all four runs, so no part of
either delta is budget or cap variance. The fail-identifier set after
the change is the set before it plus exactly the rows listed below.

**RL — 2 units, one case, `WebOnt-I5.26-009 [PositiveEntailmentTest]`**
(it scores in `type-positive-entailment.rdf` and in
`type-consistency.rdf`).

**`--dl` — 3 units, one case,
`WebOnt-someValuesFrom-003 [PositiveEntailmentTest]`** (it scores in
three catalogs).

The two cases are disjoint, and the reason is the refutation fallback
of commit `c5890f512`. `WebOnt-I5.26-009` loses its containment pass in
BOTH regimes, but under `--dl` the fallback re-establishes it by
refutation, so only RL records the loss. `WebOnt-someValuesFrom-003`
has no RL containment pass to lose; it passed under `--dl` by
containment over the materialised closure, and the fallback does not
recover it. This is why the two regimes must be measured separately:
the `--dl` positive path decides most cases by refutation, where
blank-node matching does not arise.

### Both cases in detail, from the test files

**`WebOnt-I5.26-009`.** Premise: `<owl:Ontology/>` and
`premises009#p rdf:type owl:ObjectProperty`. Conclusion:

```
_:o rdf:type owl:Ontology .
_:n rdf:type owl:Restriction .
_:n owl:onProperty premises009#p .
_:n owl:minCardinality "1"^^xsd:int .
_:n owl:equivalentClass _:n .
premises009#p rdf:type owl:ObjectProperty .
```

One node `_:n` must carry all four restriction triples. Under the
per-triple rule each of them found its own witness in the closure, so
the case passed without any node being a restriction on `p`. The RL
closure contains no such node and no rule row of the OWL 2 RL tables
mints one, so the correct containment verdict is FAIL.

**`WebOnt-someValuesFrom-003`.** Premise: `person` equivalent to
`ObjectSomeValuesFrom(parent person)`, and `fred rdf:type person`. Its
own description reads "A simple infinite loop for implementors to
avoid." Conclusion:

```
_:o rdf:type owl:Ontology .
premises003#parent rdf:type owl:ObjectProperty .
premises003#fred rdf:type owl:Thing .
premises003#fred premises003#parent _:a .
_:a rdf:type owl:Thing .
_:a premises003#parent _:b .
_:b rdf:type owl:Thing .
```

It asks for a two-step `parent` chain out of `fred` through named
witnesses. No closure of a Datalog rule set produces existential
witnesses, so the per-triple pass was matching `_:a` and `_:b` to
unrelated terms.

## 5. Is the corrected check TOO strict anywhere?

No. The distinction that matters is between "the entailment holds" and
"this engine demonstrates the entailment".

Both cases above ARE entailments under the Direct Semantics: the first
is the tautology `C EquivalentTo C`, the second follows from the
someValuesFrom equivalence. The specification expects a conforming DL
reasoner to answer yes to both. But neither entailment was demonstrated
by anything the harness computed. Each pass came from letting one
conclusion triple pick a witness that another conclusion triple
contradicts, which is a scoring accident that would grant a pass to
conclusions the premise does not entail at all.

So the two rows are not evidence that the single-mapping rule is too
strict. They are two engine gaps that the permissive matcher was
hiding:

- `WebOnt-I5.26-009` — the RL regime cannot mint class-expression
  scaffolding. This is exactly bucket B1 of
  [`2026-09-03-owl-failure-split.md`](2026-09-03-owl-failure-split.md),
  ruled on in the B1 document: comprehension conditions are informative
  in the OWL 2 RDF-Based Semantics, and the DL route is refutation. The
  `--dl` regime already closes it.
- `WebOnt-someValuesFrom-003` — `OWL.NegationGoals.negationGoals`
  returns no goal for a conclusion whose content is an anonymous
  individual chain, so the `--dl` fallback declines it. That is a
  refuter completeness gap, not a matcher defect, and it now shows as
  a failure instead of being masked.

The falsification test for this document is therefore: a case that
fails under `--strict-match` whose conclusion HAS an instance in the
closure. The search is exhaustive within its step budget and the budget
never fired, so no such case exists in this corpus.

## 6. NegativeEntailmentTest, before and after

38 pass, 0 fail (out of 38) in all four runs — RL and `--dl`, wildcard
and single mapping. 6 in `profile-RL.rdf`, 6 in `profile-EL.rdf`, 3 in
`profile-QL.rdf`, 23 in `type-consistency.rdf`.

This is the predicted result, not a coincidence: the negative path
passes when the non-conclusion is NOT contained, a stronger containment
check can only add passes there, and the line was already at 100 %. The
separate NE defect recorded in the B1 document — that NE has no
refutation dual, so a premise that DOES entail its non-conclusion by
refutation still scores PASS — is untouched by this landing and remains
open.

## 7. What the earlier OWL numbers mean

Every OWL score reported before this landing was measured with the
per-triple wildcard and is therefore an UPPER BOUND. In this corpus the
bound was loose by 2 units in RL and 3 units in `--dl`. The corrected
figures in section 4 are the ones to quote. A score that falls when the
check is corrected is the correction, not a regression.

⚠️ **A `--dl` figure of 1233 pass, 214 fail was in circulation on
2026-09-04** as the `claude/main` baseline. Measured here on
`f2988f1e6` with `--wildcard-match`, `claude/main` is 1294 pass, 153
fail (out of 1457). The 1233 line predates the merge of the
PE-via-refutation fallback (`c5890f512`) with the Table 6.5 axiomatic
triples; it was measured in a worktree that carried one and not the
other. The RL line of that report, 1160 pass, 287 fail, is reproduced
exactly.
