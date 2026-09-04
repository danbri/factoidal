# What mature OWL reasoners do that this engine does not

Date: 2026-09-04. A literature and implementation survey, written to
answer one question: which published technique closes the most
remaining OWL tests here for the least risk.

Tracked in <https://github.com/danbri/factoidal/issues/651>.

Companion documents, which hold the measurements this one builds on
and must not be contradicted:

- [`2026-09-03-owl-failure-split.md`](2026-09-03-owl-failure-split.md)
- [`2026-09-04-owl-rl-resplit.md`](2026-09-04-owl-rl-resplit.md)
- [`2026-09-04-owl-shoiq-blocking.md`](2026-09-04-owl-shoiq-blocking.md)
- [`2026-09-04-owl-b1-class-expression-structure.md`](2026-09-04-owl-b1-class-expression-structure.md)

## How to read the claims in this document

Every claim carries one of three tags. Four causal claims were
overturned by measurement on 2026-09-04 — the refuter, the refute
budget, the closure and blocking were each blamed and each exonerated
— so the tags are not decoration.

- **[PUBLISHED]** — a result in a cited paper or a cited reasoner's
  own documentation.
- **[CODE]** — a fact about this repository, read from the source on
  2026-09-04 by inspection, with the file named.
- **[INFERENCE]** — my reasoning about what a technique would do to
  our failures. Not measured. Where I cannot infer with evidence, the
  entry says **unknown**.

No score in this document is new. No suite was run to write it.

## 1. Where the engine stands, and what it is made of

Measured 2026-09-04, recorded in the companion documents:

    OWL RL closure        1173 pass, 274 fail (out of 1457)
    OWL DL tableau (--dl) about 1326 pass, 121 fail (out of 1457)

The engine is two procedures, not one. **[CODE]**

1. **An OWL 2 RL/RDF Datalog closure.**
   `formal/lean4/L4Factoidal/OWL/RLClosure.lean` (1283 lines) is the
   list-backed reference engine; `RLClosureIndexed.lean` (1471 lines)
   is the same rule set over five hash-map buckets. Both iterate
   `step` for a fuel count and stop when a round adds nothing. The
   indexed file's own header states that evaluation is naive with
   indexed joins, not semi-naive, and that there is no rule
   stratification.
2. **A `SHIQ`-shaped tableau.** `OWL/Refute.lean` (1780 lines),
   `tableauConsistent (g : Graph) (budget : Nat) : Option Bool`.
   Depth-first search on a single threaded `Nat` budget.
   `OWL/Tableau.lean` plus `OWL/TableauTheorems.lean` (306 + 280
   lines) hold the declarative calculus used as the proof home.

The whole `L4Factoidal/OWL/` directory is 24,227 lines over 35 files,
plus `Harness/OwlProbe.lean` at 1491 lines. There is no `sorry` and no
`native_decide` anywhere in it. There are 32 `partial def`s, 14 of
them in `Refute.lean` including `search` itself. Mutable state is
confined to `Materialise.lean` (one `StateM`) and to the IO harness.

**Classical tableau optimisations present: none.** Checked by
inspection on 2026-09-04. **[CODE]**

| Technique | State in `Refute.lean` |
|---|---|
| Absorption of general axioms | absent |
| Lazy unfolding of definitions | absent |
| Told subsumers | absent (property closures only) |
| Dependency-directed backtracking (backjumping) | absent — plain chronological DFS, no dependency sets |
| Semantic branching | absent — `tryAll` adds one disjunct per branch and never adds the negation of an earlier disjunct |
| Label-set caching | absent — static data is memoised in `initState`, nothing is keyed on a label set |
| Model merging | absent |
| Blocking of any kind | absent — `maxWitnessDepth = 3` and `maxGeneratedWitnesses = 6` are fuel counters |

There is no consequence-based or completion-style calculus anywhere in
`formal/lean4`. A repository-wide search for `ELK`, `EL++`,
`completion rule` and `consequence-based` returns nothing; every
`saturat*` hit is about the Datalog fixpoint. **[CODE]**

## 2. Consequence-based reasoning

### What it is

A consequence-based (CB) calculus derives the consequences that an
ontology entails, in the way a resolution prover does, but it
organises the derived clauses into **contexts** arranged as a graph,
in the way a tableau organises a model. Each context has a *core* — a
condition satisfied by all elements it represents — and holds
*context clauses* over two special variables. A saturated context
structure is read directly for subsumptions, so one run classifies the
whole ontology instead of one subsumption test per pair. **[PUBLISHED]**
Tena Cucala, Cuenca Grau and Horrocks state this framing directly:

> "CB calculi derive formulae entailed by the ontology (thus avoiding
> the explicit construction of large models) … CB calculi organise
> clauses into contexts arranged as a graph structure reminiscent of
> that used for model construction in (hyper)tableau; this prevents CB
> calculi from drawing many unnecessary inferences and yields a nice
> goal-oriented behaviour. Furthermore, in contrast to both resolution
> and (hyper)tableau, CB calculi can verify a large number of
> subsumptions in a single execution, allowing for one-pass
> classification."
> — *Sequoia: A Consequence-Based Reasoner for SROIQ*, DL 2019,
> <https://ceur-ws.org/Vol-2373/paper-27.pdf>

The line of work, in order:

- Baader, Brandt and Lutz, "Pushing the EL Envelope", IJCAI 2005 — the
  `EL` completion calculus.
- Kazakov, "Consequence-Driven Reasoning for Horn `SHIQ` Ontologies",
  IJCAI 2009, pages 2040–2045,
  <https://www.ijcai.org/Proceedings/09/Papers/336.pdf>. An IJCAI
  Distinguished Paper.
- Simančík, Kazakov and Horrocks, "Consequence-Based Reasoning beyond
  Horn Ontologies", IJCAI 2011,
  <https://www.ijcai.org/Proceedings/11/Papers/187.pdf> — `ALCH`, and
  the first statement of the *context* mechanism.
- Kazakov, Krötzsch and Simančík, "The Incredible ELK", Journal of
  Automated Reasoning 53(1):1–61, 2014,
  <https://link.springer.com/article/10.1007/s10817-013-9296-3> — the
  ELK implementation.
- Bate, Motik, Cuenca Grau, Simančík and Horrocks, "Extending
  Consequence-Based Reasoning to `SRIQ`", KR 2016,
  <http://www.cs.ox.ac.uk/files/8182/paper.pdf>.
- Tena Cucala, Cuenca Grau and Horrocks, "Sequoia: A Consequence-Based
  Reasoner for `SROIQ`", DL 2019 (above), and the journal version,
  "Pay-as-you-go consequence-based reasoning for the description logic
  `SROIQ`", Artificial Intelligence, 2021,
  <https://sciencedirect.com/science/article/abs/pii/S0004370221000692>.

Termination does not need blocking. The calculus never builds a model,
so there is no infinite chain of witnesses to cut. Sequoia's rules are
`Core`, `Hyper`, `Eq`, `Ineq`, `Factor`, `Elim`, `Succ`, `Pred`, plus
`r-Succ`, `r-Pred`, `Join` and `Nom` for nominals. `Succ` reuses an
existing context where it can, which is what bounds the structure.
**[PUBLISHED]**

### Which of our failures it would reach

This is where the evidence is against a large investment, and the
evidence is the CB literature's own account of its weak cases.

**Datatypes: it reaches none of them.** Sequoia "supports all of OWL 2
DL with the exception of datatypes"; its own evaluation had to replace
every data range by a fresh class and every literal by a fresh
individual before it could run. **[PUBLISHED]** Our residual failures
include a large datatype group — the B3 cases named
`Contradicting datatype Restrictions`, `Inconsistent Byte Filler`,
`Minus Infinity is not in owl:real`, `Plus and Minus Zero are
Distinct`, `datatype-restriction-min-max-inconsistency`,
`string-integer-clash`, `inconsistent_datatypes`, plus the four
datatype cases still failing under `--dl` on
`type-inconsistency.rdf`. A CB engine closes zero of these.
**[INFERENCE]**, from a **[PUBLISHED]** limit.

**`-108`: probably not, and for a stated reason.** `-108` is bound by
the ≤-rule's branching over successor pairs, not by budget
(measured 2026-09-04: it still fails at `--refute-budget 4096`). The
Sequoia authors name the same shape as their own worst case:

> "Timeouts mostly occurred on non-Horn ontologies where saturation
> produced many clauses with large numbers of disjuncts in the head …
> These are exacerbated for ontologies where an at-most number
> restriction is applicable to a context with a large number of
> successors for the same role; this leads to the generation of an
> exponential number of clauses with quadratically many equalities in
> the head."
> — Sequoia, DL 2019, §4 Discussion

`-108` is exactly an at-most restriction over a role hierarchy with
nine successors at the merged node. **[INFERENCE]** that CB would not
close it, resting on that **[PUBLISHED]** statement.

**`-035` (nominals): unknown.** Sequoia's `Nom` rule handles nominals,
but the same paper reports that reasoning with nominals "is still hard
for Sequoia", that the calculus "is not worst-case optimal if the
`Nom` rule is triggered (the calculus can then run in triple
exponential time)", and that the seven corpus ontologies which
triggered `Nom` "were very hard for all reasoners". **[PUBLISHED]**
Whether a CB `Nom` rule decides `-035` is **unknown** without running
one.

**`-040`, `-502`, `-909`, `-910`: no.** These are deliberately
exponential 3-SAT and integer-multiplication encodings. A complete
calculus decides them; a CB calculus is complete and is also
exponential on them. Nothing in the literature claims CB makes these
cheap. **[INFERENCE]**

**B1 (class-expression structure), B5 and B7: partly, and it changes
nothing we do not already have.** These buckets are answered here by
refutation over `premise ∪ ¬conclusion`. A CB engine answers
consistency and subsumption, so it would answer the same reduction by
the same reduction. Sequoia "currently supports consistency checking
and classification as reasoning tasks". **[PUBLISHED]** It offers no
new answer shape for a positive entailment whose conclusion our
`negationGoals` cannot negate — and that is the measured largest limit
on `--rl-refute` today: 70 of 177 positive-entailment units produce no
negation goal at all. **[CODE]** A third engine does not fix a missing
negation rule.

**Where CB would help and it is not a conformance win: speed.**
Sequoia's classification times were competitive with HermiT, Konclude,
FaCT++ and Pellet over 777 ontologies, and comparable with ELK on the
48 EL ontologies. **[PUBLISHED]** Our `--dl` corpus run now takes over
50 minutes (reported by the coordinator; the figure recorded in
[`2026-09-04-owl-rl-resplit.md`](2026-09-04-owl-rl-resplit.md) at an
earlier commit was 585 s for the whole corpus and 734 s for the
`--dl` corpus, on a loaded machine). Speed is a real problem here. CB
is one answer to it. It is not the cheapest answer, as §3 argues.

### Cost

Very large. A CB engine is a third reasoning procedure with its own
normalisation to DL-clauses, its own context structure, its own
literal ordering parameter, its own redundancy elimination, and its
own soundness and completeness proof obligations. Sequoia is a
multi-thousand-line Scala system and it still does not do datatypes
after four versions. **[PUBLISHED]** Nothing in our RL claim changes,
because a CB engine sits beside the closure exactly as the tableau
does. That is the one cheap part.

### Lean compatibility

Good, and better than the tableau's. A CB calculus is a monotone
saturation over a finite clause set — the same shape as
`RLClosure.step`, which is already total and proved. Termination is a
finiteness argument over the context structure, not a fuel counter.
The parts that resist a clean Lean statement are the *strategy*
parameters: the literal ordering, the `Succ` expansion strategy (which
context to reuse), and Sequoia's Horn-first two-phase saturation. Each
is a completeness-preserving heuristic in the papers, and each would
have to be either fixed to one concrete choice or carried as a
parameter with a completeness proof that does not depend on it.
**[INFERENCE]**

## 3. Absorption, lazy unfolding and told subsumers

### What they are

**Lazy unfolding** keeps a named concept `A` with definition `A ≡ C`
as the atom `A`, and adds `C` to a node label only when `A` (or `¬A`)
appears there. **Absorption** rewrites a general axiom `C ⊑ D` into
the form `A ⊑ C' ⊔ D` for some atomic `A` on the left, so the axiom
becomes lazily unfoldable instead of being internalised as a
disjunction on every node. Horrocks and Tobies state the pair as the
two techniques that made terminological reasoning practical:

> "Two optimisation techniques that have proved to be effective in
> dealing with terminologies are lazy unfolding and absorption."
> — Horrocks and Tobies, "Reasoning with Axioms: Theory and Practice",
> KR 2000,
> <https://www.cs.ox.ac.uk/people/ian.horrocks/Publications/download/2000/KR-2000.pdf>

**Told subsumers** precompute the subsumptions that are read straight
off the axioms (`A ⊑ B` given, so `A` is told-subsumed by `B`) and use
them to order and to prune classification, without any search. Baader,
Hollunder, Nebel, Profitlich and Franconi, "An Empirical Analysis of
Optimization Techniques for Terminological Representation Systems",
Applied Intelligence 4(2):109–132, 1994. The catalogue and its later
measurements are in Horrocks' thesis, "Optimising Tableaux Decision
Procedures for Description Logics", University of Manchester, 1997,
<https://www.cs.ox.ac.uk/people/ian.horrocks/Publications/download/1997/phd.pdf>,
and in Tsarkov, Horrocks and Patel-Schneider, "Optimizing
Terminological Reasoning for Expressive Description Logics", Journal
of Automated Reasoning 39(3), 2007,
<https://link.springer.com/article/10.1007/s10817-007-9077-y>.
FaCT++ and Pellet both implement absorption and lazy unfolding.
**[PUBLISHED]**

### What our engine does instead

`Refute.lean` holds axioms as raw `(lhs, rhs)` `ClassExpr` pairs from
`collectAxioms`, and `applyAxioms` fires one by structural match of a
node label against the antecedent. It re-scans every node against every
axiom on every round of `onePass`. `injectGlobalAxioms` puts every
axiom whose antecedent is `owl:Thing` onto every node, unconditionally.
There is no unfolding and no absorption. **[CODE]**

That is the shape absorption exists to remove. The `owl:Thing`
injection in particular is the internalisation that absorption avoids:
it puts the axiom's whole consequent — a disjunction, when the axiom
has one — on every node in the expansion, and every such disjunction
becomes a branch point.

### Which of our failures it would close

**Directly: probably none. [INFERENCE]** Absorption and lazy unfolding
do not change what a complete calculus decides. They change how long
it takes. Our residue is not budget-bound: `-108`, `-040`, `-502`,
`-909` and `-910` all still fail at 64 times the default refute
budget, measured 2026-09-04.

**Indirectly: possibly several, and this is the case for doing it.**
The refute budget bounds a search whose branching factor these
techniques reduce. A cheaper branch is not a bigger budget — it is
fewer branches for the same budget. Whether that is enough for any
named case is **unknown**, and it is exactly the kind of claim that
was wrong four times today. The falsifiable prediction is: absorption
changes the number of branches explored on `type-inconsistency.rdf`
and leaves the verdict set unchanged, or it closes cases whose
identifiers must be named in the landing.

**The wall clock is the certain win.** Over 50 minutes for a `--dl`
corpus run is a development-loop cost that is paid on every OWL
change, by every session. Absorption and lazy unfolding are the
published answer to exactly the cost we are paying — eager, repeated,
whole-axiom matching. **[PUBLISHED]** technique, **[INFERENCE]** that
it applies here, resting on **[CODE]** that `applyAxioms` is eager and
per-round.

### Cost

Moderate and contained. Absorption is a preprocessing pass over
`collectAxioms`'s output: partition the axioms into unfoldable
definitions and a residual general set, and rewrite what can be
rewritten. Lazy unfolding is a change to `applyLabelRules` and the
clash check. Both live inside `Refute.lean`.

**It changes no claim we currently make.** The RL closure is not
touched. The tableau's claim today is "no clash found within the
caps", and absorption does not strengthen or weaken it. That is the
property that makes this the low-risk item.

### Lean compatibility

Good. Absorption is a pure syntactic rewrite `List (ClassExpr ×
ClassExpr) → List (ClassExpr × ClassExpr) × List Definition`, total,
with an equisatisfiability obligation that is provable in the style of
the existing `TableauTheorems.lean`. Lazy unfolding is a change to
when a label is added, and its correctness obligation is that the
quiescent state is the same. Neither needs mutable state. Told
subsumers are a precomputed table, the same shape as the existing
`subClosure`/`supClosure` property closures in `RState`. **[INFERENCE]**

## 4. Backjumping, semantic branching and merge caching

### What they are

**Semantic branching** replaces the syntactic `⊔`-rule — try `C₁`,
then try `C₂` — with a split on `C₁` and `¬C₁`, so the two branches
are disjoint and the same clash is never found twice. It comes from
the Davis-Putnam-Logemann-Loveland split and reached description
logics through Horrocks and Patel-Schneider. **Backjumping** is
dependency-directed backtracking: each concept in a node label carries
the set of branch points it depends on, and when a clash is found the
search jumps past every branch point not in that set. Horrocks,
Sattler and Tobies, "Practical Reasoning for Very Expressive
Description Logics", Logic Journal of the IGPL 8(3):239–263, 2000,
<https://www.cs.ox.ac.uk/people/ian.horrocks/Publications/download/2000/HoST00.pdf>
— already cited in `Refute.lean` — describes backjumping as pruning
the tree so that "the number of `R`-successors explored" is reduced by
an exponential factor. FaCT++ implements both. **[PUBLISHED]**

**Merge caching for the ≤-rule.** Steigmiller, Liebig and Glimm,
"Extended Caching, Backjumping and Merging for Expressive Description
Logics", IJCAR 2012, LNCS 7364, pages 514–529,
<https://link.springer.com/chapter/10.1007/978-3-642-31365-3_40>,
combine dependency management with an unsatisfiability cache and
report that this "optimises the handling of cardinality
restrictions". This is the published technique aimed at our named
`-108` failure. **[PUBLISHED]**

### Which of our failures it would close

**`-108` is the target, and the evidence points here rather than at
CB.** `-108` is measured as bound by the ≤-rule's pair branching, not
by budget. Our ≤-rule enumerates every mergeable pair at every level,
requires every branch to clash, and re-derives the same clash in
sibling branches because nothing records why the last one failed.
**[CODE]** Backjumping plus an unsatisfiability cache is precisely the
published remedy for that pattern. **[INFERENCE]** that it would close
`-108`; **unknown** with confidence, and it must be measured, not
predicted.

One related measurement already exists and is negative: halving the
branching factor by enumerating each unordered merge pair once changed
no verdict at budget 64 or at budget 4096
([`2026-09-04-owl-shoiq-blocking.md`](2026-09-04-owl-shoiq-blocking.md)).
A constant-factor reduction is not enough. Backjumping is not a
constant factor — it removes whole subtrees — but that measurement is
a warning that the ≤-rule's cost here is dominated by successor count.

`-040`, `-502`, `-909`, `-910`: **unknown**, and unlikely. These are
built to be exponential.

### Cost

Backjumping is the most invasive of the techniques in this document.
Every concept in every node label must carry a dependency set, so
`RNode.labels : List ClassExpr` becomes a labelled structure and every
rule that adds a label must compute the dependency set correctly. An
incorrect dependency set does not crash — it prunes a branch that
contained the only model, and turns a consistent ontology into a
refutation. That is a soundness failure in the dangerous direction.

Semantic branching is much smaller: it is a change to `tryAll` in
`search`, adding `nnfNeg` of the earlier disjuncts to the later
branches. `nnfNeg` already exists.

Neither changes any claim about the RL closure.

### Lean compatibility

Semantic branching: good. It is a change to which labels a branch
gets, and `nnfNeg` is already total.

Backjumping: workable but expensive to prove. The dependency sets are
functional data, not mutable state, so a total Lean implementation is
possible. The obligation is that pruning a branch does not lose a
model, and that obligation is the whole content of the technique.
Getting it wrong is silent. **[INFERENCE]** This is the one technique
here whose risk is a wrong answer rather than a wasted session.

## 5. Nominal rules for `SHOIQ` — the `NN`-rule and the `o`-rule

Horrocks and Sattler, "A Tableau Decision Procedure for `SHOIQ`",
Journal of Automated Reasoning 39(3):249–276, 2007, extends `SHIQ` with
nominals. Nominals break the tree shape every blocking argument
assumes, because a nominal node is reachable from any depth. The paper
recovers termination by treating nominal nodes as root nodes, outside
the blocking relation, and bounding their number with the `NN`-rule;
the `o`-rule identifies two nodes that carry the same nominal.
**[PUBLISHED]** This is already the citation in
[`2026-09-04-owl-shoiq-blocking.md`](2026-09-04-owl-shoiq-blocking.md).

Our engine's `isMergeableTerm` accepts blank nodes only, so a named
individual is never identified with anything, and the rule cannot fire
at all. **[CODE]** That is why `-035` — a spy point with `≤2 invP`
that must force the domain down to two elements — is withheld.

Which failures: `WebOnt-description-logic-035` by name, and it is a
single unit. **[INFERENCE]**, from the case analysis already recorded.
Whether other withheld `owl:oneOf` cases follow is **unknown**.

Cost: a new rule family plus the root-node treatment, and it weakens
what a `some true` verdict may claim until the termination argument is
redone for the nominal case. Lean compatibility: the rules are
functional; the termination argument is the hard part and it is the
same hard part as blocking. One unit is a poor return for it.

## 6. Datatype satisfiability

Motik and Horrocks, "OWL Datatypes: Design and Implementation", ISWC
2008, LNCS 5318, pages 307–322,
<https://www.cs.ox.ac.uk/people/boris.motik/pubs/mh08datatypes.pdf>,
gives the reference treatment. Two results matter here. First,
datatype checking in OWL 2 is **NP-hard in the general case**, and the
paper says so explicitly, while noting it "may become trivial in many
(hopefully typical) cases". Second, the algorithm is **modular**: it
supports any datatype for which a small set of operations — a
*datatype handler* — can be implemented, and the tableau invokes the
handler as an oracle. **[PUBLISHED]** Reasoners take the oracle route:
Sequoia does not implement datatypes at all; Konclude and HermiT do.

Our engine has a value-space lattice, not an oracle.
`foldDatatypeConstraint` in `Refute.lean` folds a class expression
into a `ValueSet` — `unconstrained | interval | dense | dateInterval |
enum | family | empty` — and `datatypeRangeClash` reports emptiness.
`owl:oneOf` over literals and `owl:datatypeComplementOf` are handled.
Only four facets are supported: `xsd:minInclusive`, `xsd:maxInclusive`,
`xsd:minExclusive`, `xsd:maxExclusive`. There is no `pattern`, no
`length` family, no `langRange`, and no general constraint solver.
Unrecognised shapes leave the accumulator untouched, so the engine
withholds rather than fabricates. **[CODE]**

Which failures: the datatype group inside B3 — `Contradicting datatype
Restrictions`, `Contradicting-dateTime-restrictions`,
`Datatype-Float-Discrete-001`, `Different types in Datatype
Restrictions and Complement`, `Inconsistent Byte Filler`,
`Inconsistent Data Complement with the Restrictions`, `Inconsistent
String Pattern with Disjoint Dataproperties`, `Minus Infinity is not
in owl:real`, `New-Feature-Rational-002`, `Plus and Minus Zero are
Distinct`, `datatype-restriction-min-max-inconsistency`,
`inconsistent_datatypes`, `string-integer-clash` — plus the four
datatype cases still failing under `--dl`. **[INFERENCE]** that a
handler interface with `pattern` and the string facets reaches the
string-pattern cases; **unknown** how many of the numeric ones are
already reachable by extending the existing lattice instead.

The cheaper move is visible from the code: the lattice is one facet
family away from several of these, and extending
`XSD/Facets.lean` is a bounded change inside a file that already
carries the value-space vocabulary. That is not the full Motik-Horrocks
oracle. It does not need to be.

Cost: contained, and it changes no claim. Lean compatibility: good —
value sets are pure data and the existing operations are total, with
`valueSetMaxSize` already an over-approximation that only ever
withholds a clash.

## 7. Three techniques the literature offers that this list missed

**Hypertableau.** Motik, Shearer and Horrocks, "Hypertableau Reasoning
for Description Logics", Journal of Artificial Intelligence Research
36:165–228, 2009, <https://arxiv.org/pdf/1401.3485>, is the HermiT
calculus. It translates axioms into DL-clauses and expands by
hyperresolution, which removes most of the disjunctive branching that
general axioms cause in a standard tableau, and it uses *anywhere*
blocking rather than ancestor blocking, which reduces model size.
**[PUBLISHED]** It is a different calculus from ours, not an
optimisation of ours. Adopting it means rewriting `Refute.lean`.

**Coupling saturation with the tableau.** Steigmiller and Glimm,
"Pay-As-You-Go Description Logic Reasoning by Coupling Tableau and
Saturation Procedures", Journal of Artificial Intelligence Research
54:535–592, 2015,
<https://jair.org/index.php/jair/article/view/10970/26117>, is what
Konclude does: a completion-based saturation runs on the tableau's own
data structures, and its results let the tableau skip expansion.
Steigmiller, Liebig and Glimm, "Konclude: System Description", Journal
of Web Semantics 27:78–85, 2014. **[PUBLISHED]**

This is architecturally the closest published system to what we
already have — a saturation and a tableau in one engine — and it is
the strongest argument in this document *against* building a third
engine. Konclude's answer to "saturation is fast, tableau is general"
was to make them share structures, not to add a third procedure.
**[INFERENCE]** that our `--rl-refute` regime is a coarse version of
the same idea: the closure runs, then the tableau runs on the closure.
The refinement Konclude adds is that the saturation's result *prunes*
the tableau, and ours does not.

**Modular delegation.** Armas Romero, Cuenca Grau and Horrocks,
"MORe: Modular Combination of OWL Reasoners for Ontology
Classification", ISWC 2012,
<http://www.cs.ox.ac.uk/files/4873/ModularClassificationISWC.pdf>,
extracts the module of an ontology that a profile reasoner can
classify completely, and gives only the residue to the expressive
reasoner. **[PUBLISHED]** Not applicable to our corpus: the W3C OWL
test cases are tiny, and delegation is a scale technique.

**One item that is not in the literature and is the largest measured
limit we have.** Of the 177 positive-entailment units the closure
failed, **70 produced no negation goal at all** — `OWL.NegationGoals`
does not negate that conclusion shape, so the refuter never asked the
question. Zero exhausted the budget. **[CODE]**, measured and recorded
in [`2026-09-04-owl-rl-resplit.md`](2026-09-04-owl-rl-resplit.md).
`NegationGoals.lean` is 353 lines. No reasoner technique closes those
70. Writing the missing negation cases does.

## 8. Ranked recommendation

Ranked by tests closed per unit of risk. Risk means: probability of a
wrong answer, plus the size of the claim that changes.

### First — extend `OWL.NegationGoals` to the unhandled conclusion shapes

Not a reasoner technique, and that is why it is first. 70 of 177
failed positive-entailment units never reach the refuter because the
harness cannot state the question. **[CODE]**, measured. The shapes
are named: a named-subject `owl:unionOf` axiom over `owl:oneOf`
classes (`WebOnt-unionOf-003`), an `owl:hasSelf` restriction assertion
(`New-Feature-SelfRestriction-002`), the two
`New-Feature-Disjoint*Properties-002` cases, `WebOnt-I5.5-005` and
`WebOnt-I4.6-005-Direct` at five units each, and about thirty cases at
two units each.

Cost: one file, 353 lines today. Changes no claim — the file's header
already carries the soundness contract that each content assertion is
negated separately and an unsupported shape collapses to `none`. Risk
of a wrong answer: low, and the existing gates catch it
(`refuter_flips_to_fail`, and the 38 NegativeEntailmentTest units).
Highest expected units per session-day of any item here.

### Second — absorption and lazy unfolding in `Refute.lean`

The `--dl` corpus run takes over 50 minutes, and `applyAxioms` re-scans
every node against every axiom every round with no unfolding and no
absorption. **[CODE]** This is the exact cost the KR 2000 technique
was written for. **[PUBLISHED]**

It buys development-loop speed with certainty and test closures
without any. Put the speed first in the justification, and state the
prediction honestly: the verdict set may not move. It changes no
claim, it is contained in one file, and its failure mode is a slower
engine, not a wrong one.

Land it with semantic branching in the same workstream if the session
allows — semantic branching is a small change to `tryAll` and
`nnfNeg` already exists — but measure them separately, or neither
delta is attributable.

### Third — extend the datatype value-space lattice in `XSD/Facets.lean`

Thirteen-plus named B3 cases are datatype cases, and the lattice
supports four facets. **[CODE]** Extending it is bounded, changes no
claim, and its withholding-only failure mode is already established
(`valueSetMaxSize` over-approximates by design). Do not build the full
Motik-Horrocks datatype-handler oracle first; measure how far the
lattice goes, then decide.

### Fourth — backjumping with an unsatisfiability cache, aimed at `-108`

The published remedy for our named ≤-rule failure. **[PUBLISHED]**
Ranked fourth, not higher, because its failure mode is a soundness
failure in the dangerous direction: a wrong dependency set prunes the
branch holding the only model and reports a refutation. It needs its
own proof obligation, and the ConsistencyTest line (762 units) is the
gate that would catch it.

### Not ranked, and the reasoning is in §9

Consequence-based reasoning. Nominal `NN`/`o` rules. Pairwise blocking
(already measured as not the lever). Hypertableau. Modular delegation.

## 9. Is a consequence-based calculus a better route than extending the tableau?

**No, not now.** Four pieces of evidence, in order of force.

1. **It reaches none of our datatype failures, by its own account.**
   Sequoia supports all of OWL 2 DL "with the exception of datatypes",
   after four released versions, and had to erase every data range
   from its evaluation corpus to run. **[PUBLISHED]** A substantial
   part of our residue is datatypes. A new engine that cannot see them
   is not the engine our failures ask for.

2. **Its published worst case is our named worst case.** The Sequoia
   authors name at-most number restrictions over a context with many
   successors of the same role as the shape that produces "an
   exponential number of clauses with quadratically many equalities in
   the head". **[PUBLISHED]** `WebOnt-description-logic-108` is that
   shape. Building CB to close `-108` bets against the paper.

3. **It answers the same two questions our tableau already answers.**
   Sequoia's reasoning tasks are consistency checking and
   classification. **[PUBLISHED]** Our positive-entailment failures are
   reduced to consistency of `premise ∪ ¬conclusion`, and the measured
   bottleneck in that reduction is that 70 units never produce a
   negation goal. **[CODE]** A CB engine inherits that bottleneck
   unchanged, because the bottleneck is upstream of the decision
   procedure.

4. **The system that faced our exact architecture chose coupling, not
   a third engine.** Konclude has a saturation procedure and a tableau
   in one reasoner, and the published design makes the saturation
   share the tableau's data structures so it can prune the tableau's
   expansion. **[PUBLISHED]**, Steigmiller and Glimm, JAIR 54, 2015.
   We have a closure and a tableau, and `--rl-refute` already runs one
   after the other. Tightening that coupling is a smaller step than
   building a CB engine and it targets the same cost.

The argument **for** CB, stated fairly so a later session can reopen
it: CB is a monotone saturation, which is a better fit for a total,
`sorry`-free Lean implementation than a tableau with blocking is. Its
termination is a finiteness argument, not a fuel counter, and we still
carry a fuel counter (`maxWitnessDepth = 3`) where the mathematics
wants blocking. **[INFERENCE]** If the goal ever becomes *classification
speed on large real ontologies* rather than *W3C conformance units*,
CB becomes the right answer, and ELK's and Sequoia's measured results
are the evidence for it. That is a different goal from the one on the
table.

**Conditions that would reopen this.** Any one of them:
(a) the datatype work lands and datatypes stop being a large share of
the residue; (b) a measured need for classification over an ontology
where the tableau does not terminate in useful time; (c) a decision
that the fuel counter in `Refute.lean` must be retired and pairwise
blocking proves harder to state in Lean than a CB termination
argument.

## 10. Techniques judged not worth doing here

**Consequence-based reasoning as a third engine.** §9. The largest
commitment in this document, and it reaches neither the datatype
group nor `-108`, by the CB literature's own statements.

**The `NN`-rule and the `o`-rule for nominals.** One named unit,
`WebOnt-description-logic-035`. The rules require the root-node
treatment that takes nominal nodes outside the blocking relation, and
they weaken what a `some true` verdict may claim until the termination
argument is redone. **[PUBLISHED]** cost, one **[INFERENCE]** unit of
return. Revisit only if a second nominal case is found.

**Pairwise blocking, as a way to close tests.** Already measured as
not the lever: `maxWitnessDepth` 3 → 8 leaves
`type-inconsistency.rdf` byte-identical. Blocking is still worth doing
to replace a fuel counter with a theorem and to let `some true` mean
satisfiable on the `SHIQ` fragment, and
[`2026-09-04-owl-shoiq-blocking.md`](2026-09-04-owl-shoiq-blocking.md)
says so. A session that does it must not expect the score to move.

**Hypertableau.** A different calculus, not an optimisation of ours.
It would replace `Refute.lean` and every theorem in
`TableauTheorems.lean`. Its benefits — less disjunctive branching from
general axioms, smaller models from anywhere blocking — overlap
substantially with what absorption and semantic branching buy inside
the calculus we have. **[INFERENCE]**

**Modular delegation (MORe).** A scale technique for large real
ontologies. The W3C OWL test cases are tiny. It would close nothing.

**Told subsumers.** They accelerate classification, and we do not run
classification as a task — the probe answers consistency and
entailment per test case. They would close nothing here.
**[INFERENCE]** Worth revisiting if a classification task is ever
added.
