# OWL Phase 5 — restriction-bnode equivalence + `allValuesFrom` scoping

Dated 2026-04-24. Continues the arc of
[`2026-04-24-owl-session-notes.md`](2026-04-24-owl-session-notes.md).
This doc scopes a single agent's attempt at the 5 still-failing SPARQL
entailment tests: `simple 2`, `3`, `5`, `6`, `8`. Only F\* is edited;
the main thread rebuilds.

## Test-by-test analysis

All 5 queries select individuals under a complex OWL class expression.
The data is a flat ABox from `simple.ttl`: individuals `:a`, `:b`, `:c`, `:d`
linked by a chain `:a :p :b`, `:b :p :c`, `:c :p :d`, with typed memberships
in named classes `:A`, `:B`, `:C`.

| Test | Query CE | Expected | Current closure gap |
|---|---|---|---|
| `simple 2` | `intersectionOf(:A, [Restriction, onProperty :p, someValuesFrom :B])` | `:a` | Query's syntactic restriction bnode is not bridged to the closure's canonical `__rl_svf_:p__on__:B`. BGP never binds. |
| `simple 3` | `Restriction someValuesFrom [intersectionOf(:A,:B)]` | `:c` | `cls-svf2-qualified` only accepts IRI fillers. Bnode CE filler is skipped. |
| `simple 5` | `Restriction someValuesFrom [unionOf(:A,:B)]` | `:a, :b, :c` | Same as simple 3 but union filler. |
| `simple 6` | `Restriction allValuesFrom [unionOf(:A,:B,:C)]` | `:a, :b, :c` | No `cls-avf` rule exists. Filler is also a union bnode. |
| `simple 8` | `Restriction someValuesFrom [Restriction someValuesFrom :B]` | `:b` | Nested restriction filler. Closure must create canonical-for-canonical. |

## Attempt plan for this commit (scope-controlled)

Priority dictated by closure-reachable entailment under OWL-RL:

### 1. `simple 2` — restriction-bnode equivalence bridge  (attempt)

**Rule** `owl_rule_restriction_equivalence_bridge`:

For every data-side restriction bnode `_:r` with
`(_:r rdf:type owl:Restriction) ∧ (_:r owl:onProperty P) ∧
(_:r owl:someValuesFrom C)` where `P, C` are IRIs, emit:

```
_:r rdfs:subClassOf __rl_svf_P__on__C
__rl_svf_P__on__C rdfs:subClassOf _:r
```

The canonical `__rl_svf_P__on__C` carries the same structural shape
and is populated via `cls-svf2-qualified`. Linking the two via
`rdfs:subClassOf` both-ways (cheaper and scoped-narrower than
`owl:equivalentClass`, which triggers further rewrites) lets the
existing RDFS closure propagate type membership both directions:
`:a a canonical → :a a _:r`. Under OWL-Direct query evaluation the
query's syntactic bnode `_:r` is rewritten to a variable (or matched
directly, depending on the rewriter); either way the derived
`:a rdf:type _:r` triple is present.

Note this rule fires only when the data graph has a
`someValuesFrom`-style restriction bnode that matches a canonical we
ALREADY materialised. It is therefore non-expansive and terminates.

### 2. `simple 6` — `allValuesFrom` rule  (defer)

The session notes flag this as needing `cls-avf1`:
`C owl:allValuesFrom D ∧ C owl:onProperty P ∧ x a C ∧ x P y → y a D`.

Problem: the filler `D` in simple 6 is a union bnode. Deriving
`y a unionBnode` does not, under OWL-RL, let us propagate
`y a :A ∨ y a :B ∨ y a :C` — disjunction is not Datalog-expressible.
And the query asks for bindings of `?x` — it expects `:a, :b, :c`,
each of which has a `:p` successor typed in at least one of A/B/C.
Making the closure materialise the existential universally-accessible
for those 3 individuals requires rewriting the query, not closing
the ABox.

**Decision**: do not attempt simple 6 in this commit. Note it as
query-rewriter work for the agent currently in `OWL.QueryRewrite`.

### 3. `simple 3` — intersection filler  (defer to rewriter)

The filler is a query-side bnode `[intersectionOf (:A :B)]`. Under
Direct Semantics the rewriter should unfold this into a conjunctive
BGP. Agent `ad43763d` is in `OWL.QueryRewrite` now; they own nested
filler expansion.

Closure-side alternative: extend `cls-svf2-qualified` to iterate over
y's types AND over y's membership in intersection/union CE bnodes
whose operands are in y's types. Cost is bounded but the rule set
starts to grow unwieldy. Skip for this commit.

### 4. `simple 5` — union filler  (defer)

Same reasoning as simple 3. Union in `someValuesFrom` position is a
disjunction on the filler; the closure cannot eliminate the bnode
without query-side rewriting.

### 5. `simple 8` — nested restriction  (defer)

Needs canonical-for-canonical materialisation. Would follow naturally
from the restriction-equivalence bridge if the canonical carried full
restriction shape, but chaining across multiple levels is its own
commit.

## What lands in this commit

Just #1 — the restriction-equivalence bridge, targeted at `simple 2`.

If F\* verifies, we commit and let the main thread rebuild. If F\*
errors out on the new rule, we revert and ship only the scoping doc.

No `admit()`, no `--lax`. No edits to `OWL.QueryRewrite.fst` or
`SPARQL11.Algebra.fst` (other agents are in those files).

## Out of scope for Phase 5 entirely

- `paper-sparqldl-Q3` — needs Tableau stage (c) cardinality.
- Disjunction in query position — needs OWL-Direct tableau, not RL.
