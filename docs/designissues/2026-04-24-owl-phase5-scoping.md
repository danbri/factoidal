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

## 2026-04-24 update — root cause found (the REAL reason simple 1..8 all fail)

Ran the current `w3c_runner` binary and captured the post-rewrite BGPs
via `FACTOIDAL_DEBUG_OWL_REWRITE=1`. The failure mode is NOT
"rewriter handles flat but not nested". It's deeper:

**The SPARQL parser emits `[ ... ]` bnode-with-properties as a TREE OF
JOINS, not one BGP.** Observed on simple 1:

```
(join
  [BGP: ?x type ?_bnode_c]
  (join
    [BGP: ?_bnode_c intersectionOf ?_bnode_list]
    (join
      [BGP: ?_bnode_list first :A ; rest ?_bnode_list2]
      [BGP: ?_bnode_list2 first :B ; rest rdf:nil] )))
```

`OWL.QueryRewrite.rewrite_bgp_nested` operates on a SINGLE BGP. It
never sees the intersectionOf marker alongside its consumer, so
`find_markers` returns `[]` for each sub-BGP and the rewrite is a
no-op. The debug log confirms: "rewrite changed pattern? **false**"
for simple1/4/7 too — flat and nested alike. The Phase 3 "pass"
attribution for simple1/4/Q2 in the session notes must have been
observed in an earlier build before some other change split the
BGPs, OR the parser has changed behaviour recently. **Current
snapshot (commit 76a6ded binary): simple 1/2/3/4/5/6/7/8 all fail.**

This means:
- **My original Option B (`owl:equivalentClass` between data-side
  restriction bnodes and canonicals) fixes nothing** — the query has
  no data-side restriction bnode to bridge from; the entire CE lives
  in the query and gets split into joined BGPs.
- **The root fix must flatten joined BGPs before the rewriter runs**,
  in `OWL.QueryRewrite.fst` (or in a pre-rewrite pass in
  `OWL.QueryEval.fst`). That is out of scope for THIS commit — agent
  `ad43763d` is in `OWL.QueryRewrite.fst` per the task description,
  and `SPARQL11.Algebra.fst` is locked by another agent.

### What I will still attempt in F\* closure-only work

- **Add `cls-avf1` rule** for `allValuesFrom` (simple 6). Does not
  depend on the rewriter. Harmless even if the rewriter fails to
  produce matching query patterns (the rule only ADDS type-membership
  triples the way `cls-svf2-qualified` does). If F\* verifies the
  rule cleanly, commit it.

### What I will NOT attempt

- simple 2/3/5/8 — all blocked on the rewriter BGP-flattening fix.
  Adding closure rules without the rewriter fix moves no tests.

### Recommendation to the rewriter agent

In `OWL.QueryRewrite.rewrite_ggp`, before delegating to
`rewrite_bgp_nested`, walk the GGP tree and coalesce adjacent
`GP_BGP` / `GP_Join` subtrees into a single BGP **when every leaf is
a BGP**. That is sound under SPARQL semantics (join of BGPs is BGP
concatenation) and exposes the cross-BGP `intersectionOf` /
`unionOf` / `someValuesFrom` markers to the existing rewriter.

```fstar
// Sketch:
let rec collect_bgp_leaves (g : group_graph_pattern)
  : option bgp (* None if non-BGP/join leaf *) =
  match g with
  | GP_BGP b -> Some b
  | GP_Join a b ->
    (match collect_bgp_leaves a, collect_bgp_leaves b with
     | Some ba, Some bb -> Some (List.Tot.append ba bb)
     | _ -> None)
  | _ -> None

// in rewrite_ggp:
match collect_bgp_leaves g with
| Some merged -> rewrite_bgp_nested merged
| None -> /* existing recursion */
```

This should unblock simple 1/4/7 immediately, then the existing
machinery handles their body. simple 2 additionally needs the
restriction-bnode case in `expand_ce_subject` (treat a bnode operand
whose triples-in-BGP describe a Restriction as the canonical
`__rl_svf_P__on__C` IRI).
