# Q6 Deep Dive: OPTIONAL + ORDER BY on UK Parliament COTTAS

Date: 2026-05-02

Query under investigation:

```sparql
PREFIX : <https://id.parliament.uk/schema/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

SELECT ?Legislature ?LegislatureName ?House ?HouseName
WHERE {
  ?House a :House .
  OPTIONAL { ?House :houseName ?HouseName . }
  OPTIONAL { ?House rdfs:label ?HouseName . }
  OPTIONAL { ?House :name      ?HouseName . }
  OPTIONAL {
    ?House :houseInLegislature ?Legislature .
    OPTIONAL { ?Legislature rdfs:label ?LegislatureName . }
    OPTIONAL { ?Legislature :name      ?LegislatureName . }
  }
}
ORDER BY ?LegislatureName ?HouseName
LIMIT 20
```

## Live Behavior

From the live Fly `/admin/recent.json` buffer:

- `status = 504`
- `parse_ms = 0.00`
- `eval_ms = 29999.75`
- `format_ms = 0.00`
- `total_ms = 29999.75`

So this is a pure evaluator/runtime problem, not parse or formatting.

## Algebra Shape

`--explain-only` lowers the query to:

```text
Project [?Legislature, ?LegislatureName, ?House, ?HouseName]
  Slice limit=20
    OrderBy [...]
      LeftJoin (OPTIONAL)
        LeftJoin (OPTIONAL)
          LeftJoin (OPTIONAL)
            LeftJoin (OPTIONAL)
              BGP
                ?House rdf:type :House
              BGP
                ?House :houseName ?HouseName
            BGP
              ?House rdfs:label ?HouseName
          BGP
            ?House :name ?HouseName
        LeftJoin (OPTIONAL)
          LeftJoin (OPTIONAL)
            BGP
              ?House :houseInLegislature ?Legislature
            BGP
              ?Legislature rdfs:label ?LegislatureName
          BGP
            ?Legislature :name ?LegislatureName
```

Important consequence:

- `LIMIT 20` sits above `OrderBy`
- `OrderBy` sits above the entire `LeftJoin` tree
- therefore the current `LIMIT` pushdown fast path cannot apply

## Current Fast Paths Do Not Apply

The engine currently has useful shortcuts for:

- streaming `COUNT(*)`
- streaming `COUNT(*) GROUP BY ?g`
- single-triple-pattern `LIMIT` pushdown

Q6 matches none of those shapes.

Relevant code:

- `formal/fstar/SPARQL11.Store.fst`
  - `detect_streaming_count_star`
  - `detect_streaming_count_group_by_graph`
  - `detect_limit_single_tp`
  - `eval_limit_single_tp`

## Explain Findings: Several OPTIONAL Branches Are Provably Empty

The explain pass already shows:

- `?House :name ?HouseName` -> estimate `0`, predicate absent
- `?House :houseInLegislature ?Legislature` -> estimate `0`, predicate absent
- `?Legislature :name ?LegislatureName` -> estimate `0`, predicate absent

So three OPTIONAL branches are known-empty against this corpus snapshot.

That is valuable because:

- semantically, `LeftJoin(left, empty) = left`
- operationally, the current evaluator still enters these branches as ordinary
  `GP_LeftJoin` subpatterns instead of short-circuiting them away

## Structural Bottleneck #1: Eager OPTIONAL Evaluation

Backend path today:

- `eval_pattern_backend` in `formal/fstar/SPARQL11.Store.fst`
- for `GP_LeftJoin p1 p2 filter_e` it does:

```text
left_join (eval_pattern_backend p1 ...) (eval_pattern_backend p2 ...) filter_e
```

And `left_join` in `formal/fstar/SPARQL11.Algebra.fst` is:

```text
for each mu1 in omega1:
  scan all mu2 in omega2
  keep compatible merges
  if none, keep mu1
```

This means:

1. The entire right-hand OPTIONAL side is materialized up front.
2. Join compatibility is checked via nested-loop scans.
3. Shared-variable restriction from the left side is not pushed into the right
   side before right-side evaluation.

For Q6 that is disastrous, because branches like:

- `OPTIONAL { ?House rdfs:label ?HouseName . }`

are evaluated globally, not “for the current `?House`”.

## Structural Bottleneck #2: LIMIT Cannot Help Early

Because of the algebra shape:

- base BGP expands to many `?House`
- OPTIONAL branches add more rows / bindings
- ORDER BY requires materializing/sorting the candidate sequence
- only then can `LIMIT 20` cut the tail

So even though the user asks for 20 rows, the engine may need to build and sort
far more before the limit becomes effective.

## Structural Bottleneck #3: Planner Is Too Coarse for This Shape

Earlier investigations already showed that planner estimates often tie at coarse
row-group granularity and then fall back to input order.

For Q6, the problem is even bigger:

- each OPTIONAL branch is its own single-triple BGP
- branch-local estimates do not express global left-join cost
- there is no strong policy yet for:
  - skipping known-empty OPTIONAL branches
  - preferring correlated evaluation over global right-side materialization
  - minimizing intermediate row width before ORDER BY

## What This Means

Q6 is currently slow for three separate reasons at once:

1. No applicable fast path.
2. Eager `LeftJoin` semantics on fully materialized right sides.
3. LIMIT above ORDER BY, so the result bound does not reduce early work.

The timeout is therefore expected with the current architecture.

## Best Immediate Improvement Candidates

### Candidate A: Skip provably empty OPTIONAL branches

Low-risk, semantics-preserving optimization:

- if explain/planner machinery can prove `p2` is empty for all bindings,
  replace `LeftJoin(p1, p2)` with `p1`

For this exact Q6 snapshot, that would eliminate three branches immediately.

### Candidate B: Correlated OPTIONAL evaluation for backend path

Higher-value, higher-risk optimization:

- for backend `GP_LeftJoin`, evaluate `p1` first
- for each `mu1`, evaluate `substitute_pattern mu1 p2`
- then do left-join assembly locally per left row

This is much closer to what a human expects for:

- `OPTIONAL { ?House rdfs:label ?HouseName }`

and avoids materializing all labels in the corpus when only labels compatible
with current `?House` bindings matter.

This looks like the most important medium-term performance improvement for
Parliament-style queries.

### Candidate C: Add execution tracing around OPTIONAL / LEFT JOIN

Before changing semantics, instrument:

- left input row count
- right input row count
- compatible merge count
- unmatched-left count

That would let `/admin` and local tracing show whether a query is failing due to:

- huge right-side materialization
- huge compatibility scans
- sort-before-limit pressure

## Recommended Next Step

1. Add durable tracing for backend `GP_LeftJoin`.
2. Add a narrow optimization for provably empty OPTIONAL branches.
3. Re-test Q6.
4. If still too slow, implement correlated backend OPTIONAL evaluation.
