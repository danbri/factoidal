# Tav2 — parent7 finish: SELECT * projects rewritten-bnode existentials (2026-04-25)

## Symptom

After Tav's wider `is_schema_metapredicate` gate (Wave 15, HEAD `2ed10a8`),
parent7 still FAILs with **311 actual rows** vs 1 expected. The expected SRX
projects ONE column `?parent`, the actual rows project TWO columns:
`?_bnode__:bnode_18` and `?parent`.

Sample of the leak (verbose runner output, see `/tmp/parent7_verbose.log`):

```
?parent=<http://example.org/test#Dudley>          <-- the only row expected
ACTUAL (311 rows):
  ?_bnode__:bnode_18=owl:Thing,    ?parent=rdfs:domain
  ?_bnode__:bnode_18=owl:Thing,    ?parent=rdfs:range
  ?_bnode__:bnode_18=owl:Class,    ?parent=:Female
  ?_bnode__:bnode_18=_:_anon7,     ?parent=:Dudley
  ...
```

The variable `?_bnode__:bnode_18` is the **rewriter-introduced synthetic
variable** for the blank node `[ a owl:Restriction ; ... ]` in the WHERE
clause. parent7 uses bracketed-bnode property-list syntax; the rewriter
in `SPARQL11.Algebra.fst` (`rewrite_query_bnodes_pattern`, called from
`eval_select_query` line 3589) turns `PT_BNode b` / `PS_BNode b` into
`PT_Var ("_bnode_" ^ b)` / `PS_Var (...)` so blank nodes act as
existentials.

The same rewrite was added in OCaml patch
`53_blank_node_variable_rewriting.sh` (#53) — that patch is now redundant
with the F\*-side rewriter and is only kept for legacy compatibility.

## Root cause (revised)

`SELECT *` returns ALL variables in scope of the WHERE clause's solution
mappings. After bnode-existential rewriting, the mapping carries the
synthetic `?_bnode_<label>` keys alongside the user-named variables.
`eval_select_query` line 3656:

```fstar
let projected = match sel with
  | Select_Vars items -> project_solutions (select_item_vars items) ordered
  | Select_All -> ordered      <-- ordered carries _bnode_* keys
```

Per SPARQL 1.1 §18.2.4 ("OutScope of variables"), `*` denotes the set
of in-scope variables of the WHERE clause. The original query's blank
nodes are NOT variables, so post-rewrite synthetic variables they map
to are NOT in the user's "in-scope" set. Returning them as columns:

1. inflates the row count (every distinct binding of the synthetic
   variable creates a new row),
2. makes the SRX comparison fail (extra column = no match),
3. leaks implementation detail (skolem labels) into user output.

Tav's wider `is_schema_metapredicate` correctly tightened the closure rules,
but the leak that remained was projection-side, not closure-side. The over-
count from 954 → 311 was the closure-side improvement; the residual 311
rows are **all 1 row × |bindings of ?_bnode_18|**, plus join multiplicities
where multiple synthetic variables coexist (parent7 has only one bnode in
the query, so it's purely the binding fan-out).

## Fix (F\*-only)

In `SPARQL11.Algebra.fst`:

1. Add a pure helper `is_synthetic_bnode_var : var_name -> bool` that
   recognises the `"_bnode_"` prefix used by `rewrite_query_bnode_*`.
2. Add a helper `strip_synthetic_bnode_vars : solution_sequence -> solution_sequence`
   that drops any `(v, t)` pair from each solution mapping where
   `is_synthetic_bnode_var v`.
3. In `eval_select_query`, change the `Select_All` projection branches
   (both grouping and non-grouping paths) to call
   `strip_synthetic_bnode_vars` before returning.

This is a projection-layer fix, not a closure-rule fix. It does not
touch any OWL/RDFS rule, no `assume val`, no patches.

### Soundness

- The synthetic variables are never user-visible (the user wrote `[...]`
  not `?x`), so removing them from the result is a no-op for any well-
  written test.
- Removing the columns may change duplicate-elimination behaviour under
  `SELECT DISTINCT`. parent7 doesn't use DISTINCT, but for safety we
  must strip BEFORE DISTINCT/REDUCED so that distinct-after-strip is
  the right semantics. parent7's expected = 1 row with `?parent=Dudley`,
  and the post-strip rows include exactly 1 row matching that (the
  canonical maxqc1 binding) plus duplicates that DISTINCT would collapse.
  Correct order: strip → ORDER BY → DISTINCT → LIMIT.
- For `SELECT ?x` (Select_Vars) the synthetic variables are already
  filtered out by `project_solutions`, so the helper need only run for
  `Select_All`.

### Why this is F\*-first, not patch-side

The OCaml patch `53_blank_node_variable_rewriting.sh` predates the F\*
rewriter and runs the SAME rewrite again from the runner. With an F\*
projection-strip in place we could later delete that patch, but the
patch's continued presence does not change the fix — both code paths
introduce the same `_bnode_*` variable names, both stripped uniformly
by the new helper.

## Acceptance check

1. F\* verifies clean (no `--lax`, no `--admit_smt_queries`).
2. After main thread re-extracts:
   - parent7 PASSes (1 row, `?parent=:Dudley`).
   - parent2..parent10 unchanged.
   - sparqldl-* unchanged.
   - scm-* unchanged.
   - simple1..simple8 unchanged.
3. Sweep delta: +1 SPARQL pass on entailment.
