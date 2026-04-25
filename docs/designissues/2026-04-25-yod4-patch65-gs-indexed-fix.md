# Yod4 — Wave 18 build unblock: graph_store gs_indexed field across patches

Date: 2026-04-25
Branch: claude/main
Scope: post-extraction OCaml patches only — no F* changes.

## Symptom

Wave 18 OCaml compile fails:

```
File "SPARQL11_Algebra.ml", line 2970, characters 43-59:
2970 |   | Some g -> FStar_Pervasives_Native.Some { gs_graph = g }
                                                  ^^^^^^^^^^^^^^^^
Error: Some record fields are undefined: gs_indexed
```

Phase 0 (`be27bf9`) added `gs_indexed : indexed_graph` to the `graph_store`
record in `RDF.Graph.Executable.fst`. Patches that hand-construct
`{ gs_graph = ... }` literals are now ill-typed.

Plus, build log shows:

```
WARNING: 65_base_iri_resolution could not find eval_select_query header
WARNING: 65_base_iri_resolution could not close eval_select_query result scope
```

## Root causes

### 1. Patch 57 (`57_service_client_bind.sh`)

Constructs `{ gs_graph = g }` directly. There is now an F*-extracted
helper `graph_to_store` (line 154 of SPARQL11_Algebra.ml) that already
wraps a graph with the proper indexed companion. Use it.

### 2. Patch 65 (`65_base_iri_resolution.sh`)

Two stale regexes:

a. The opening anchor expects:
   `  match (q1?).q_form with\n  | QF_Select sel ->`
   (2-space indent, no parens around `match`).
   But the actual extracted code at L4964 is:
   `      (match q1.q_form with\n       | QF_Select sel ->`
   (6/7-space indent, parens, scrutinee inside `match q1`).
   This is because Phase 0 / Tav2's edits added an `apply_query_dataset`
   call before the inner match, wrapping it in a `match uu___ with | (g1, ds1) -> (...)`.

b. The closing anchor expects:
   `  | QF_Describe uu___ -> []`
   The actual code at L5035 is:
   `       | QF_Describe uu___1 -> [])`
   (different indent, `uu___1` not `uu___`, trailing close paren).

### 3. Sweep of other patches

`grep -l 'gs_graph =' patches/*.sh experimental_ocaml_glue/*.sh` returned
ONLY `57_service_client_bind.sh`. No other patches construct graph_store
literals. Done.

## Fix plan

1. Patch 57: replace the literal `{ gs_graph = g }` with
   `graph_to_store g`. `graph_to_store` is the canonical F\*-side wrapper
   that builds the index (`gs_indexed = build_indexed g`). Using it keeps
   semantic intent in F* and any future schema evolution is picked up
   automatically.

2. Patch 65: rewrite the two regex anchors:
   - Opening: match the new `(match q1.q_form with` paren+indent shape,
     and account for the `apply_query_dataset` prelude. Wrap the whole
     paren-bound match in a `let saved_base = ... in current_base_iri_ref := q.q_base; let result = (match ...) in current_base_iri_ref := saved_base; result` block.
   - Closing: tolerate `uu___1` and the trailing `)` from the now-paren-wrapped match.

3. Acceptance: `./build-ocaml.sh compile` succeeds; w3c_runner sweep
   produces 1657/1658.

## Verification

Re-extracted from current F\* sources (so `graph_store` has both `gs_graph`
and `gs_indexed`), then re-applied patches and `./build-ocaml.sh compile`.
Compile success log: `/Users/danbri/working/factoidal/.claude-runs/yod4-build-*.log`.

## Out of scope

- F* changes (graph_store schema is correct).
- Phase 2.5 wiring.
- Other backend constructors.
