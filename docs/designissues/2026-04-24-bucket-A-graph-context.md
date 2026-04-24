# Bucket A: graph-context threading diagnosis (WIP)

Date: 2026-04-24
Status: in progress
Timebox: 90 min

## The 4 failing tests

| Suite | Test | Expected | Got |
|---|---|---|---|
| aggregates | `COUNT: no GROUP BY inside of GRAPH` | 17 | 0 |
| bindings | `VALUES inside GRAPH binding the same variable as the graph name` | 24 | 0 |
| construct | `constructwhere04` | 4 | 0 (uses `FROM`) |
| basic-update | `INSERT same bnode twice` (two variants) | named=1/1 | default=0/0 |

## Hypotheses (pre-read)

- **GP_Graph**: `eval_pattern` in `SPARQL11.Algebra.fst` may ignore the named graph selector `gt` and pass the *default* graph to the inner `p`, so cross-graph joins return empty.
- **FROM <data.ttl>**: dataset clause in `eval_select_query` may not install `data.ttl` into the default graph before evaluation.
- **INSERT DATA + bnodes across GRAPH blocks**: `apply_insert_data` probably creates fresh bnodes per GRAPH block rather than sharing bnode labels across the whole op.

Filling in per-test .rq + .fst evidence next.

