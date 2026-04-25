# SPARQL Update bnode-scoping fix — basic-update suite (2026-04-25)

## Goal

Fix the 2 W3C `basic-update` suite fails (task #23):

- `:insert-05a` — "INSERT same bnode twice"
- `:insert-data-same-bnode` — "INSERTing the same bnode with INSERT DATA into two different Graphs is the same bnode"

## Diagnosis

Both tests boil down to a bnode-scoping disagreement between current F\* code
and SPARQL 1.1 Update §4.1.1 / §4.1.3.

### Test 1: `insert-05a.ru`

Pre-data: `<http://example.org/g1>` contains `_:b :p :o`.

Update:
```sparql
INSERT { GRAPH :g2 { ?S ?P ?O } } WHERE { GRAPH :g1 { ?S ?P ?O } } ;
INSERT { GRAPH :g2 { ?S ?P ?O } } WHERE { GRAPH :g1 { ?S ?P ?O } } ;
INSERT { GRAPH :g3 { :s :p ?count } } WHERE { SELECT (COUNT(*) AS ?count) WHERE { GRAPH :g2 { ?s ?p ?o } } } ;
DROP GRAPH :g1 ;
DROP GRAPH :g2
```

Expected `g3` after the request: `:s :p 1`.

Current behaviour: g3 ends up with `:s :p 2` (two triples in g2 because the
post-instantiation `rename_quad_bnodes` step in `apply_modify` mangles the
**variable-bound** bnode `?S=_:b` (from the pre-data) with a different
per-op prefix each time, producing two distinct bnode labels in g2 and
hence count=2.

### Test 2: `insert-data-same-bnode.ru`

Update:
```sparql
INSERT DATA { GRAPH :g1 { _:b :p :o }
              GRAPH :g2 { _:b :p :o } } ;
INSERT { GRAPH :g2 { ?S ?P ?O } } WHERE { GRAPH :g1 { ?S ?P ?O } } ;
INSERT { GRAPH :g3 { :s :p ?count } } WHERE { SELECT (COUNT(*) AS ?count) WHERE { GRAPH :g2 { ?s ?p ?o } } } ;
DROP GRAPH :g1 ;
DROP GRAPH :g2
```

Expected `g3` after the request: `:s :p 1`.

The first INSERT DATA op shares a single `_insdata_<n>` prefix across the two
GRAPH blocks, so g1 and g2 both get the same fresh node. Good. But the
second op (`INSERT { GRAPH :g2 } WHERE { GRAPH :g1 }`) has the same bug as
Test 1 — `?S=_:b` is renamed by `rename_quad_bnodes` with a per-op prefix
that differs from g2's existing bnode label, so g2 gains a second distinct
bnode → count=2.

## Root cause

`apply_modify` line 4996 calls `insert_quads_per_mapping` which runs
`rename_quad_bnodes prefix` over **every** bnode in the instantiated quads.
That step is meant to give *template* bnodes (`_:b` literally written in
the INSERT clause) per-solution-mapping freshness. But variable-bound
bnodes (`?S` matched against an existing bnode from the dataset) flow
through `instantiate_bgp` → `bound_subject_of_pattern` → `S_BNode b` with
their **dataset-original** label, and then get clobbered by the same
post-rename, breaking graph identity.

## Fix

Move template-only bnode freshening **into instantiation** (where we know
which positions are `PS_BNode` template literals vs `PS_Var` bindings).
Drop the post-instantiation `rename_quad_bnodes` step in `apply_modify`.

Concrete change (one .fst, no new files):

1. Add a salt/sol_ix-aware variant of `instantiate_bgp` and
   `instantiate_ggp_quads` that calls `fresh_bnode_for_op` on `PS_BNode`
   subject and `PT_BNode` object positions:

   ```fstar
   let fresh_bnode_for_op (op_salt:string) (sol_ix:nat) (lbl:string) : bnode_id =
     String.concat "" [op_salt; "_sm"; string_of_int sol_ix; "_"; lbl]

   let bound_subject_freshen (op_salt:string) (sol_ix:nat) ...
   let instantiate_tp_freshen ...
   let instantiate_bgp_freshen ...
   let instantiate_ggp_quads_freshen ...
   ```

   Var-bound `_:b` passes through unchanged. Template `_:b` becomes
   `<op_salt>_sm<sol_ix>_b` — deterministic, distinct per op + per
   mapping.

2. Thread `op_idx : nat` through `apply_update_ops` so each
   `U_Modify` and `U_InsertData` sees a distinct salt:

   ```fstar
   let rec apply_update_ops (ds:rdf_dataset) (ops:list update_op)
                            (op_idx:nat) : Tot rdf_dataset (decreases ops) =
     match ops with
     | [] -> ds
     | op :: rest ->
       let ds' = apply_update_op ds op op_idx in
       apply_update_ops ds' rest (op_idx + 1)
   ```

3. `apply_insert_data` keeps a single shared salt prefix (the request salt
   `request_<dataset_size>`) for ALL `U_InsertData` ops in one request,
   so `INSERT DATA { _:b … } ; INSERT DATA { _:b … }` map to the SAME
   bnode. (NB: inside `apply_insert_data` we don't have multiple
   solutions; `_:b` shared across multiple GRAPH blocks within one op
   already shares a prefix.)

4. `apply_modify` uses `op_idx` to derive its per-op salt, drops the
   `rename_quad_bnodes` post-step, and uses `instantiate_ggp_quads_freshen`.

## Verification

`fstar.exe --include . --cache_dir .cache --hint_dir hints SPARQL11.Algebra.fst`,
no `--lax`. Patch ocaml-output via existing patch sequence (no new
patches needed if extraction goes through cleanly).

## Expected test deltas

- `basic-update`: 11 pass, 2 fail → **13 pass, 0 fail**.
- `insert-where-same-bnode` and `insert-where-same-bnode2` (currently
  passing, where each op uses a *template* `_:b`) must continue to pass:
  the per-op salt change keeps their bnodes distinct across ops, which
  is the required behaviour.
- No other suite touches the modified functions in a way that changes
  the externally observable graph (template bnodes already get a fresh
  per-(op,mapping) label in current code; only the *exact label string*
  changes).
