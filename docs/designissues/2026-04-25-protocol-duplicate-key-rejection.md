# Protocol: reject duplicate `query=` / `update=` keys (Phase 2, Agent Yod)

Date: 2026-04-25
Owner: Agent Yod
Phase: SPARQL 1.1 Protocol Phase 2 — bad-request tightening
Predecessors: He's Phase 1 (commit `f2d1492`), Tau's scoping (commit `3db0591`)

## Goal

Close two W3C protocol tests with a narrow F\* delta, no runner-side changes:

- `bad_multiple_queries` — `GET /sparql?query=ASK%20%7B%7D&query=SELECT%20%2A%20%7B%7D` → 4xx
- `bad_multiple_updates` — `POST` form-encoded `update=CLEAR%20NAMED&update=CLEAR%20DEFAULT` → 4xx

Both currently FAIL because `build_from_kvs` calls `first_value`, which silently
ignores duplicate keys and returns the first occurrence.

## Spec citation

W3C SPARQL 1.1 Protocol §2.1.4 (also §2.2.4 for update):

> "If the protocol client tries to include more than one `query` (or `update`)
> parameter, ... the service MUST return a 400 error."

## Where the fix goes

`formal/fstar/SPARQL.Protocol.fst`, function `build_from_kvs` (lines 456–480).

Current shape:

```fstar
let q_opt = first_value "query"  kvs in
let u_opt = first_value "update" kvs in
...
```

`first_value` is defined at lines 262–266 and silently returns the head of
`collect_values` — i.e. the first occurrence — losing duplicate signal.

## Approach

Pre-flight check on the kv list **before** picking a `first_value`:

```fstar
let n_query  = List.Tot.length (collect_values "query"  kvs) in
let n_update = List.Tot.length (collect_values "update" kvs) in
if n_query > 1 then
  PR_Bad "more than one query= parameter (Protocol §2.1.4)"
else if n_update > 1 then
  PR_Bad "more than one update= parameter (Protocol §2.2.4)"
else
  (* existing logic *)
```

`collect_values` is already case-sensitive (line 257: `if k = key then ...`),
which matches the spec — `query` and `Query` are distinct parameters.

Both `query` paths through `decode_request` use `build_from_kvs` (GET line 504,
POST form line 513) so a single fix covers all three duplicate-key vectors:
`?query=A&query=B`, `?update=A&update=B`, and form-bodies of either.

## Out of scope

- `bad_query_non_utf8` / `bad_update_non_utf8` — needs charset inspection
  in `content_type_base`. Separate task.
- `bad_update_dataset_conflict` — needs algebra-level detection. Separate task.
- `update_dataset_*` / `update_base_uri` — needs runner-side dataset
  persistence. He's Phase 3 territory.

## Verification

```
fstar.exe --include . --cache_dir .cache SPARQL.Protocol.fst
```

No `--lax`. No `build-ocaml.sh extract` or `compile` (Wave 9 rebuild in flight).

## Expected outcome

On next rebuild after the Wave 9 rebuild lands:

- `bad_multiple_queries` flips SKIP/FAIL → PASS
- `bad_multiple_updates` flips SKIP/FAIL → PASS

He's `run_protocol_test` already maps `PR_Bad` → 4xx, so no runner change needed.
