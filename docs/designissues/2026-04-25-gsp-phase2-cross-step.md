# GSP Phase 2 — cross-step (suite-level) state sharing

Date: 2026-04-25
Agent: Gimel2
Predecessor: `docs/designissues/2026-04-25-gsp-phase1-stateful.md` (Pe, `60230c3`)
Lane:
  - `formal/fstar/ocaml-output/w3c_runner.ml` `run_gsp_test` only.
  - **No** changes to `SPARQL.GraphStore.fst` (Pe's algo is correct).
  - **No** changes to `run_protocol_test` (He's lane).
  - **No** `extract` / `compile` runs.

## Problem

After Pe's Phase 1 (`60230c3`), `http-rdf-update` is at 13/19 PASS. The
remaining 6 fails are all GET-of-{PUT,POST} or HEAD tests whose semantic
prior state was set up by an earlier *test* in the manifest (not an
earlier `#### Request` block in the same comment — each comment has a
single request).

Current runner state (run before Phase 2):

```
FAIL: GET of PUT - Initial state            (target=http://.../person/1.ttl, expect 200, got 404)
FAIL: GET of PUT - default graph            (target=<default>, expect 200, got 404)
FAIL: PUT - mismatched payload              (needs Turtle parser — DEFERRED)
FAIL: GET of POST - multipart/form-data     (target=person/1.ttl, expect 200, got 404)
FAIL: GET of POST - create new graph        (target=$NEWPATH$, expect 200, got 404)
FAIL: GET of POST - after noop              (target=$NEWPATH$, expect 200, got 404)
```

Phase 1's per-test `ref empty_store` discards prior PUTs/POSTs. Phase 2
fixes the GET-of-* cases with two surgical glue changes; the
`put__mismatched_payload` failure stays since it requires Turtle parsing
to detect URI/body subject mismatch (Pe's Phase 1 deferred this).

## Approach (≤120 LoC OCaml glue)

1. **Suite-level shared store**: add a top-level `_gsp_suite_store` ref.
   Reset at the start of `http-rdf-update` (detected by test name
   `"PUT - Initial state"` — the first manifest entry).

2. **Key normalisation**: `_gsp_target_of_request` returns a
   `gs_target`; we add a thin `_gsp_canonical_key` that maps the various
   URL shapes for "the same graph" to a single string:
   - `?default` ⇒ canonical `<default>`
   - `?graph=http://$HOST$/$GRAPHSTORE$/person/1.ttl` and
     direct path `$GRAPHSTORE$/person/1.ttl` and
     `http://$HOST$/$GRAPHSTORE$/person/1.ttl` all ⇒ `/person/1.ttl`
   - bare container POST (`POST $GRAPHSTORE$`) ⇒ `$NEWPATH$` so that
     the subsequent GET on `$NEWPATH$` resolves.

3. Wrap `_gsp_dispatch` so writes go to the canonical key (via
   `GT_Named canon` / `GT_Default`) and reads do too.

The semantic decisions (PUT-creates-vs-replaces, POST-merges, etc.) all
still flow through `SPARQL_GraphStore.gsp_*`. Per CLAUDE rule #15, the
new code is pure URL-shape normalisation glue.

## Tests we expect to flip to PASS

| Test                                  | Expected | Why flips |
|---------------------------------------|----------|-----------|
| `GET of PUT - Initial state`          | 200      | shared store + key canon |
| `GET of PUT - default graph`          | 200      | shared store (key already matched) |
| `GET of POST - multipart/form-data`   | 200      | shared store + key canon (post__multipart_formdata seeded /person/1.ttl) |
| `GET of POST - create new graph`      | 200      | shared store + bare-container ⇒ `$NEWPATH$` |
| `GET of POST - after noop`            | 200      | shared store + `$NEWPATH$` |

Realistic delta: **+5 PASS** (13 → 18 of 19). The remaining FAIL is
`put__mismatched_payload`, which needs the F* Turtle parser to detect
URI/body subject mismatch (deferred to a future phase).

## Hard limits

- ≤120 LoC of new w3c_runner.ml.
- No `.fst` changes.
- No `extract` / `compile`.
- 60-min budget.
