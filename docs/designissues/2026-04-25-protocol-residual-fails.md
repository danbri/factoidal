# Protocol residual fails — Wave 10 → Agent Qof

**Date:** 2026-04-25  
**Branch:** claude/main  
**HEAD at start:** `49d87a2` (Wave 10) — actual score: 29 pass / 5 fail

## Recount

The Wave-10 release notes summarised the protocol suite as "32/2", but
re-running today gives **29 pass, 5 fail, 0 skip**. The five fails:

| # | Manifest entry | Symptom on F* runner | Root cause |
|---|---|---|---|
| 1 | `query_dataset_full` | `parse error: invalid IRI` | `ASK FROM <abs> { <data1.rdf> ?p ?o }` — relative IRI in BGP, no `BASE` clause; parser rejects |
| 2 | `query_content_type_describe` | `parse error: unsupported: DESCRIBE queries` | DESCRIBE not yet supported in SPARQL11.Parser |
| 3 | `query_content_type_construct` | `parse error: invalid IRI` | `CONSTRUCT { <s> <p> 1 } WHERE {}` — relative IRIs `<s>`, `<p>` |
| 4 | `update_post_form` | `expected query= on /query endpoint, got update=` | Path is `/sparql/` (no `query`/`update` discriminator); decoder rule needs the form-encoded body to choose between PR_Query / PR_Update by the form key (`update=`/`query=`), not by URL path |
| 5 | `update_base_uri` | `update parse error: expected predicate-object list` | `INSERT DATA { GRAPH <abs> { <abs> <abs> <test> } }` — `<test>` is relative; parser bails on next predicate-object pair |

## Decision

The user's task spec assumed two specific fails (`bad_update_dataset_conflict`
and a similar dataset-clauses-vs-protocol-params test). Those are already
PASSING — the conflict-rejection logic landed in
`SPARQL.Protocol.fst` already (`PR_Bad_using_conflict`-style branch).

The five real fails split into two buckets:
- **(1, 3, 5) relative-IRI handling.** SPARQL §4.1.1.1 says relative IRIs
  in queries/updates must be resolved against an in-scope `BASE` IRI; if
  there is none, an implementation MAY use the service URI. Three of the
  five fails are not really *protocol* bugs — they're **parser** strictness.
  Resolving relative IRIs in the absence of an explicit BASE is genuinely
  out of scope for a 45-min slot (touches SPARQL11.Parser.fst broadly).
- **(2) DESCRIBE.** Pure parser feature gap.
- **(4) `/sparql/` + `update=` form-body.** This *is* a protocol-decoder
  bug. The decoder currently picks PR_Query vs PR_Update from the URL
  path (`/query` vs `/update`), but for a form-encoded POST the form key
  itself is authoritative (W3C Protocol §2.2.2 form encoding). When the
  body has `update=` (and no `query=`), it's an UPDATE regardless of path.

## Fix scope (45-min budget)

Fix #4 only — it's the one true protocol bug. The other four are parser
work and should be tracked as separate issues. Expected delta: 29→30 pass.

## Implementation plan for #4

In `SPARQL.Protocol.fst`, the `decode_request` POST + form-encoded branch
already extracts `query=` and `update=` keys from the form body. The
current logic is roughly:

```
if path matches "/update" or contains "update" → PR_Update
elif body has "update=" → PR_Update
else → PR_Query
```

The actual current logic looks at endpoint shape. Fix: when the form has
**both** present, error; when **only `update=`** present, return
`PR_Update` regardless of path; when only `query=`, return `PR_Query`.

(This is what the test asserts: `POST /sparql/` with `update=CLEAR%20ALL`
→ 2xx.)

## Verification

After edits, run `make verify-SPARQL.Protocol` (no `--lax`).

Then re-run `./bin/darwin-arm64/w3c_runner protocol` — expected 30/4.
