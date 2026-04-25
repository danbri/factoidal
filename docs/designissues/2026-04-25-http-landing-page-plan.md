# 2026-04-25 — `factoidal-http` landing page + bundled web component

Agent: Sade2. Branch: claude/main. HEAD at start: d23854d.

## Goal

Make `factoidal-http` self-discoverable in a browser. Hitting
`http://host:port/` returns an HTML page that loads the existing
`factoidal-sparql-client` web component pointed at the same instance's
`/sparql` endpoint. The bare `/sparql` URL with no `query=` continues
to 4xx per W3C SPARQL Protocol §2.1.5, which is correct behaviour
for a Protocol endpoint; the discoverable UX lives at `/`.

## Why now

- Endpoint is live at `http://100.107.116.70:3030/sparql` with 3.14M
  parliament quads.
- Web component bundle (`docs/fstar-extracted/factoidal-sparql-client.js`,
  ~54 KB) already exists and is shipped via the docs site. Embedding
  it into the server makes the endpoint self-documenting without an
  external host.
- Protocol-conformant `/sparql` 400-on-no-query is unfriendly to humans
  who paste the URL into a browser; we redirect to `/` when
  `Accept: text/html` is present, leaving curl / RDFLib / Jena alone.

## Routes added (all in `factoidal_http.ml`, pre-dispatch)

| Method | Path | Behaviour |
|--|--|--|
| GET | `/` | 200, `text/html`, inline HTML page |
| GET | `/index.html` | same as `/` |
| GET | `/factoidal-sparql-client.js` | 200, `application/javascript`, served from disk |
| GET | `/sparql` w/ `Accept: text/html`, no `query=` | 303 redirect to `/` |
| GET | `/sparql` w/ no `query=`, non-HTML accept | 400 (existing F* path) |

Everything else (POST /sparql, POST /update, GET /sparql?query=...) is
untouched — the new routes intercept BEFORE `P.decode_request` so the
F* protocol logic is unchanged.

## File-on-disk lookup for `factoidal-sparql-client.js`

The binary needs to find the JS bundle at runtime. Strategy: search a
small list of candidate paths derived from `Sys.argv.(0)` and CWD:

1. `<exe-dir>/../docs/fstar-extracted/factoidal-sparql-client.js`
2. `<exe-dir>/factoidal-sparql-client.js` (if a deployer co-locates it)
3. `<cwd>/docs/fstar-extracted/factoidal-sparql-client.js`
4. `<cwd>/factoidal-sparql-client.js`

If none exist, return 404 with a helpful message ("bundle not found,
checked: ..."). No fancy templating; just absolute-path resolution.

## HTML page contents (inlined string in OCaml)

- Minimal styling (system font, narrow column).
- Heading: "factoidal SPARQL endpoint".
- Brief explanation of what this is.
- A `<factoidal-sparql-client endpoint="/sparql">` element with one
  seeded `<factoidal-query>` child: `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }`.
- A `<script type="module" src="/factoidal-sparql-client.js"></script>`.
- A footer line with a link to `/sparql?query=...` for the same query
  (so curl users get a copy-pasteable URL).

## Hard limits respected

- LoC: target < 200 added LoC in factoidal_http.ml.
- No edits to `SPARQL.HTTP.fst` / `SPARQL.Protocol.fst`.
- No re-extraction or rebuild required (rule #11 — `build-ocaml.sh
  compile` will pick up the change next time someone runs it).
- No semantic logic — pure I/O glue per rule #15.

## F* discipline

The decision "GET / is HTML, GET /sparql is SPARQL Protocol" is a
dispatch-table item, which lives in `factoidal_http.ml` already. We're
adding rows to that table, not encoding RDF/SPARQL semantics.

## Coordination

- Aleph3 owns the web-component bundle itself; Sade2 only embeds it.
- Bet3 is consolidating CLIs; Sade2 doesn't touch CLI structure, just
  the HTTP server.

## Out of scope (for this commit)

- The `?examples=parliament` deep-link to vendored .rq queries (stretch
  goal in the brief). Note for follow-up: the queries live under
  `third_party/data/ukparliament/sparql/{main,detail}/*.rq` and there
  are 24 of them. Discoverable from the running server would need
  another route (e.g. `GET /examples/parliament/<n>.rq` serving
  `text/plain`). Defer.
- Caching headers / ETag for the JS bundle.
- Compression (gzip/br).
- TLS (the brief is explicit: behind a tunnel).
