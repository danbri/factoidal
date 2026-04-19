# factoidal

Formally-verified SPARQL 1.1 + RDF 1.1, for Node and the browser.

The semantics live in [F*](https://www.fstar-lang.org/) and are compiled
down via OCaml and then js_of_ocaml into the `factoidal.js` bundle
shipped in this package. There is no hand-written SPARQL evaluator —
the JavaScript you run here was extracted from the same `.fst`
specifications that verify under Z3.

> Status: **0.1.0-alpha.0, unpublished.** This package is scaffolding
> committed to the repo so we can iterate on the API surface before
> cutting a real release. Nothing here has been published to the npm
> registry yet. See `CHANGELOG.md`.

## Install

```bash
npm install factoidal
```

## Usage (Node, CommonJS)

```js
const { query } = require('factoidal');

const data = `
  @prefix ex:  <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   foaf:name "Bob"   .
`;

const q = `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name
`;

(async () => {
  const results = await query(data, q);
  for (const row of results.results.bindings) {
    console.log(row.name.value);
  }
})();
```

## Usage (Node, ESM / TypeScript)

```ts
import { query } from 'factoidal';

const r = await query(data, q);      // SparqlResultsJson
console.log(r.results!.bindings);
```

The types ship with the package (`index.d.ts`).

## Usage (Browser, ES module)

```html
<script type="module">
  import { query } from 'https://unpkg.com/factoidal/browser.js';
  const ttl   = '@prefix : <http://ex/> . :a :p :b .';
  const r     = await query(ttl, 'SELECT * WHERE { ?s ?p ?o }');
  console.log(r.results.bindings);
</script>
```

The browser entry assumes `factoidal.js` sits alongside `browser.js`
on the same origin. If your bundler or CDN layout differs, call
`setFactoidalUrl('https://.../factoidal.js')` once before `query()`.

## API

```ts
query(dataString: string, queryString: string, options?: QueryOptions)
  : Promise<SparqlResultsJson | string>
```

| option       | values                                          | default    |
| ------------ | ----------------------------------------------- | ---------- |
| `dataFormat` | `'turtle' \| 'ntriples' \| 'nquads' \| 'trig' \| 'rdfxml'` | `'turtle'` |
| `entail`     | `'none' \| 'RDFS' \| 'OWL-RL'`                  | `'none'`   |
| `output`     | `'json' \| 'csv' \| 'tsv' \| 'xml' \| 'table' \| 'ntriples'` | `'json'`   |

When `output` is `'json'`, the promise resolves to a parsed SPARQL
Results JSON object (see [W3C
spec](https://www.w3.org/TR/sparql11-results-json/)). For every other
value it resolves to the raw string the CLI would have printed.

The promise **rejects** on bad input (unparseable query, malformed
RDF) or on a non-zero exit from the underlying engine. The thrown
`Error` carries `.exitCode`, `.stdout`, and `.stderr` properties for
diagnosis.

## How this thing works

```
 F* .fst    ──(fstar.exe --codegen OCaml)──►    OCaml
                                                 │
                                                 ├── native bin/<platform>/factoidal
                                                 │
                                                 └── js_of_ocaml ──► factoidal.js
                                                                       (this bundle)
```

The `factoidal.js` file in this package is the exact same artifact
the project ships to GitHub Pages for its
[browser demo](https://danbri.github.io/factoidal/fstar-extracted/).
It's a js_of_ocaml build of a command-line tool: argv in, stdout out.
This module drives it via js_of_ocaml's fake filesystem
(`globalThis.jsoo_fs_tmp`), overrides `process.argv`, captures
`console.log`, and returns the parsed result.

A future release will add a wasm_of_ocaml path — the API is already
`async` so that swap-in is non-breaking.

## What works / what doesn't

Tested against the W3C SPARQL 1.1 conformance suite:

- **Works:** `SELECT`, `ASK`, SPARQL 1.1 grammar, `FILTER`, `OPTIONAL`,
  `UNION`, `MINUS`, `BIND`, `VALUES`, `EXISTS` / `NOT EXISTS`,
  `DISTINCT`, `ORDER BY`, `LIMIT`, `OFFSET`, `GROUP BY`, `HAVING`,
  all aggregates (`COUNT`, `SUM`, `AVG`, `MIN`, `MAX`, `GROUP_CONCAT`,
  `SAMPLE`), subqueries, property paths, 30+ built-in functions,
  named graphs, RDFS and an OWL 2 RL Datalog subset for
  `--entail RDFS` / `--entail OWL-RL`.
- **Partially works:** `CONSTRUCT` (parses and evaluates, but the
  Turtle serializer for the result graph is still being wired up —
  some `CONSTRUCT` queries currently return empty).
- **Not yet:** `SERVICE` (federated query), `DESCRIBE`, SPARQL
  `UPDATE` beyond `INSERT DATA` / `DELETE DATA`, the SPARQL Protocol
  HTTP endpoint, OWL-Direct reasoning beyond the RL Datalog subset.

Current conformance numbers live in the main repo's `README.md` and
`.claude-worklog.md`.

### Known limitations in this JS package specifically

- **Not reentrant.** The bundle is a one-shot CLI — two concurrent
  `query()` calls in the same process will collide on the shared
  `globalThis` state. Serialize calls if you need parallelism.
- **Hash functions in the browser return empty strings.** MD5, SHA1,
  SHA256, SHA384, SHA512 work under Node (via `node:crypto`) but the
  browser shim returns `""`. The rest of SPARQL's built-in functions
  work identically.
- **Synchronous under the hood.** The API is `async` but the work
  happens on the calling thread. For big datasets run it in a worker.

## License

Apache-2.0. See the `LICENSE` file at the repo root
([github.com/danbri/factoidal/blob/claude/main/LICENSE](https://github.com/danbri/factoidal/blob/claude/main/LICENSE)).
A copy is included when this package is published.

## Source

[github.com/danbri/factoidal](https://github.com/danbri/factoidal)
