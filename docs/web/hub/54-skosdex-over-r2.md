---
title: "A store in a bucket: SPARQL over plain HTTP"
description: "Open a Shardborough generation that lives in an object store, ask the engine which artifacts a query needs, fetch only those, and answer the query in the browser. Nine SKOS query shapes, with the keys, the bytes and the time each one costs."
layout: hub.njk
series: docs-hub
series_order: 54
vocab: skos
status: experimental
tests: tests/hub/post54_test.mjs
hubHideCellSource: true
hubEngineLabel: "the Lean-derived WebAssembly engine, over HTTP"
---

[Post 51](../51-query-shardborough-blocks-in-browser/) fetched three block
files this notebook already knew the names of. This page does not know any
names. It fetches one pointer file, hands the manifest to the engine, and
then asks the engine a question the whole design turns on:

> Which artifacts does this query need?

The engine answers with a list of object keys. The page fetches exactly
those keys and nothing else, checks each one against the SHA-256 the
manifest commits for it, and hands the bytes back. No server process runs
anywhere: the store is a directory of immutable objects behind an ordinary
web server, and the query engine is in the tab.

## The request sequence, in full

```text
GET  <base>/CURRENT                    5 bytes      the activated generation's name
GET  <base>/gen-1/manifest.sbm2        one object   every artifact, its length, its SHA-256

  storeManifestInspect(manifest)       in the tab   the engine decodes it; the page never parses it
  storeQueryPlan(manifest, sparql)     in the tab   -> {mode, shards, keys[], sidecarKeys[], blobKeys[]}

GET  <base>/gen-1/<key>                per key      bounded parallel; Range where a window is named
  SHA-256(bytes) == manifest's digest  in the tab   a mismatch is refused BY NAME; bytes discarded

  storeQuery(manifest, sparql, windows over one region)  -> SPARQL Results JSON
```

Two properties make this safe over a transport nobody controls. The
manifest commits a SHA-256 per artifact, so a substituted or truncated
object is refused by name rather than answered from. And the refusal
happens twice: the page checks the digest before the bytes reach the
module, and `storeQuery` checks every artifact it opens against the same
commitment regardless. Turning the page's check off changes *when* a bad
object is caught, not *whether*.

The host that does the fetching is
[`@factoidal/core`'s `store-http`](https://github.com/danbri/factoidal/blob/claude/main/npm/factoidal/store-http/index.mjs).
It decides nothing: it has no field offset, no magic number and no idea
what a block is. `tools/host-purity-lint.sh` scans it for exactly those.

## Nine SKOS questions

The nine shapes below are the SPARQL cookbook of the
[skosdex](https://github.com/danbri/skosdex) web application, rewritten for
whichever store you point the notebook at. The default target is a small
store served from this site: five IPTC NewsCodes vocabularies, 4,434
triples in thirteen predicate-local blocks, published by the IPTC under
CC BY 4.0. It is a real generation, packed and activated by the same Lean
tools, and served here as plain files.

Watch the **objects** and **bytes** columns. Eight of the nine shapes read
one, two or three of the thirteen blocks. The predicate census reads all
thirteen, because a triple pattern with an unbound predicate can be
answered by any of them and the engine says so rather than guessing.

```observable-js
skosdexOverHttp = {
  const shapes = [
    { id: "census", title: "Concept census",
      why: "The core SKOS conformance check: who types their entries skos:Concept, and how many.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT (COUNT(?c) AS ?concepts) WHERE { ?c a skos:Concept }` },
    { id: "indexer", title: "The indexer shape",
      why: "The exact pattern a search indexer flattens into one document per concept.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT ?c ?pref ?def WHERE {
  ?c a skos:Concept ; skos:prefLabel ?pref .
  OPTIONAL { ?c skos:definition ?def }
  FILTER(LANGMATCHES(LANG(?pref), "en"))
} LIMIT 20` },
    { id: "schemes", title: "Scheme inventory",
      why: "One row per concept scheme, with how many concepts each holds.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT ?scheme (COUNT(?c) AS ?concepts) WHERE { ?c skos:inScheme ?scheme }
GROUP BY ?scheme ORDER BY DESC(?concepts)` },
    { id: "languages-of-one", title: "One concept, every language",
      why: "Every label a single concept carries, with its language tag. IPTC tags en-gb and en-us, never plain en.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT ?lang ?label WHERE {
  <http://cv.iptc.org/newscodes/spamfstat/yards-per-attempt> skos:prefLabel ?label
  BIND(LANG(?label) AS ?lang)
} ORDER BY ?lang` },
    { id: "same-label", title: "Same label, which concept",
      why: "A label-level crosswalk: which concepts carry this exact label in this exact language.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT ?c WHERE { ?c skos:prefLabel "number-of-plays"@en-gb }` },
    { id: "language-coverage", title: "Language coverage",
      why: "Labels per language tag across the whole store.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT ?lang (COUNT(?l) AS ?labels) WHERE {
  ?s skos:prefLabel ?l BIND(LANG(?l) AS ?lang)
} GROUP BY ?lang ORDER BY DESC(?labels)` },
    { id: "predicates", title: "Predicate census",
      why: "How the store links things. An unbound predicate reaches every block, so this is the shape that reads everything.",
      q: `SELECT ?p (COUNT(*) AS ?n) WHERE { ?s ?p ?o } GROUP BY ?p ORDER BY DESC(?n)` },
    { id: "top-concepts", title: "Top concepts of every scheme",
      why: "The entry points a concept browser starts from: a join across two predicate blocks.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT ?scheme ?c ?label WHERE {
  ?scheme skos:hasTopConcept ?c . ?c skos:prefLabel ?label
  FILTER(LANGMATCHES(LANG(?label), "en-gb"))
} LIMIT 20` },
    { id: "definitions", title: "Definitions that mention video",
      why: "A full-text-ish filter with no index: the engine reads one block and evaluates CONTAINS over it.",
      q: `PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
SELECT ?c ?def WHERE {
  ?c skos:definition ?def
  FILTER(LANGMATCHES(LANG(?def), "en") && CONTAINS(LCASE(?def), "video"))
} LIMIT 20` }
  ];
  const sampleBase = new URL("../assets/store/sample/", location.href).href;
  const r2Base = "https://pub-ce682919a85f481f9864add9d9a66737.r2.dev/skosall/";
  const liveMode = document.body.dataset.hubMode === "live";

  const root = html`<section class="store-http-demo">
    <style>
      .store-http-demo { display:grid; gap:.9rem; padding:clamp(.85rem,2.5vw,1.35rem); border:1px solid #c4dce5; border-radius:1rem; background:linear-gradient(145deg,#f7fbfc 0%,#eef7f8 100%); box-shadow:0 .8rem 2.2rem rgba(21,57,75,.08); }
      .store-http-demo .eyebrow { margin:0 0 .2rem; color:#196a85; font-size:.72rem; font-weight:800; letter-spacing:.12em; text-transform:uppercase; }
      .store-http-demo h2 { margin:0; color:#15394b; font-size:clamp(1.15rem,3.5vw,1.65rem); line-height:1.15; }
      .store-http-demo .subhead { margin:.35rem 0 0; color:#4b6572; font-size:.92rem; }
      .store-http-demo label { display:grid; gap:.35rem; font-weight:700; color:#15394b; }
      .store-http-demo input, .store-http-demo select, .store-http-demo textarea { width:100%; padding:.6rem .7rem; border:1px solid #a8cbd7; border-radius:.6rem; background:#fff; color:#15394b; font:.88rem/1.5 ui-monospace, SFMono-Regular, Menlo, monospace; box-sizing:border-box; }
      .store-http-demo textarea { min-height:8rem; resize:vertical; }
      .store-http-demo input:focus-visible, .store-http-demo select:focus-visible, .store-http-demo textarea:focus-visible, .store-http-demo button:focus-visible { outline:3px solid #075fd0; outline-offset:2px; }
      .store-http-demo .actions { display:flex; flex-wrap:wrap; gap:.55rem; }
      .store-http-demo button { min-height:2.75rem; padding:.55rem .85rem; border:1px solid #196a85; border-radius:.6rem; color:#fff; background:#196a85; font:inherit; font-weight:700; cursor:pointer; }
      .store-http-demo button.secondary { color:#15394b; background:#f7fbfc; border-color:#b8d2dc; }
      .store-http-demo button:disabled { opacity:.65; cursor:wait; }
      .store-http-demo .status { margin:0; padding:.7rem .8rem; border-left:4px solid #196a85; background:#e5f1f5; color:#15394b; }
      .store-http-demo .why { margin:0; color:#4b6572; font-size:.9rem; }
      .store-http-demo table { width:100%; border-collapse:collapse; font-size:.86rem; }
      .store-http-demo th, .store-http-demo td { text-align:left; padding:.3rem .45rem; border-bottom:1px solid #d6e6ec; vertical-align:top; }
      .store-http-demo td.num { text-align:right; font-variant-numeric:tabular-nums; }
      .store-http-demo .scroll { overflow:auto; max-height:22rem; }
      .store-http-demo details { border:1px solid #c4dce5; border-radius:.65rem; padding:.55rem .75rem; background:#f7fbfc; }
      .store-http-demo summary { cursor:pointer; font-weight:700; color:#15394b; }
      .store-http-demo pre { white-space:pre-wrap; overflow-wrap:anywhere; margin:.5rem 0 0; font-size:.8rem; }
      @media (max-width: 640px) { .store-http-demo .actions button { flex:1 1 11rem; } }
      @media (prefers-color-scheme: dark) {
        .store-http-demo { background:linear-gradient(145deg,#13252d 0%,#172f38 100%); border-color:#345866; box-shadow:none; }
        .store-http-demo h2 { color:#e8f7fb; }
        .store-http-demo .subhead, .store-http-demo .why { color:#b9d1da; }
        .store-http-demo input, .store-http-demo select, .store-http-demo textarea, .store-http-demo details { background:#17272e; color:#d9eef5; border-color:#345866; }
        .store-http-demo .status { background:#19323d; color:#d9eef5; }
        .store-http-demo button.secondary { background:#17272e; color:#d9eef5; border-color:#4e7786; }
      }
    </style>
    <header>
      <p class="eyebrow">A store in a bucket</p>
      <h2>Query objects over HTTP</h2>
      <p class="subhead">The engine names the keys. This page fetches those keys, checks their digests, and answers in your browser.</p>
    </header>
    <label>Collection root (the URL that holds <code>CURRENT</code>)
      <input class="base" type="url" spellcheck="false" />
    </label>
    <div class="actions">
      <button type="button" class="secondary use-sample">Use the bundled sample store</button>
      <button type="button" class="secondary use-r2">Use the skosdex store in R2</button>
    </div>
    <label>Question
      <select class="shape"></select>
    </label>
    <p class="why"></p>
    <label>SPARQL
      <textarea class="sparql" spellcheck="false"></textarea>
    </label>
    <div class="actions">
      <button type="button" class="run">Open the store and run</button>
      <button type="button" class="secondary run-all">Run all nine</button>
    </div>
    <p class="status" aria-live="polite"></p>
    <div class="scroll rows" aria-live="polite"></div>
    <details open><summary>Requests this query made</summary><div class="scroll requests"></div></details>
    <details><summary>What the engine planned</summary><pre class="plan">No run yet.</pre></details>
  </section>`;

  const baseInput = root.querySelector(".base");
  const shapeSelect = root.querySelector(".shape");
  const why = root.querySelector(".why");
  const sparql = root.querySelector(".sparql");
  const status = root.querySelector(".status");
  const rowsBox = root.querySelector(".rows");
  const requestsBox = root.querySelector(".requests");
  const planBox = root.querySelector(".plan");
  const runButton = root.querySelector(".run");
  const runAllButton = root.querySelector(".run-all");

  baseInput.value = sampleBase;
  for (const shape of shapes) {
    const option = document.createElement("option");
    option.value = shape.id;
    option.textContent = shape.title;
    shapeSelect.append(option);
  }
  const shapeById = id => shapes.find(s => s.id === id) || shapes[0];
  const showShape = () => {
    const shape = shapeById(shapeSelect.value);
    why.textContent = shape.why;
    sparql.value = shape.q;
  };
  showShape();
  status.textContent = liveMode
    ? "Ready. The R2 preset needs this live page; the strict page allows same-origin fetches only."
    : "Ready. This is the strict page, which allows same-origin fetches only — the sample store works here, the R2 preset needs the live twin of this page.";

  const table = (columns, rows) => {
    const head = columns.map(c => `<th>${c.label}</th>`).join("");
    const body = rows.map(r => "<tr>" + columns.map(c =>
      `<td class="${c.num ? "num" : ""}">${c.get(r)}</td>`).join("") + "</tr>").join("");
    const node = document.createElement("div");
    node.innerHTML = `<table><thead><tr>${head}</tr></thead><tbody>${body}</tbody></table>`;
    return node;
  };
  const escape = value => String(value ?? "")
    .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  const shortTerm = term => term === undefined ? ""
    : term.type === "uri" ? escape(term.value.replace(/^.*[/#]([^/#]+)$/, "$1"))
    : escape(term.value) + (term["xml:lang"] ? "@" + term["xml:lang"] : "");
  const kb = bytes => (bytes / 1024).toFixed(1) + " kB";
  const ms = value => value.toFixed(0) + " ms";

  let opened = null;
  let openedBase = null;
  const openStore = async () => {
    const base = baseInput.value.trim();
    if (opened !== null && openedBase === base) return opened;
    status.textContent = `Fetching CURRENT and the manifest from ${base} …`;
    const started = performance.now();
    const store = await fn.openStoreOverHttp(base, { concurrency: 4 });
    opened = store;
    openedBase = base;
    const facts = store.facts;
    status.textContent =
      `Opened ${facts.generation}: ${facts.entries.toLocaleString()} artifacts, ` +
      `${facts.rows.toLocaleString()} rows, ${kb(facts.bytes)} of blocks, ` +
      `manifest ${kb(facts.manifestBytes)}, wire version ${facts.wireVersion}. ` +
      `${ms(performance.now() - started)}.`;
    return store;
  };

  const showAnswer = (shape, answer) => {
    const bindings = (answer.result.srj && answer.result.srj.results.bindings) || [];
    const variables = (answer.result.srj && answer.result.srj.head.vars) || [];
    rowsBox.replaceChildren(table(
      variables.map(name => ({ label: "?" + name, get: row => shortTerm(row[name]) })),
      bindings));
    requestsBox.replaceChildren(table([
      { label: "object key", get: r => escape(r.key) },
      { label: "bytes", num: true, get: r => r.bytes.toLocaleString() },
      { label: "ms", num: true, get: r => r.ms.toFixed(0) },
      { label: "digest", get: r => r.verified ? "checked" : "—" }
    ], answer.requests));
    planBox.textContent = JSON.stringify({
      question: shape.title,
      mode: answer.plan.mode,
      artifactsSelected: answer.plan.shards,
      keys: answer.plan.keys,
      sidecarKeys: answer.plan.sidecarKeys,
      blobKeys: answer.plan.blobKeys,
      entriesDroppedByZoneMap: answer.plan.zoneExcluded,
      objectsFetched: answer.requests.length,
      bytesTransferred: answer.timings.networkBytes,
      planMs: Math.round(answer.timings.planMs),
      fetchMs: Math.round(answer.timings.fetchMs),
      answerMs: Math.round(answer.timings.answerMs)
    }, null, 2);
    status.textContent =
      `${shape.title}: ${bindings.length} row${bindings.length === 1 ? "" : "s"}, ` +
      `${answer.requests.length} object${answer.requests.length === 1 ? "" : "s"} fetched, ` +
      `${answer.timings.networkBytes.toLocaleString()} bytes, ` +
      `plan ${ms(answer.timings.planMs)} · fetch ${ms(answer.timings.fetchMs)} · ` +
      `answer ${ms(answer.timings.answerMs)}. Mode ${answer.plan.mode}.`;
  };

  const runOne = async () => {
    const shape = shapeById(shapeSelect.value);
    const store = await openStore();
    showAnswer(shape, await store.query(sparql.value));
  };

  const runAll = async () => {
    const store = await openStore();
    const measured = [];
    for (const shape of shapes) {
      const answer = await store.query(shape.q);
      const bindings = (answer.result.srj && answer.result.srj.results.bindings) || [];
      measured.push({
        title: shape.title,
        mode: answer.plan.mode,
        objects: answer.requests.length,
        bytes: answer.timings.networkBytes,
        rows: bindings.length,
        total: answer.timings.totalMs
      });
    }
    rowsBox.replaceChildren(table([
      { label: "question", get: r => escape(r.title) },
      { label: "plan mode", get: r => escape(r.mode) },
      { label: "objects", num: true, get: r => r.objects },
      { label: "bytes", num: true, get: r => r.bytes.toLocaleString() },
      { label: "rows", num: true, get: r => r.rows },
      { label: "ms", num: true, get: r => r.total.toFixed(0) }
    ], measured));
    requestsBox.replaceChildren();
    const bytes = measured.reduce((sum, r) => sum + r.bytes, 0);
    status.textContent =
      `Nine questions, ${measured.reduce((s, r) => s + r.objects, 0)} objects, ` +
      `${bytes.toLocaleString()} bytes in all. The whole store is ` +
      `${store.facts.bytes.toLocaleString()} bytes.`;
  };

  const guard = (button, work) => async () => {
    runButton.disabled = true;
    runAllButton.disabled = true;
    try {
      await work();
    } catch (error) {
      status.textContent = `Did not complete: ${error.message}`;
      planBox.textContent = String(error.stack || error);
    } finally {
      runButton.disabled = false;
      runAllButton.disabled = false;
    }
  };

  shapeSelect.addEventListener("change", showShape);
  baseInput.addEventListener("change", () => { opened = null; openedBase = null; });
  root.querySelector(".use-sample").addEventListener("click", () => {
    baseInput.value = sampleBase; opened = null; openedBase = null;
  });
  root.querySelector(".use-r2").addEventListener("click", () => {
    baseInput.value = r2Base; opened = null; openedBase = null;
    status.textContent = liveMode
      ? "The R2 generation holds 219,530,671 rows in 36,106 artifacts and its manifest is 25.5 MB. Opening it is measured in minutes, not seconds — see the prose below before you press Run."
      : "This strict page cannot fetch a cross-origin URL. Open the live twin of this page to reach R2.";
  });
  runButton.addEventListener("click", guard(runButton, runOne));
  runAllButton.addEventListener("click", guard(runAllButton, runAll));
  return root;
}
```

## What the nine shapes cost

Measured on 2026-09-07 against the bundled sample store, through the same
host this page uses, over an ordinary HTTP server
(`node tests/store-http/over-http.mjs`). The store is 455,818 bytes of
blocks in thirteen objects, plus a 6,044-byte manifest.

| question | plan mode | objects | bytes | rows |
|---|---|---|---|---|
| Concept census | `ibk3-paged-merkle(1)` | 1 | 48,565 | 1 |
| The indexer shape | `ibk3-paged-merkle(3)` | 3 | 291,306 | 20 |
| Scheme inventory | `ibk3-paged-merkle(1)` | 1 | 48,380 | 5 |
| One concept, every language | `ibk3-paged-merkle(1)` | 1 | 143,503 | 2 |
| Same label, which concept | `ibk3-paged-merkle(1)` | 1 | 143,503 | 1 |
| Language coverage | `ibk3-paged-merkle(1)` | 1 | 143,503 | 2 |
| Predicate census | `ibk3-paged-merkle-full-manifest(13)` | 13 | 455,818 | 13 |
| Top concepts of every scheme | `ibk3-paged-merkle(2)` | 2 | 191,888 | 20 |
| Definitions that mention video | `ibk3-paged-merkle(1)` | 1 | 99,238 | 20 |

Opening the store costs two requests: `CURRENT`, then the manifest. Every
later question costs one request per artifact the plan named, and a
question whose predicate is a constant names one artifact per predicate.

## Where the selectivity comes from

Nothing on this page is a cache or an index of the page's own making. The
manifest already says, per artifact, which predicate it holds, how many
rows, how many bytes, its SHA-256, and — from wire version 10 — the range
of subjects and objects it covers. `storeQueryPlan` reads the query's
triple patterns against those declarations and drops every artifact that
cannot contribute. The plan reports `zoneExcluded`: how many artifacts the
subject and object ranges alone ruled out, with no block read at all.

That is also the limit. A pattern with an unbound predicate can be
answered by any block, so the plan selects the whole manifest and says so
in its mode (`…-full-manifest(N)`). Selectivity here is a property of the
manifest, not of the query engine's cleverness, and the notebook shows you
which of the two you got.

## The big one: 219 million rows in an R2 bucket

Every skosdex vocabulary that could be fetched — 662 named graphs,
219,530,671 quads, 18.6 GB of blocks in 36,106 artifacts — was packed on
Fly.io and synced to Cloudflare R2
(`deploy/fly/skosall/`). The bucket is public, serves ranges, and answers
a browser preflight from `https://danbri.github.io`. Measured from this
laptop on 2026-09-07:

| step | measured |
|---|---|
| `GET CURRENT` | 316 ms, 5 bytes |
| `GET manifest.sbm2` | 4.3 s, 25,533,404 bytes (5.9 MB/s) |
| the same manifest again | 4.9 s — R2 sends no `Cache-Control`, so nothing is reused |
| hexadecimal encoding of the manifest for the ABI | 4.6 s, 51,066,808 characters |
| **`storeManifestInspect`** | **538 s** |

The transport is not the problem. Decoding a 25.5 MB manifest of 36,106
entries takes nine minutes inside the engine, and both `storeQueryPlan`
and `storeQuery` decode it again, so one question against this generation
costs roughly half an hour. It also overflows the default call stack
before it gets that far: Node clears it with a worker thread and a 64 MB
stack, and a browser tab has no such control.

So the R2 preset in the cell above is real, reachable and correct, and it
is not usable from a tab today. What has to change is in the engine, not
in the page:

1. **Carry the manifest as bytes, not as hexadecimal.** The blob ABI
   already exists — `storeQuery` uses it for artifacts. The manifest
   argument is still a hex string, which doubles it and costs seconds
   before any work starts.
2. **Decode the manifest once and keep it.** `storeOpen` already retains
   decoded state behind a handle, but it opens artifacts eagerly, which a
   19 GB generation cannot do. A manifest-only handle would make the
   9-minute decode a one-off instead of a per-call cost.
3. **Make the decode itself cheaper and non-recursive**, so a tab's fixed
   frame budget is enough
   ([issue 653](https://github.com/danbri/factoidal/issues/653) is the
   same defect on the query path).
4. **Split the manifest**, so a reader who wants one vocabulary fetches
   one vocabulary's declarations. §4 of
   [the hierarchical named graphs note](../../../designissues/2026-09-07-hierarchical-named-graphs/)
   is where that argument is being had.

Until then the honest description of the R2 store is: published, verified,
range-readable, and opened by a program with a big stack and patience.

Two smaller things a reader will meet. Cloudflare rate-limits the
`r2.dev` development URL, so the notebook keeps at most four requests in
flight and a custom domain is what a real deployment uses. And this page,
like every hub page, has a strict twin and a live twin: the strict page's
`connect-src 'self'` allows the bundled sample store and refuses R2, and
the live twin allows both.

## Reproducing it

```bash
# The tests, against a mock bucket — no network, no credentials.
node tests/store-http/over-http.mjs
node --test tests/hub/post54_test.mjs

# A mock bucket you can point a browser at.
node tests/store-http/mock-bucket.mjs --root npm/factoidal/sample-store \
  --prefix skosall --port 8787

# The public bucket, checked by hand.
BASE=https://pub-ce682919a85f481f9864add9d9a66737.r2.dev/skosall
curl -sI "$BASE/CURRENT"
curl -sI -H 'Range: bytes=0-1023' "$BASE/gen-1/predicate-0.ibk5"
curl -s -o /dev/null -D - -X OPTIONS \
  -H 'Origin: https://danbri.github.io' \
  -H 'Access-Control-Request-Method: GET' \
  -H 'Access-Control-Request-Headers: range' "$BASE/gen-1/manifest.sbm2"
```

The design record is
[the store-over-HTTP note](../../../designissues/2026-09-07-store-over-http/);
the operating manual for packing and activating a generation is the
[`shardborough-storage` skill](https://github.com/danbri/factoidal/blob/claude/main/skills/shardborough-storage/SKILL.md).
