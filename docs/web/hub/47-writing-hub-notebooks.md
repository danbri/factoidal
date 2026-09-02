---
title: "Writing Hub notebooks"
description: "How Factoidal's checked, Observable-style browser notebooks are authored and tested."
layout: hub.njk
series: docs-hub
series_order: 47
vocab: none
status: published
tests: tests/hub/post47_test.mjs
---

Hub posts are ordinary versioned Markdown pages with small live cells. They
borrow Observable's reactive notebook model — values can be named once and
used by later cells — while remaining a static Eleventy site with all runtime
code vendored in this repository. For Observable's wider ecosystem and its
static-site framework, see the official [Observable Framework documentation](https://observablehq.com/framework/).
Factoidal does not require an Observable account or a CDN at runtime.

## A minimal query notebook

Use an `observable-js` fence for a live cell. Give reusable values a name;
later cells then depend on that value rather than duplicating data.

```observable-js
notebookTurtle = '<http://example.org/alice> <http://example.org/name> "Alice" .'
```

```observable-js
notebookDataset = fn.parse(notebookTurtle)
```

```observable-js
const rows = await fn.query(notebookDataset, `# The ex:name of every subject in the dataset declared by the cell above.
SELECT ?name WHERE { ?s <http://example.org/name> ?name }`);
return pretty(rows);
```

The runtime orders those cells by their references and recomputes dependent
cells when a reader edits and runs one. The available bindings are deliberately
small: `fn` is the typed Factoidal interface (`parse`, `query`, and selected
other capabilities); `pretty` renders binding rows; `d3`, `Plot`, `html`, and
`md` support presentation. Prefer `fn` to the lower-level `Factoidal` binding.

Keep cells small and make I/O explicit. A live cell should demonstrate a real
capability, not merely decorate prose. Use ordinary fenced code for static
syntax examples. Browser pages are sandboxed and normally make no network
requests; a post that intentionally allows a third-party dependency must
declare and test that boundary.

## The test contract

Every post with cells has a Node test under `tests/hub/`. It extracts the
literal fenced source from the Markdown and executes it against the same typed
API used in the browser. That pins the page's examples to real results rather
than allowing prose and code to drift apart. The implementation details and
full authoring reference remain in [`README.md`](README/).

For a richer reactive example, see [post 26](../26-reactive-cells-declare-once-use-everywhere/).
