# Hub SPARQL result components — 2026-08-30

The Hub now ships a small, dependency-free custom-element module at
`web/hub/assets/sparql-result-elements.mjs`. It is deliberately separate from
the Observable-style notebook machinery: any static documentation page can
load it and set a component's `results` property to a SPARQL Results JSON
object.

The public elements are:

- `factoidal-sparql-results` for `SELECT` result bindings;
- `factoidal-sparql-graph` for graph / `CONSTRUCT`-style statements;
- `factoidal-sparql-boolean` for `ASK` results; and
- `factoidal-sparql-error` for an accessible query failure message.

`factoidal-sparql-results` defaults to a sortable result table, carries full
IRI/literal detail in the rendered terms, and offers reader controls for
language and datatype filtering, term-detail visibility, table transposition,
and record-card views. Card direction and the gentle named palettes are
ordinary attributes (`palette`, `view`, `tags`, `transpose`,
`card-direction`, `max-rows`), so most pages need no custom JavaScript.

Post 50, the life-sciences Shardborough notebook, is the first consumer. Its
runner now has explicit progress and error states and displays the actual
cross-graph SELECT result instead of a JSON diagnostic dump. This is UI work
only: it does not change the documented present execution boundary (Turtle
loaded into the existing browser evaluator).

Verification on 2026-08-30:

- `node --check web/hub/assets/sparql-result-elements.mjs`;
- `node --test tests/hub/post50_test.mjs`; and
- a full Eleventy build to a disposable directory, including assertion that
  the module and post 50 output are emitted.

An in-app interactive browser pass was unavailable in this coding environment
because the browser connection did not supply its required sandbox policy.
The page should still receive a final phone/desktop interaction pass in the
deployed GitHub Pages browser before its visual treatment is considered final.
