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

`factoidal-sparql-results` defaults to a sortable result table, with variables
as columns and bindings as rows. It carries full IRI/literal detail in the
rendered terms and offers reader controls for language and datatype filtering,
independent language-tag/datatype visibility, value/language/datatype sorting,
table transposition, and record-card views. Card direction and the gentle named
palettes are ordinary attributes (`palette`, `view`, `language-tags`,
`datatypes`, `tags`, `transpose`, `card-direction`, `max-rows`), so most pages
need no custom JavaScript. `tags` remains as a backwards-compatible shorthand
for hiding both kinds of term metadata.

Post 50, the life-sciences Shardborough notebook, is the first consumer. Its
runner now has explicit progress and error states and displays the actual
cross-graph SELECT result in its default table rather than a JSON diagnostic
dump or forced card view. This is UI work only: it does not change the
documented present execution boundary (Turtle loaded into the existing browser
evaluator).

Verification on 2026-08-30:

- `node --check web/hub/assets/sparql-result-elements.mjs`;
- `node --test tests/hub/post50_test.mjs`; and
- a full Eleventy build to a disposable directory, including assertion that
  the module and post 50 output are emitted.

An in-app interactive browser pass was unavailable in this coding environment
because the browser connection did not supply its required sandbox policy.
The page should still receive a final phone/desktop interaction pass in the
deployed GitHub Pages browser before its visual treatment is considered final.
