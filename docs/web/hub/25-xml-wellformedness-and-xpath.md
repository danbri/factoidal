---
title: "XML well-formedness and XPath"
description: "The same F* XML parser that underpins RDF/XML also answers two questions on its own: is this document well-formed, and what does an XPath 1.0 expression select from it. Both run in your browser over the verified parser and the Stage-1 XPath engine."
layout: hub.njk
series: docs-hub
series_order: 25
vocab: xml
status: published
tests: tests/hub/post25_test.mjs
---

RDF/XML — one of the [five syntaxes](./11-one-graph-five-syntaxes/) — is
built on plain XML, so factoidal has a generic XML parser underneath it
([`Parser.XML.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/Parser.XML.fst)).
That parser is useful on its own, for two XML questions that have
nothing to do with RDF: **is this document well-formed**, and **what
does an XPath expression select from it**. This post exposes both over
the verified parser and the Stage-1 XPath engine
([`XPath.Eval.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/XPath.Eval.fst)),
running live.

## Well-formed, or not

XML well-formedness is a structural property: tags nest and match,
attributes are quoted, there is one root element. It is decided entirely
by whether the parser accepts the byte string — there is no separate
"validator" pass. This first cell hands the parser a document that
nests and matches:

```observable-js
const XML = `<library>
  <book id="b1"><title>SPARQL 1.1</title></book>
  <book id="b2"><title>RDF Primer</title></book>
</library>`;
return await Factoidal.xmlWellformed(XML);
```

`{ ok: true, wellformed: true }`. Now break it — a closing tag that does
not match the element it closes — and ask again:

```observable-js
const BAD = `<library><book></shelf></library>`;
return await Factoidal.xmlWellformed(BAD);
```

`{ ok: true, wellformed: false }`. The `</shelf>` closes nothing that is
open, so `Parser_XML.parse_xml_document` returns `None`, and
`xmlWellformed` reports the document as not well-formed. The decision is
the accept/reject signal itself, straight from the F*-extracted parser —
the same signal the W3C conformance runner scores.

## XPath: selecting nodes

XPath 1.0 is the query language for XML that predates — and inspired —
SPARQL's property paths. An expression names a path through the
document tree and returns a **node-set**, a string, a number, or a
boolean. `Factoidal.xpathEval(xml, expr)` returns an envelope carrying
the `resultType` and the value; for a node-set it lists each node's
kind, name, and string-value. Here `//book/title` selects both title
elements:

```observable-js
const XML = `<library>
  <book id="b1"><title>SPARQL 1.1</title></book>
  <book id="b2"><title>RDF Primer</title></book>
</library>`;
const res = await Factoidal.xpathEval(XML, "//book/title");
return pretty(res.nodes.map((n) => ({ kind: n.kind, name: n.name, value: n.value })));
```

Two `element` rows, named `title`, with the string-values `SPARQL 1.1`
and `RDF Primer`. The `//` is XPath's abbreviation for
`descendant-or-self::node()/`, so `//book/title` reaches both books
wherever they sit under the root.

## XPath: the four result types

Not every expression returns nodes. `count()` returns a number, a
`text()` step returns a node-set, `string(@id)` returns a string, and a
comparison returns a boolean. This cell runs one of each and tabulates
the `resultType` the engine assigned alongside the value:

```observable-js
const XML = `<library>
  <book id="b1"><title>SPARQL 1.1</title></book>
  <book id="b2"><title>RDF Primer</title></book>
</library>`;
const exprs = [
  "count(//book)",
  "//book[1]/title/text()",
  "string(//book[2]/@id)",
  "count(//book) > 1",
];
const rows = [];
for (const e of exprs) {
  const r = await Factoidal.xpathEval(XML, e);
  rows.push({
    expression: e,
    resultType: r.resultType,
    value: r.resultType === "nodeset" ? r.stringValue : String(r.value),
  });
}
return pretty(rows);
```

`count(//book)` is a **number** (`2`); `//book[1]/title/text()` is a
**nodeset** whose string-value is `SPARQL 1.1`; `string(//book[2]/@id)`
is a **string** (`b2`); and `count(//book) > 1` is a **boolean**
(`true`). The `[1]`/`[2]` predicates are positional, `@id` steps into
the attribute axis, and `text()` selects the character data — the same
XPath 1.0 constructs the spec-cited battery in
[`tests/unit/xpath_tests.ml`](https://github.com/danbri/factoidal/blob/claude/main/tests/unit/xpath_tests.ml)
exercises section by section.

## Scope: well-formedness now, DTD deliberately not

Two boundaries are deliberate and named in the runner:

- **No DTD/DOCTYPE processing.** `Parser.XML.fst` has no `<!DOCTYPE`
  production at all, so a document carrying an internal or external DTD
  subset is reported as not well-formed rather than validated. This is a
  scope cut, not a defect — the W3C runner skips DTD-validation tests
  by design.
- **XPath covers a documented subset.** The forward and reverse axes,
  positional predicates, the node tests, and the core function library
  are supported; `following::`/`preceding-sibling::` and the id()
  function are rejected cleanly at parse time rather than
  mis-evaluated.

Against the vendored
[W3C XML Conformance Test Suite](https://github.com/danbri/factoidal/tree/claude/main/third_party/testing/xml/xmlconf),
the parser scores **244 real pass, 0 fail** out of 2585 — "real"
meaning the parser rejected the construct actually under test. The
rest are skipped rather than force-passed: 1166 documents this
well-formedness-only parser can reject only because it does not
implement DOCTYPE/DTD (the tested construct is never exercised), and 32
that are not-well-formed only under XML 1.1 or Namespaces, outside what
this XML-1.0, non-namespace parser claims. Driven by
[`bin/xml-runner`](https://github.com/danbri/factoidal/blob/claude/main/bin/xml-runner/xml_runner.ml).

## What's next

The same parser drives RDF/XML in the
[five-syntaxes post](./11-one-graph-five-syntaxes/); XPath is the
selection half of the XForms/XSLT-style processing that the
[program plan](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-05-xforms-model-program-plan.md)
sketches on top of it.

Every live cell above is pinned in
[`tests/hub/post25_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post25_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
npm-entry ABI instead of the in-browser `Factoidal` adapter.
