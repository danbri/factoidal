---
title: "Transforming and checking XML: XSLT and Schematron"
description: "An XSLT 1.0 stylesheet reshaping an XML document, and a Schematron rule firing on a document that violates it and clearing on one that doesn't — both running live over the verified F* engines that sit next to the XML parser from the well-formedness/XPath post."
layout: hub.njk
series: docs-hub
series_order: 27
vocab: none
status: published
tests: tests/hub/post27_test.mjs
---

The [well-formedness/XPath post](./25-xml-wellformedness-and-xpath/) covers
two questions the generic XML parser answers on its own: is a document
well-formed, and what does an XPath expression select from it. Two more
engines sit on the same parser: **XSLT 1.0**
([`XSLT.Transform.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/XSLT.Transform.fst))
rewrites an XML document into another XML document by template, and
**Schematron** ([`Schematron.Validate.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/Schematron.Validate.fst))
checks a document against rules written as XPath assertions rather than a
grammar. Both run live below.

## XSLT: reshaping a document

A stylesheet matches a template against the source tree and rebuilds the
output from `xsl:value-of` and `xsl:for-each`. This one turns a `<library>`
of `<book>` elements into a flat `<catalog>` of one-line `<entry>`
elements:

```observable-js
abi = await Factoidal.loadNpmEntry()
```

```observable-js
xsltResult = {
  const stylesheet = `<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <xsl:template match="/library">
    <catalog><xsl:for-each select="book"><entry><xsl:value-of select="title"/> by <xsl:value-of select="author"/></entry></xsl:for-each></catalog>
  </xsl:template>
</xsl:stylesheet>`;
  const source = `<library>
  <book id="b1"><title>SPARQL 1.1</title><author>W3C</author></book>
  <book id="b2"><title>RDF Primer</title><author>W3C</author></book>
</library>`;
  const raw = JSON.parse(abi.xsltTransform(stylesheet, source));
  if (!raw.ok) throw new Error(raw.error);
  return raw.output;
}
```

`<catalog><entry>SPARQL 1.1 by W3C</entry><entry>RDF Primer by W3C</entry></catalog>` —
two `<book>` elements walked by `xsl:for-each`, each field pulled out by
`xsl:value-of`. Nothing here is a special case of the parser: the
stylesheet is itself parsed by the same `Parser.XML.fst` module post 25
uses to decide well-formedness, then interpreted as a template against the
source tree.

## Schematron: rules instead of a grammar

A DTD or XSD says what shape a document must have. Schematron says what
must be true of it, in plain XPath — "a `person` element must have an
`age` child" is one `<assert>` inside one `<rule>`:

```observable-js
schematronRules = `<schema xmlns="http://purl.oclc.org/dsdl/schematron">
  <pattern>
    <rule context="person">
      <assert test="age">person must have an age</assert>
    </rule>
  </pattern>
</schema>`
```

Run it against a document that fails the rule:

```observable-js
schematronBad = {
  const doc = `<person><name>Bob</name></person>`;
  const raw = JSON.parse(abi.schematronValidate(schematronRules, doc));
  if (!raw.ok) throw new Error(raw.error);
  return pretty(raw.findings);
}
```

One finding, rendered as a table: an `assert-fail` at context `person`, test `age`, message
"person must have an age". Add the missing element and the same rule
clears:

```observable-js
schematronGood = {
  const doc = `<person><name>Bob</name><age>30</age></person>`;
  const raw = JSON.parse(abi.schematronValidate(schematronRules, doc));
  if (!raw.ok) throw new Error(raw.error);
  return raw.findings;
}
```

`[]` — the same `<rule context="person">` walks every `person` element in
the document via the context XPath, evaluates `age` as a boolean test at
each one, and this time there's nothing to report.

## Reaching these from the browser

`xsltTransform` and `schematronValidate` aren't (yet) wrapped by the
browser adapter the way `xmlWellformed`/`xpathEval` are — the cells above
call `Factoidal.loadNpmEntry()` directly and talk to the same
`factoidalNpmEntry` ABI object the wrapped calls use underneath, JSON in,
JSON out. Every live cell above is pinned in
[`tests/hub/post27_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post27_test.mjs).
