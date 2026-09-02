---
title: "JSON-LD: RDF as JSON"
description: "JSON-LD is RDF wearing the syntax most web developers already know — an @context turns ordinary JSON keys into predicate IRIs, mechanically, with nothing hidden."
layout: hub.njk
series: docs-hub
series_order: 7
vocab: schema.org
status: published
tests: tests/hub/post07_test.mjs
---

Every post in this series so far has parsed Turtle — RDF's own,
purpose-built syntax. Most working developers never write Turtle; they
write JSON. JSON-LD closes that gap: it's RDF expressed in ordinary
JSON, readable and writable with the same tools and habits as any
other JSON API, needing exactly one addition — an `@context` — to make
its keys mean something outside the document that contains them.

## A JSON object that isn't RDF yet

```json
{
  "@id": "http://example.org/alice",
  "name": "Alice",
  "jobTitle": "Engineer"
}
```

This is a perfectly ordinary JSON object. `@id` is a JSON-LD keyword —
it names the subject, `http://example.org/alice` — but `name` and
`jobTitle` are bare strings with no defined meaning outside this
document. Nothing says whether `name` means `schema:name`,
`foaf:name`, or something this document's author made up. Feed it to
the engine's JSON-LD processor anyway and see what comes out:

```observable-js
const PLAIN_JSON = JSON.stringify({
  "@id": "http://example.org/alice",
  "name": "Alice",
  "jobTitle": "Engineer",
});

const result = await Factoidal.jsonldToRdf(PLAIN_JSON);
const tripleCount = result.nquads.trim().length === 0 ? 0 : result.nquads.trim().split("\n").length;
return { tripleCount };
```

Zero triples. `@id` alone asserts nothing by itself — it just names a
subject — and JSON-LD 1.1 §7.2's expansion algorithm drops any key
that isn't `@`-prefixed and doesn't resolve to an absolute IRI under
the (absent) context. `name` and `jobTitle` are silently discarded, not
guessed at: the engine never invents a predicate IRI for a term it
can't resolve.

## `@context`: the mapping that fixes it

```json
{
  "@context": {
    "schema": "http://schema.org/",
    "name": "schema:name",
    "jobTitle": "schema:jobTitle",
    "Person": "schema:Person"
  },
  "@id": "http://example.org/alice",
  "@type": "Person",
  "name": "Alice",
  "jobTitle": "Engineer"
}
```

`@context` is itself a plain JSON object: `"name": "schema:name"` says
"wherever this document uses the key `name`, read it as the predicate
`schema:name`" — and `"schema": "http://schema.org/"` says how to
expand that CURIE. `@type` is a keyword (like `@id`), and its value
`"Person"` is looked up in the same context to become
`schema:Person`. There's no inference here, no natural-language
understanding — expansion is a mechanical string-substitution pass
over the JSON tree, term by term. The same document, now with a
context attached:

```observable-js
ALICE_JSONLD = JSON.stringify({
  "@context": {
    "schema": "http://schema.org/",
    "name": "schema:name",
    "jobTitle": "schema:jobTitle",
    "Person": "schema:Person",
  },
  "@id": "http://example.org/alice",
  "@type": "Person",
  "name": "Alice",
  "jobTitle": "Engineer",
});
```

Run the same call as above, now with a context in place:

```observable-js
async function tryJsonldToRdf(jsonldText) {
  try {
    if (typeof Factoidal.jsonldToRdf !== "function") {
      throw new Error("Factoidal.jsonldToRdf is not exposed by this build");
    }
    const result = await Factoidal.jsonldToRdf(jsonldText);
    return { available: true, nquads: result.nquads };
  } catch (err) {
    return { available: false, note: err.message };
  }
}

return tryJsonldToRdf(ALICE_JSONLD);
```

Three triples this time: `schema:name "Alice"`, `schema:jobTitle
"Engineer"`, and `rdf:type schema:Person` — the exact same
subject, now with predicates any other RDF tool can read, because
they're full IRIs instead of document-local strings. Same JSON
structure, same keys, one small addition, and the data means something
outside its own document.

`Factoidal.jsonldToRdf` is a raw ABI export (`bin/npm-entry/entry_jsoo.ml`'s
`jsonldToRdf`, per [`README.md`](./README.md)'s bindings table), not
one of `fn`'s typed methods — it needs the npm-entry ABI bundle the
same way `shexValidate` and `shaclValidate` do, so the `try`/`catch`
capability check above is the same pattern
[post 06](./06-shapes-the-other-dialect-shex.md) used for ShEx.
`fn.parse(text, {format: 'jsonld'})` also parses JSON-LD (the common
case, and the typed path every earlier post in this series uses), but
`jsonldToRdf` exists specifically for
`rdfDirection`/`expandContext`/`processingMode` — options `fn.parse`'s
generic surface has no room for.

## Round trip: JSON-LD in, N-Quads out, then query it

The three triples above are ordinary RDF the moment they exist — query
them with the same SPARQL every other post in this series uses, no
JSON-LD-specific query language required, starting from the same
`ALICE_JSONLD` document above:

```observable-js
const result = await Factoidal.jsonldToRdf(ALICE_JSONLD);
const nquads = result.nquads;

const reparsed = await fn.parse(nquads, { format: "nquads" });
const rows = await fn.query(reparsed, `
  # Name and job title for every person, from the N-Quads produced above.
  PREFIX schema: <http://schema.org/>
  SELECT ?name ?title WHERE {
    ?person schema:name ?name ; schema:jobTitle ?title .
  }
`);

return rows.map((r) => ({ name: r.get("name").value, title: r.get("title").value }));
```

`fn.parse`'s N-Quads input is the exact text `Factoidal.jsonldToRdf`
produced two paragraphs up — nothing about the query layer knows or
cares that this data started life as JSON.

## The reverse: RDF back to JSON-LD

Expansion has an inverse. JSON-LD's **fromRdf** algorithm (the
"Serialize RDF as JSON-LD" direction) takes an RDF dataset and produces
the **expanded-form** JSON-LD document for it: no `@context`, every
predicate spelled as a full IRI, every value wrapped as a `@value`
object. `Factoidal.jsonldFromRdf` runs it — hand it the same three
triples as N-Quads and it hands back the node object they describe:

```observable-js
const NQUADS = [
  '<http://example.org/alice> <http://schema.org/name> "Alice" .',
  '<http://example.org/alice> <http://schema.org/jobTitle> "Engineer" .',
  '<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://schema.org/Person> .',
].join("\n");

const result = await Factoidal.jsonldFromRdf(NQUADS);
return JSON.parse(result.jsonld);
```

One node object: its `@id` is `http://example.org/alice`, its `@type`
lists `http://schema.org/Person`, and each `schema:` predicate carries a
one-element array of `{"@value": …}`. This is the round trip closing —
the expanded document, when fed back through `jsonldToRdf` with an
identity context, reproduces the triples it came from. `jsonldFromRdf`
is the raw ABI export backing the verified
[`JSONLD.FromRdf.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/JSONLD.FromRdf.fst)
algorithm, scored below.

## Score

Factoidal's JSON-LD `toRdf` conformance scores **460 pass, 1 fail, 6
skip (of 467)** against the JSON-LD 1.1 test suite — see
[the test-results dashboard]({{ '/test-results/' | url }}) for the
current run. The 1 fail is a documented Ryu-class float-formatting
case (a specific `xsd:double` lexical form the serializer renders
differently than the suite expects, not a semantic error); the 6
skips are tests that only apply under JSON-LD 1.0 processing mode,
which this engine does not target.

The reverse direction, `jsonldFromRdf`, scores **49 pass, 5 fail (of
54)** against the JSON-LD 1.1 `fromRdf` manifest — driven by
[`bin/jsonld-fromrdf-runner`](https://github.com/danbri/factoidal/blob/claude/main/bin/jsonld-fromrdf-runner/jsonld_fromrdf_runner.ml).
The 5 fails are the non-normative `rdfDirection` variants and the
JSON-LD-1.0 list-serialization semantics, neither of which this engine
targets.

## What's next

[Canonical graphs: RDFC-1.0 and content addressing](./08-canonical-graphs-rdfc10.md)
picks up where this post's N-Quads output leaves off: what happens
when two graphs describe the same facts with different blank-node
labels, and how RDFC-1.0 makes them compare equal anyway.

Every live cell above is pinned in
[`tests/hub/post07_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post07_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn`/`Factoidal` adapters.
