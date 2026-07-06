---
title: "Canonical graphs: RDFC-1.0 and content addressing"
description: "Two RDF graphs can assert identical facts and still fail a byte-for-byte diff, because blank-node labels are arbitrary — RDFC-1.0 canonicalizes them away, live, down to a stable content hash."
layout: hub.njk
series: docs-hub
series_order: 8
vocab: foaf
status: published
tests: tests/hub/post08_test.mjs
---

[Post 01](./01-triples-rdf-from-first-principles.md) introduced blank
nodes as "some person, unnamed" — a real term kind, but one whose
label (`_:x`, `_:b47`, whatever a parser happens to generate) has no
meaning outside the document that contains it. That's fine for reading
a graph. It's a problem the moment you want to *compare* two graphs
byte-for-byte: the same facts, serialized by two different tools, or
by the same tool on two different days, can carry completely different
blank-node labels — and a naive diff reports them as different
documents when they assert exactly the same thing.

## The same facts, two label choices

```turtle
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex:   <http://example.org/> .

# Document A
ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows _:x .
_:x a foaf:Person ; foaf:name "Bob" .

# Document B -- same facts, different blank-node label
ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows _:friend42 .
_:friend42 a foaf:Person ; foaf:name "Bob" .
```

Both documents say: Alice is a `foaf:Person` named "Alice" who knows
someone, and that someone is a `foaf:Person` named "Bob." `_:x` and
`_:friend42` are both just "the unnamed person Alice knows" — the
label is a parser's bookkeeping choice, not part of the fact. RDFC-1.0
(RDF Dataset Canonicalization) is the W3C algorithm for exactly this:
given any graph, deterministically compute canonical blank-node labels
from the graph's own structure (a hash-based relabeling, refined until
every blank node's hash is stable under its neighbors' hashes too), so
two isomorphic graphs — same shape, any original labels — always
canonicalize to the identical byte sequence.

## Canonicalizing both, live

```observable-js
const DOC_A = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows _:x .
  _:x a foaf:Person ; foaf:name "Bob" .
`;

const DOC_B = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows _:friend42 .
  _:friend42 a foaf:Person ; foaf:name "Bob" .
`;

const canonA = await Factoidal.canonicalize(DOC_A, { format: "turtle" });
const canonB = await Factoidal.canonicalize(DOC_B, { format: "turtle" });

return { identical: canonA === canonB, canonicalNQuads: canonA };
```

`identical: true` — `canonA` and `canonB` are the same string, blank
node label and all (`_:c14n0`, RDFC-1.0's own canonical-label
convention). Parsing renamed `_:x`/`_:friend42` to whatever
document-scoped label each parse happened to assign; canonicalization
erased that difference entirely.
`Factoidal.canonicalize` is a raw ABI export (see
[`README.md`](./README.md)'s bindings table) — there's no `fn`
wrapper for it yet, so cells call it directly the same way
[post 06](./06-shapes-the-other-dialect-shex.md) and
[post 07](./07-json-ld-rdf-as-json.md) called `Factoidal.shexValidate`/
`jsonldToRdf`.

## Content addressing: a hash of the canonical form

Once two graphs canonicalize to the same bytes, hashing those bytes
gives every graph a content address — a fixed-length identifier that's
equal exactly when the facts are equal, regardless of how the graph
was serialized or which tool produced it. That's the same idea as a
git commit hash or a container image digest, applied to RDF graphs
instead of files. Hash both canonical forms above, then change one
fact and confirm the hash moves:

```observable-js
const DOC_A = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows _:x .
  _:x a foaf:Person ; foaf:name "Bob" .
`;

const DOC_B = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows _:friend42 .
  _:friend42 a foaf:Person ; foaf:name "Bob" .
`;

// Same facts as DOC_A, but Bob's name is changed -- a genuinely
// different graph, not just a different blank-node label.
const DOC_C = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows _:x .
  _:x a foaf:Person ; foaf:name "Bobby" .
`;

async function sha256Hex(text) {
  const bytes = new TextEncoder().encode(text);
  const digest = await crypto.subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(digest)].map((b) => b.toString(16).padStart(2, "0")).join("");
}

const canonA = await Factoidal.canonicalize(DOC_A, { format: "turtle" });
const canonB = await Factoidal.canonicalize(DOC_B, { format: "turtle" });
const canonC = await Factoidal.canonicalize(DOC_C, { format: "turtle" });

const hashA = await sha256Hex(canonA);
const hashB = await sha256Hex(canonB);
const hashC = await sha256Hex(canonC);

return {
  sameFactsSameHash: hashA === hashB,
  differentFactsDifferentHash: hashA !== hashC,
  urn: `urn:rdfc:sha256:${hashA}`,
};
```

`sameFactsSameHash: true` (A and B differed only in a blank-node
label), `differentFactsDifferentHash: true` (C really does assert a
different fact — Bob's name changed). `urn:rdfc:sha256:...` is a
usable content-addressed identifier for the graph: publish it, cache
by it, or fetch by it, and anyone recomputing the same hash from an
isomorphic graph gets the same answer using only this project's own
canonicalize + a standard hash function — no shared blank-node
numbering scheme required between producer and consumer.

## Score

Factoidal's RDFC-1.0 implementation scores **86 pass, 0 fail (of 86)**
against the RDF Dataset Canonicalization test suite — see
[the test-results dashboard]({{ '/test-results/' | url }}) for the
current run.

## What's next

[Mapping tables to triples: RML](./09-mapping-tables-to-triples-rml.md)
turns CSV and JSON source data into RDF via a declarative mapping —
the last of this batch's four capabilities, with a sibling CSVW post
still to come for the tabular-data-with-metadata angle.

Every live cell above is pinned in
[`tests/hub/post08_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post08_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn`/`Factoidal` adapters.
