---
title: "A walkthrough of the IKL GUIDE"
description: "The Lean 4 CLIF reader parses and translates worked examples straight from Pat Hayes and Chris Menzel's IKL GUIDE, section by section, live in the browser."
layout: hub.njk
series: docs-hub
series_order: 41
vocab: none
status: published
tests: tests/hub/post41_test.mjs
---

[Post 39](../39-propositions-as-first-class-citizens/) introduced the
reader for [Common Logic (CL)](https://www.iso.org/standard/66249.html)
and [IKL](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html), Pat
Hayes and Chris Menzel's extension of it, with one CLIF sentence and
one translation. This page is the tutorial: it works through the [IKL
GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) itself,
section by section, quoting the GUIDE's own prose and parsing and
translating the GUIDE's own examples with the same reader, live.

A few of the GUIDE's constructs sit outside what this reader covers —
numeric quantifiers (`(exists 3 (y) ...)`), the `cl:text`/`cl:module`/
`cl:imports`/`cl:comment` phrase forms, functional terms used as a
predication subject. Each place that happens below says so once, at
the point it happens, and moves on.

## What the reader will not read

Before the tour starts, one boundary. [ISO/IEC
24707](https://www.iso.org/standard/66249.html) wraps a body of CL
text in `cl:text`/`cl:comment`/`cl:module`/`cl:imports` phrase forms —
the namespace-qualified spelling of the unprefixed `text`/`comment`
forms the GUIDE's own Appendix A uses to wrap its structural axioms
("It is written entirely as commented IKL text"). This reader parses
single sentences and flat sentence sequences (`CL/Syntax.lean`'s
covered fragment); it does not parse that enclosing structure, so
asking it to read one exercises the boundary directly.

```observable-js
moduleForm = '(cl:text "demo" (P a))'
```

```observable-js
moduleAttempt = {
  try { return await fn.l4Call("clParse", [moduleForm]); }
  catch (e) { return { ok: false, message: e.message }; }
}
```

The error names the reason and the tracking issue:
`'cl:text' phrases are not covered by this reader (issue 580)`. The
engine stays alive afterward — every op call below runs against the
same module.

## Predication and names (GUIDE "IKL Overview")

CLIF — Common Logic Interchange Format — is, in the GUIDE's own words,
written "in 'Lisp style', with the relation or function name after the
opening parenthesis, and with names separated by whitespace rather
than commas." Ground facts are the simplest sentences it has: the
GUIDE's "Description logics translate into IKL relational operators"
section gives two, back to back — "Ground facts (often called 'A-box'
sentences in the DL literature) such as membership in a class, or a
property having a value, are represented as a simple atomic sentences
such as `(isHuman "Osama bin Laden")(childOf "Osama bin Laden" "Hamida
al-Attas")`."

```observable-js
groundFacts = '(isHuman "Osama bin Laden")(childOf "Osama bin Laden" "Hamida al-Attas")'
```

```observable-js
groundParse = fn.l4Call("clParse", [groundFacts])
```

`sentences` reads 2 — one text, two sentences — and `pureCL` is
`true`: nothing here is IKL-specific, it is [ISO/IEC
24707](https://www.iso.org/standard/66249.html) CL proper. The double
quotes around `"Osama bin Laden"` are CLIF's [enclosed
name](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) form — a
normal name spelled with whitespace, not the single-quoted [quoted
string](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) that
the GUIDE distinguishes carefully in "Special IKL name forms": an
enclosed name "function[s] logically just like any other name," while
a quoted string "denotes a particular sequence of ... Unicode
characters, and cannot mean anything else." `normalized` re-encloses
both names on the way back out, unchanged in meaning.

## Quantifier forms

The GUIDE's "Forms of quantifiers" section adds a restriction to a
quantifier binding by writing `(name term)` inside the binding list,
"an abbreviation" the GUIDE spells out directly:
`(forall ((x isHuman))(exists ((y charseq))(= y (nameOf x)) ))`.

```observable-js
restrictedQuant = "(forall ((x isHuman))(exists ((y charseq))(= y (nameOf x))))"
```

```observable-js
restrictedParse = fn.l4Call("clParse", [restrictedQuant])
```

`pureCL` is `true` — restricted binders are CLIF sugar, not an IKL
extension — and `normalized` shows the reader's own spacing of the
same restricted forms, `(forall ((x isHuman)) (exists ((y charseq)) (=
y (nameOf x))))`.

Appendix B, "Identity Conditions for Propositions," states the
individuation floor for `(that S)` terms directly: "a change of bound
names in a sentence does not change the proposition expressed by the
sentence, so that for example `(that (exists (x)(loves Jim x)))`
equals `(that (exists (y)(loves Jim y)))`." Below, both variants go
through `clToDataset` — the CL→RDF bridge (`CL/ToRdf.lean`) that names
a proposition's graph by the SHA-256 of its alpha-normalized canonical
CLIF.

```observable-js
lovesX = "(believes K (that (exists (x)(loves Jim x))))"
```

```observable-js
lovesY = "(believes K (that (exists (y)(loves Jim y))))"
```

```observable-js
lovesXDs = fn.l4Call("clToDataset", [lovesX, "urn:cl:"])
```

```observable-js
lovesYDs = fn.l4Call("clToDataset", [lovesY, "urn:cl:"])
```

```observable-js
graphNameOf = (nq) => nq.match(/urn:cl:that:sha256:[0-9a-f]{64}/)[0]
```

```observable-js
alphaPin = {
  const gx = graphNameOf(lovesXDs.nquads);
  const gy = graphNameOf(lovesYDs.nquads);
  return { graphOfX: gx, graphOfY: gy, sameGraph: gx === gy };
}
```

`sameGraph` reads `true`: the `x`-bound and `y`-bound sentences name
the SAME graph, exactly the identity the GUIDE's Appendix B fixes as a
minimum and [issue
589](https://github.com/danbri/factoidal/issues/589) tracks as the
engine's individuation rule — bound-variable renaming does not change
which proposition a `(that S)` term names.

## Proposition names and `(that S)`

The GUIDE's "Proposition names" section introduces the construct that
makes IKL more than Common Logic: "a syntactic form which makes a
sentence into the name of the corresponding proposition, by enclosing
it inside parentheses, preceded by the special IKL reserved word
`that`." To assert a proposition rather than merely name it, the GUIDE
adds a second pair of parentheses around the name, "cancelling" the
reification: `((that (isHuman "Brant Cheikes")))` — its own example —
"is such an atomic sentence, which means exactly the same as the inner
sentence."

```observable-js
cheikes = '((that (isHuman "Brant Cheikes")))'
```

```observable-js
cheikesParse = fn.l4Call("clParse", [cheikes])
```

`pureCL` is `false`: the cancelling-parentheses form is IKL, not plain
CL, even though it asserts nothing an ordinary sentence could not.

The GUIDE's "Proposition names are referentially transparent" section
gives the family this page's translation targets — a proposition as
the object of an ordinary relation. First, on names inside a
proposition referring the same way they do outside one: "if `(= Bill
William)` then it follows that propositions about Bill are also about
William." Then, its own example of the consequence for `believes`:
"if Bill is in fact the same as William, and `(Believes Harry (that
(isLiar Bill)))` then it follows — in fact, it is the same assertion —
that `(Believes Harry (that (isLiar William)))`."

```observable-js
harryBill = "(Believes Harry (that (isLiar Bill)))"
```

```observable-js
harryBillDs = fn.l4Call("clToDataset", [harryBill, "urn:cl:"])
```

`count` is 2, `skipped` is 0: the link triple `urn:cl:Harry
urn:cl:Believes <propIri>` in the default graph, and `urn:cl:Bill
rdf:type urn:cl:isLiar` inside the named graph the proposition IRI
names. This page does not run the equality reasoning the GUIDE's
transparency claim depends on (`Bill` and `William` are two different
CLIF names here, translated to two different IRIs) — that is a
separate question from the naming rule section 6 below returns to.

## Quantifying-in

"Quantifying in" is the GUIDE's name for a proposition ABOUT a
particular, unnamed individual — an outer quantifier binding a
variable that reappears free inside a `(that S)` term. Its own
example, from "Proposition names": `(exists (x) (Believes "Lois Lane"
(that (= x Superman)) ))`.

```observable-js
loisLane = '(exists ((x isHuman)) (Believes "Lois Lane" (that (= x Superman)) ))'
```

```observable-js
loisParse = fn.l4Call("clParse", [loisLane])
```

It parses (`pureCL` is `false`, as any `that`-bearing sentence is),
but `clToDataset` translates only specific top-level shapes — an
atomic sentence, or `(pred subj (that S))` — and a top-level
quantified sentence, this one included, is outside that fragment: the
whole sentence is skipped and counted, not partially translated. What
DOES translate is a `that`-term whose OWN sentence contains a
quantifier, which the GUIDE gives right next to its quantifying-in
example, as the weaker, de dicto contrast: "Bill believes that some
such Iranian exists," `(believes Bill_Andersen (that (exists ((x
Iranian))(and (customer x "Bank Melli Iran") (exists 3 ((y
aircraft))(owns x y)) ))) )`. Below drops the closing `(exists 3
((y aircraft))(owns x y))` conjunct — a numeral-headed quantifier,
outside this reader's covered fragment — and keeps the rest.

```observable-js
deDicto = '(believes Bill_Andersen (that (exists ((x Iranian))(customer x "Bank Melli Iran"))))'
```

```observable-js
deDictoDs = fn.l4Call("clToDataset", [deDicto, "urn:cl:"])
```

`count` is 1 (the link triple `Bill_Andersen believes <propIri>`) and
`skipped` is 1 (the restricted existential body is not itself atomic,
so it is not turned into a triple). The sentence text is still
recorded inside the named graph, as the sentence-record triple, and
can be queried back out.

```observable-js
rows = (r) => r.srj.results.bindings.map(
  (b) => Object.fromEntries(Object.entries(b).map(([k, t]) => [k, t.value])))
```

```observable-js
deDictoSentence = {
  const r = await fn.l4Call("queryDataset", [deDictoDs.nquads,
    "SELECT ?sentence WHERE { GRAPH ?g { ?g <urn:cl:def:sentence> ?sentence } }"]);
  return rows(r);
}
```

One row, `(exists ((v1 Iranian)) (customer v1 "Bank Melli Iran"))` —
the alpha-normalized canonical form (`x` renamed to `v1`) of the
sentence that never made it into a triple, recovered as data.

## Contexts via `ist`

"Contexts and modalities in IKL" gives `ist` — "is true in" — as the
uniform way to relate a context to a proposition: `(ist
TemporalContextDay06-16-2006 (that (Dead Osama-Bin-Laden)))`, glossed
as "a natural IKL rendering of the ICL sentence `(Dead
Osama-Bin-Laden)` asserted in a context TemporalContextDay06-16-2006."
A footnote to the same example gives a "more realistic" context name,
built from the XML Schema datatype convention: `(ist (TemporalContext
(xsd:dateTime '2002-10-10-T12:00:00-05:00')) (that (Dead
Osama-Bin-Laden)))`.

```observable-js
xsdContext = "(ist (TemporalContext (xsd:dateTime '2002-10-10-T12:00:00-05:00')) (that (Dead Osama-Bin-Laden)))"
```

```observable-js
xsdContextDs = fn.l4Call("clToDataset", [xsdContext, "urn:cl:"])
```

It parses, but `count` comes back 0 and `skipped` 1: `clToDataset`'s
`(pred subj (that S))` clause needs `subj` to be a plain CLIF name,
and `(TemporalContext (xsd:dateTime ...))` is a functional term, not a
name. Simplified to the GUIDE's own earlier, bare-name context —
dropping the datatype function, keeping the same relation and
proposition — the sentence translates in full.

```observable-js
simpleContext = "(ist TemporalContextDay06-16-2006 (that (Dead Osama-Bin-Laden)))"
```

```observable-js
simpleContextDs = fn.l4Call("clToDataset", [simpleContext, "urn:cl:"])
```

`count` is 2, `skipped` is 0. A `GRAPH` pattern reads inside the
context's proposition directly:

```observable-js
contextQuery = {
  const r = await fn.l4Call("queryDataset", [simpleContextDs.nquads,
    "SELECT ?g ?s WHERE { GRAPH ?g { ?s a <urn:cl:Dead> } }"]);
  return rows(r);
}
```

One row: the proposition's graph name, and `urn:cl:Osama-Bin-Laden` as
the subject the context's content is about.

## What identity does not include

Appendix B fixes bound-variable renaming as the floor on propositional
identity, then adds a separate, DEFINED relation for a further set of
equivalences. `=p` holds of commuted conjunction —
`(=p (that (and PHI RHO)) (that (and RHO PHI)) )` — as one of several
axioms the GUIDE lists explicitly: it allows "propositional identity
to be defined by axioms," and `=p` is "the smallest relation
satisfying all these conditions" — commutativity of `and` among them.
This is a
different, wider relation than the alpha-variant naming rule above;
the engine's `propIri` hashing computes the narrower one.

```observable-js
commutedPQ = "(believes K (that (and (P a)(Q a))))"
```

```observable-js
commutedQP = "(believes K (that (and (Q a)(P a))))"
```

```observable-js
commutedDsPQ = fn.l4Call("clToDataset", [commutedPQ, "urn:cl:"])
```

```observable-js
commutedDsQP = fn.l4Call("clToDataset", [commutedQP, "urn:cl:"])
```

```observable-js
commutedNames = {
  const gx = graphNameOf(commutedDsPQ.nquads);
  const gy = graphNameOf(commutedDsQP.nquads);
  return { graphOfPQ: gx, graphOfQP: gy, sameGraph: gx === gy };
}
```

`sameGraph` reads `false`: today, `propIri` hashes the alpha-normalized
CLIF text as written, and `(and (P a)(Q a))` is not the same text as
`(and (Q a)(P a))`. The GUIDE puts this identification in `=p`, a
relation this reader does not compute; [issue
589](https://github.com/danbri/factoidal/issues/589) tracks
generalizing proposition naming from alpha-equivalence toward `=p`.

## Finale: a small GUIDE-flavoured KB

One join, using everything above: an RDF triple the CL text never
mentions, and a CL text — a `worksAt` fact plus a `believes`/`that`
proposition, in the "ground facts" and "proposition names" styles this
page opened with — that never mentions RDF.

```observable-js
orgLabel = '<urn:cl:Acme> <http://www.w3.org/2000/01/rdf-schema#label> "Acme Corp" .\n'
```

```observable-js
orgClif = "(and (worksAt Alice Acme)(believes Alice (that (Trustworthy Acme))))"
```

```observable-js
orgSparql = `PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?employee ?label WHERE {
  ?company rdfs:label ?label .
  SERVICE <urn:ikl:kb> { ?employee <urn:cl:worksAt> ?company ; <urn:cl:believes> ?g }
  GRAPH ?g { ?company a <urn:cl:Trustworthy> }
}`
```

```observable-js
orgJoined = {
  const r = await fn.l4Call("queryWithIklService", [orgLabel, orgClif, orgSparql]);
  return rows(r);
}
```

One row: `urn:cl:Alice`, `"Acme Corp"`. The default-graph pattern reads
the RDF label; the `SERVICE` pattern reads the CL translation's
`worksAt` and `believes` link triples; the `GRAPH` pattern reads inside
the believed proposition to confirm it is about the same company. None
of the three sources alone answers the query.

## Closing

Every CLIF text on this page is quoted or directly adapted from the
[IKL GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html)
(Hayes and Menzel): "Description logics translate into IKL relational
operators" for ground predication; "Forms of quantifiers" for the
restricted-binder abbreviation; Appendix B for the alpha-variant pin
and the `=p` commutativity axiom; "Proposition names" for the
cancelling-parentheses assertion, the transparency example, and
quantifying-in; "Contexts and modalities in IKL" for `ist`. Three
places said plainly where the reader's covered fragment (`CL/
Syntax.lean`) stops short of the GUIDE's own text: the `cl:text`
phrase-structure boundary, the numeral-headed quantifier `(exists 3
...)` dropped from the de dicto belief example, and the
`xsd:dateTime`-built context name simplified to a bare context name.
The wider CL/IKL port is tracked at [issue
580](https://github.com/danbri/factoidal/issues/580); proposition
individuation — the alpha-normalized naming this page pins, and the
GUIDE's stronger `=p` as a follow-up — at [issue
589](https://github.com/danbri/factoidal/issues/589).
