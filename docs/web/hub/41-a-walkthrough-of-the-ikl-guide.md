---
title: "A walkthrough of the IKL GUIDE"
description: "The Lean 4 CLIF reader parses worked examples straight from Pat Hayes and Chris Menzel's IKL GUIDE, section by section, live in the browser."
layout: hub.njk
series: docs-hub
series_order: 41
vocab: none
status: published
tests: tests/hub/post41_test.mjs
---

[Common Logic (CL)](https://www.iso.org/standard/66249.html) and
[IKL](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) — Pat
Hayes and Chris Menzel's extension of it — are read by a CLIF reader
implemented in Lean 4. This page is the tutorial: it works through the
[IKL GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html)
itself, section by section, quoting the GUIDE's own prose and parsing
the GUIDE's own examples with the same reader, live.

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

It parses (`pureCL` is `false`, as any `that`-bearing sentence is).

## What identity does not include

Appendix B, "Identity Conditions for Propositions," fixes bound-name
renaming as the floor on propositional identity, stated directly:
"a change of bound names in a sentence does not change the proposition
expressed by the sentence, so that for example `(that (exists
(x)(loves Jim x)))` equals `(that (exists (y)(loves Jim y)))`." That
much is a naming-independent fact about the two sentences, provable
from the CLIF grammar alone — it needs no RDF projection to state or
check.

Appendix B then goes further, adding a separate, DEFINED relation for
a wider set of equivalences: `=p` holds of commuted conjunction —
`(=p (that (and PHI RHO)) (that (and RHO PHI)) )` — as one of several
axioms the GUIDE lists explicitly, allowing "propositional identity to
be defined by axioms," with `=p` "the smallest relation satisfying all
these conditions." Bound-name renaming and `=p`-commutativity are
different claims of different strength: the first follows from the
grammar of quantification, the second is an axiom asserted on top of
it. Recovering that second, wider relation from an RDF encoding is
tracked at [issue 589](https://github.com/danbri/factoidal/issues/589)
and is not demonstrated on this page.

## Closing

Every CLIF text on this page is quoted or directly adapted from the
[IKL GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html)
(Hayes and Menzel): "Description logics translate into IKL relational
operators" for ground predication; "Forms of quantifiers" for the
restricted-binder abbreviation; "Proposition names" for the
cancelling-parentheses assertion and quantifying-in; Appendix B for
the bound-name-renaming floor and the `=p` commutativity axiom. One
place said plainly where the reader's covered fragment (`CL/
Syntax.lean`) stops short of the GUIDE's own text: the `cl:text`
phrase-structure boundary. The wider CL/IKL port is tracked at [issue
580](https://github.com/danbri/factoidal/issues/580); proposition
individuation — bound-name renaming versus the GUIDE's stronger `=p`
— at [issue 589](https://github.com/danbri/factoidal/issues/589).
