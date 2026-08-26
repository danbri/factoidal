---
title: "A little IKL walkthrough"
description: "One squirrel story, told twice, in short question-and-answer steps: quoted words are evidence, `that`-terms are propositions, and the step between them is where a case against Jon is made or lost."
layout: hub.njk
series: docs-hub
series_order: 44
vocab: none
status: published
tests: tests/hub/post44_test.mjs
---

[Post 41](../41-a-walkthrough-of-the-ikl-guide/) tours the [IKL
GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) section
by section. This page does something smaller. It takes one story and
writes it down twice, one short step at a time, with a question before
each step and the engine's answer after it.

The story: Foxworth the squirrel hid nuts. Bram says words about it.
Clud passes those words on. In one telling the words put Jon at the
cache, which makes Jon a suspect. In the other telling the same words
came out of a mix-up, and Jon was never near the cache.

Every cell on this page calls one operation, `clParse`. It reads
[CLIF](https://www.iso.org/standard/66249.html) text and reports what
it read. It does not evaluate, translate, or infer.

## 1. The words

**What did Bram produce — a proposition, or a string of words?**

A string of words. Write it as a CLIF quoted string, in single quotes.

```observable-js
testimony = "(uttered Bram 'I saw Jon watching Foxworth by the nut tree')"
```

```observable-js
testimonyParse = fn.l4Call("clParse", [testimony])
```

**Why single quotes and not double quotes?**

The two marks do different jobs in
[CLIF](https://www.iso.org/standard/66249.html), and the assignment is
the reverse of the C and Java convention. Single quotes make a *quoted
string*: a sequence of Unicode characters with a fixed meaning, which
the GUIDE describes as denoting "a particular sequence of ... Unicode
characters, and cannot mean anything else." Double quotes make an
*enclosed name*: an ordinary logical name that happens to contain
spaces or punctuation, which "function[s] logically just like any
other name."

**So what can the logic see inside the single quotes?**

Nothing. `Jon` inside `'I saw Jon watching Foxworth by the nut tree'`
is three characters of a character sequence. No variable can bind it.
No name can be equated with it. That is the property the page is
about: the words are the record of what was said, and deciding what
they mean is a later step that can go wrong.

**`pureCL` reads `true`. Why?**

Nothing so far uses an IKL construct. Quoted strings are
[ISO/IEC 24707](https://www.iso.org/standard/66249.html) Common Logic.
The flag turns to `false` at the first `that`-term, and that boundary
is the subject of the rest of the page.

## 2. What Clud has

**Clud is the one reporting all this. What does Clud have?**

Clud has the event of Bram speaking, not the content of what Bram
said.

```observable-js
cludEvidence = "(witnessed Clud (that (uttered Bram 'I saw Jon watching Foxworth by the nut tree')))"
```

```observable-js
cludEvidenceParse = fn.l4Call("clParse", [cludEvidence])
```

**`pureCL` flipped to `false`. What flipped it?**

`that`. The GUIDE calls `(that S)` "a syntactic form which makes a
sentence into the name of the corresponding proposition." Clud
witnessed a proposition, so a proposition needs a name, so the
sentence needs `that`. This sentence holds in both tellings of the
story. It is the part nobody disputes.

## 3. The rule that governs `that`

**Can a `that`-term be the argument of another `that`?**

No, and the engine says why.

```observable-js
doubleThat = "(believes Clud (that (that (guilty Jon))))"
```

```observable-js
doubleThatAttempt = {
  try { return await fn.l4Call("clParse", [doubleThat]); }
  catch (e) { return { ok: false, message: e.message }; }
}
```

The message reads `'(that S)' is a term; to assert the proposition
write '((that S))' (offset 21)`.

**Why is that the rule?**

`that` takes a sentence and yields a term. `(that (guilty Jon))` is
already a term, so it cannot be handed to `that` again. To get a
sentence back out of a term, the GUIDE uses a second pair of
parentheses — `((that (guilty Jon)))` — which cancels the reification
and "means exactly the same as the inner sentence." Operator position
asserts. Argument position mentions.

## 4. Scenario A: the chain that incriminates

**Can `that` nest at all, then?**

Yes, when each `that` wraps a sentence. Put a predication between the
two and the nesting is legal.

```observable-js
scenarioA = "(witnessed Clud (that (saw Jon (that (cached Foxworth 'the beech hollow')))))"
```

```observable-js
scenarioAParse = fn.l4Call("clParse", [scenarioA])
```

**Read it back in English.**

Clud witnessed that Jon saw that Foxworth cached the nuts in the beech
hollow. Three layers: Clud's witnessing, Jon's seeing, Foxworth's
caching. The inner `that` is the argument of `saw`, and the outer
`that` is the argument of `witnessed`. Between them sits `saw Jon ...`,
which is a sentence.

**Where is the cache location?**

In a quoted string again, `'the beech hollow'`. The page keeps it
there because it is a place-name in reported words, not a logical
constant this text needs to reason with.

## 5. Why scenario A is evidence

**Does the engine know that witnessing something makes it true?**

No. Witnessing is factive, and factivity is an axiom you write.

```observable-js
factivity = "(forall (a p) (if (witnessed a p) (p)))"
```

```observable-js
factivityParse = fn.l4Call("clParse", [factivity])
```

**`pureCL` is `true` here. But `p` stands for a proposition.**

The parentheses around `p` are the same cancelling parentheses as in
step 3, applied to a variable. Common Logic is unsegregated: a name
can occur in argument position and in operator position, so `(p)` is a
sentence in plain CL with no IKL extension in it. That is what keeps
the flag at `true`.

**What does the axiom buy?**

With it, scenario A puts Jon at the cache: Clud witnessed that Jon saw
where the nuts went, so Jon saw where the nuts went. Without it, the
same text says only that Clud witnessed something. The engine supplies
neither reading. The axiom is a claim about the word `witnessed` and
somebody has to make it.

## 6. A proposition about an individual you cannot name

**Suppose Clud thinks some squirrel is guilty but cannot say which.**

Bind a variable outside the `that` and use it inside.

```observable-js
quantifyIn = "(exists (x) (and (squirrel x) (believes Clud (that (guilty x)))))"
```

```observable-js
quantifyInParse = fn.l4Call("clParse", [quantifyIn])
```

**Why does this work inside `that` and not inside `'...'`?**

The GUIDE states the contrast directly: inside a `that`-term "the
'inner' names of the sentence are still visible to other operations,
and can for example be bound by quantifiers." Inside a quoted string
they are characters, and `(exists (x) ... 'x is guilty' ...)` binds
nothing. A `that`-term is transparent to the logic around it. A quoted
string is opaque to it.

## 7. The constraint that decides the design

**Then can the mix-up be written as Clud believing one thing under one
name and not under another?**

No. IKL is referentially transparent, and the GUIDE says what follows
from that. Take `(= Bill William)`:

> then it follows — in fact, it is the same assertion — that
> `(Believes Harry (that (isLiar William)))` … and this holds whether
> or not Harry knows Bill by his other name. This follows from the
> transparent and panoptic nature of IKL.

```observable-js
transparency = "(and (= Foxworth OldGrey) (believes Clud (that (cached Foxworth 'the beech hollow'))))"
```

```observable-js
transparencyParse = fn.l4Call("clParse", [transparency])
```

**What does that text say about Clud?**

Given the identity, it says that Clud believes the proposition, and
the same sentence with `OldGrey` in place of `Foxworth` states the
same belief. Clud's not knowing the second name changes nothing. The
transparency the GUIDE describes is what step 6 relies on; it is also
what closes off belief-opacity as a way to write down a
misunderstanding.

**Then where does the misunderstanding go?**

One level down, into which proposition a given string of words
expresses. That relation holds between a quoted string and a
`that`-term, and it does not have to be single-valued. This is why the
page put Bram's testimony in single quotes in step 1.

## 8. Scenario B: one string, two readings

**Write the two readings of the same words.**

```observable-js
scenarioB = `(and
  (uttered Bram 'I saw Jon watching Foxworth by the nut tree')
  (readAs 'I saw Jon watching Foxworth by the nut tree'
          (that (saw Jon (that (cached Foxworth 'the beech hollow')))))
  (readAs 'I saw Jon watching Foxworth by the nut tree'
          (that (saw Bram (that (watched Jon Foxworth))))))`
```

```observable-js
scenarioBParse = fn.l4Call("clParse", [scenarioB])
```

**What is the difference between the two readings?**

The first reading is scenario A's chain: Jon saw the caching, so Jon
knows where the nuts are. The second reading says only that Bram saw
Jon looking at Foxworth. It places Jon in Foxworth's line of sight and
nowhere near the beech hollow. It clears Jon of the caching evidence.

**Are both readings consistent with the words Bram said?**

Yes. The string is the same string in both `readAs` sentences. The
argument is over which proposition it expresses, and nothing in the
character sequence settles it.

## 9. Where the second reading comes from

**Make the mix-up concrete.**

Wren saw two other squirrels at the nut tree and described them
without names. Bram heard the description, supplied the names Jon and
Foxworth, and retold it in the first person.

```observable-js
mixup = `(and
  (uttered Wren 'the grey one was watching the other by the nut tree')
  (readAs 'the grey one was watching the other by the nut tree'
          (that (watched Nib Quill)))
  (heard Bram 'the grey one was watching the other by the nut tree')
  (retold Bram 'the grey one was watching the other by the nut tree'
              'I saw Jon watching Foxworth by the nut tree'))`
```

```observable-js
mixupParse = fn.l4Call("clParse", [mixup])
```

**Which step is the wrong one?**

`retold`. Wren's words read as a proposition about Nib and Quill. The
string Bram produced reads as a proposition about Jon and Foxworth.
Every other step in the chain is intact: Wren did see two squirrels,
Bram did hear the words, Clud did witness Bram speaking. The failure
is at one string-to-string move and it leaves no mark in the strings
themselves.

**Does the text say the retelling was wrong?**

No. It says a retelling happened and records the two readings. To make
the case against Jon collapse, add the axiom that a retelling
preserves the proposition, and the text becomes contradictory; leave
it out, and the incriminating reading is unsupported. Both moves are
the reader's to make.

## 10. The axiom scenario B declines

**Is there an axiom that would rule the mix-up out?**

Yes: say that a string determines its proposition.

```observable-js
readAsFunctional = "(forall (s p q) (if (and (readAs s p) (readAs s q)) (= p q)))"
```

```observable-js
readAsFunctionalParse = fn.l4Call("clParse", [readAsFunctional])
```

**Read it back.**

If a string reads as `p` and the same string reads as `q`, then `p`
and `q` are the same proposition. Scenario B's two `readAs` sentences
name different propositions, so scenario B is a text that does not
include this axiom. `pureCL` is `true` again: three variables, a
conditional and an equation, no IKL construct anywhere.

**Does anything force a choice between the two scenarios?**

Not on this page. `clParse` reads CLIF text and reports its structure.
Both scenarios parse. Choosing between them is the work the logic is
written down to support, and it is done with axioms and evidence that
this page states rather than assumes.

## Closing

The `pureCL` flag tracked the boundary the whole way. It read `true`
while the text quoted words (steps 1, 5 and 10) and `false` from the
first `that`-term onward (steps 2, 4, 6, 7, 8 and 9). Quoted strings
carry what was said. `that`-terms carry what is believed, seen and
witnessed. `readAs` is the step between them, and it is the step the
squirrel story breaks.

The devices are matched to that division rather than interchangeable.
Because IKL is transparent — the GUIDE's `(= Bill William)` passage —
a description-sensitive confusion cannot be stated inside a
`that`-term. It has to be stated about a string. So the witness
produces characters, and the reading of those characters is a separate,
defeasible claim.

Quotations are from Hayes and Menzel's [IKL
GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html):
"Special IKL name forms" for the quoted-string and enclosed-name
contrast, "Proposition names" for `that`, the cancelling-parentheses
form and quantifying-in, and the transparency passage in the same
section. The lexical distinction between `'...'` and `"..."` is
[ISO/IEC 24707](https://www.iso.org/standard/66249.html). The wider
CL/IKL port is tracked at [issue
580](https://github.com/danbri/factoidal/issues/580).
