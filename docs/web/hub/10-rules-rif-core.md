---
title: "Rules over RDF: RIF Core"
description: "RIF frame rules as data, forward-chained live over two customer records — plus the boundary of the subset this project implements."
layout: hub.njk
series: docs-hub
series_order: 10
vocab: none
status: published
tests: tests/hub/post10_test.mjs
---

Every post so far reads a graph, queries it, or checks it against a
schema or a shape. RIF (Rule Interchange Format) does something
different: a RIF document *is itself data* — `<Forall>`/`<Frame>`/
`<Implies>` rules written in RIF-XML — and evaluating it means
forward-chaining those rules against a fact base until nothing new
follows. Where RDFS/OWL 2 RL closure (post 3) hard-codes a fixed rule
set inside the engine, RIF lets a document *author* its own rules.

## The subset this project implements

RIF Core is a full production-rule language. This project implements
the fragment its vendored W3C test cases actually exercise:
`Forall`/`Frame`/`And`/`Implies` rule bodies translated to SPARQL
basic graph patterns, forward-chaining fixpoint saturation, and
single-`<Import>` companion-graph resolution — see
[`docs/claude-rules/scope.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/claude-rules/scope.md)'s
RIF Core section for the exact boundary, including what's explicitly
**not** implemented (RIF-BLD built-ins beyond a numeric/string core,
list terms, RIF-PRD production actions). That honesty matters here
more than most posts: RIF is a big spec, and this is a real subset of
it, not the whole thing.

Measured against the full W3C RIF Core distribution (the original 4
vendored SPARQL-manifest cases plus the 46-test Core dialect corpus,
50 tests total): **34 pass, 4 labelled fails, 12 precise skips (of
50)** — see
[the test-results dashboard]({{ '/test-results/' | url }}) for the
current run and
[`bin/rif-runner/README.md`](https://github.com/danbri/factoidal/blob/claude/main/bin/rif-runner/README.md)
for what each of the 4 fails and 12 skips actually is (every skip
names the specific unimplemented builtin or construct — no blanket
"unsupported" lines). The subset in scope for the rest of this post —
frame/BGP rule bodies over ground facts — is squarely inside the 34
that pass.

## A frame rule, read as prose

RIF's `Frame` construct is the same idea as an RDF triple, written as
"object has slot: value" instead of subject-predicate-object. This
rule (mined directly from the W3C RIF Core test suite's `Frames` test
case, vendored at
[`third_party/testing/rif/tc/Frames/`](https://github.com/danbri/factoidal/blob/claude/main/third_party/testing/rif/tc/Frames/Frames-premise.rif))
says: *if a customer's status is "gold", that customer gets a 10%
discount*:

```xml
<Forall>
  <declare><Var>Customer</Var></declare>
  <formula>
    <Implies>
      <if>
        <Frame>
          <object><Var>Customer</Var></object>
          <slot ordered="yes">
            <Const type="&rif;iri">http://example.org/example#status</Const>
            <Const type="&xs;string">gold</Const>
          </slot>
        </Frame>
      </if>
      <then>
        <Frame>
          <object><Var>Customer</Var></object>
          <slot ordered="yes">
            <Const type="&rif;iri">http://example.org/example#discount</Const>
            <Const type="&xs;integer">10</Const>
          </slot>
        </Frame>
      </then>
    </Implies>
  </formula>
</Forall>
```

The real fixture pairs this with a second rule for `silver` status
(discount 5) and one ground fact (`customer017` is `gold`). Below,
both rules run live against two customers — one gold, one silver —
via `Factoidal.rifEval(rifRulesXml, dataNQuads)`
(`npm/factoidal/browser.js`'s raw RIF export, forward-chaining
saturation over `RIF.Core.Eval.fst`'s fixpoint). The call is wrapped
in a try/catch: an older engine bundle that predates the RIF export
would throw "the loaded factoidal-npm-entry bundle predates the RIF
exports" rather than silently produce nothing, so this cell reports
that instead of failing invisibly.

```observable-js
const rifRulesXml = `<?xml version="1.0" encoding="UTF-8"?>
<Document xmlns="http://www.w3.org/2007/rif#">
  <payload>
    <Group>
      <sentence>
        <Forall>
          <declare><Var>Customer</Var></declare>
          <formula>
            <Implies>
              <if>
                <Frame>
                  <object><Var>Customer</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://example.org/example#status</Const>
                    <Const type="http://www.w3.org/2001/XMLSchema#string">gold</Const>
                  </slot>
                </Frame>
              </if>
              <then>
                <Frame>
                  <object><Var>Customer</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://example.org/example#discount</Const>
                    <Const type="http://www.w3.org/2001/XMLSchema#integer">10</Const>
                  </slot>
                </Frame>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
      <sentence>
        <Forall>
          <declare><Var>Customer</Var></declare>
          <formula>
            <Implies>
              <if>
                <Frame>
                  <object><Var>Customer</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://example.org/example#status</Const>
                    <Const type="http://www.w3.org/2001/XMLSchema#string">silver</Const>
                  </slot>
                </Frame>
              </if>
              <then>
                <Frame>
                  <object><Var>Customer</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://example.org/example#discount</Const>
                    <Const type="http://www.w3.org/2001/XMLSchema#integer">5</Const>
                  </slot>
                </Frame>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
    </Group>
  </payload>
</Document>`;

const dataNQuads =
  '<http://example.org/example#customer017> <http://example.org/example#status> "gold" .\n' +
  '<http://example.org/example#customer017> <http://example.org/example#name> "John Doe" .\n' +
  '<http://example.org/example#customer042> <http://example.org/example#status> "silver" .\n' +
  '<http://example.org/example#customer042> <http://example.org/example#name> "Jane Roe" .\n';

try {
  const result = await Factoidal.rifEval(rifRulesXml, dataNQuads);
  const discountLines = result.saturatedNquads
    .split("\n")
    .filter((line) => line.includes("#discount"));
  return {
    available: true,
    inputCount: result.inputCount,
    derivedCount: result.derivedCount,
    discounts: discountLines,
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

Four input facts (two customers, each with a status and a name), two
derived facts — `customer017` gets the gold rule's 10, `customer042`
gets the silver rule's 5. Neither discount triple was asserted
anywhere in the data; both came purely from forward-chaining the two
rules to a fixpoint.

## No matching status, no discount

The rules only fire when their `if` frame actually matches. A third
customer with a status the rules don't mention (`bronze`) should
derive nothing:

```observable-js
const rifRulesXml = `<?xml version="1.0" encoding="UTF-8"?>
<Document xmlns="http://www.w3.org/2007/rif#">
  <payload>
    <Group>
      <sentence>
        <Forall>
          <declare><Var>Customer</Var></declare>
          <formula>
            <Implies>
              <if>
                <Frame>
                  <object><Var>Customer</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://example.org/example#status</Const>
                    <Const type="http://www.w3.org/2001/XMLSchema#string">gold</Const>
                  </slot>
                </Frame>
              </if>
              <then>
                <Frame>
                  <object><Var>Customer</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://example.org/example#discount</Const>
                    <Const type="http://www.w3.org/2001/XMLSchema#integer">10</Const>
                  </slot>
                </Frame>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
    </Group>
  </payload>
</Document>`;

const dataNQuads =
  '<http://example.org/example#customer099> <http://example.org/example#status> "bronze" .\n' +
  '<http://example.org/example#customer099> <http://example.org/example#name> "Sam Bronze" .\n';

try {
  const result = await Factoidal.rifEval(rifRulesXml, dataNQuads);
  return {
    available: true,
    inputCount: result.inputCount,
    derivedCount: result.derivedCount,
    rounds: result.rounds,
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

Two input facts, zero derived — `derivedCount: 0`. The rule engine
doesn't guess; a frame rule that doesn't match produces nothing,
exactly the way a SPARQL query with no matching bindings returns an
empty result set rather than a fabricated one.

## What's next

[The next post](./11-one-graph-five-syntaxes.md) leaves rules behind
and goes back to plain syntax — parsing the same graph from five
different concrete RDF syntaxes and showing the bytes converge.

Every live cell above is pinned in
[`tests/hub/post10_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post10_test.mjs),
executed against the real npm-entry ABI the same way the in-browser
`Factoidal` binding is, rather than a hand-copied approximation.
