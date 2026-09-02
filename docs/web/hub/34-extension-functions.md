---
title: "Extension functions: your code inside the verified engine"
description: "SPARQL 1.1 §17.6 custom functions registered by IRI (the Comunica model): sync and async JavaScript bodies, a WebAssembly-bodied function, and a function whose body is itself F*-verified — with an honest account of exactly which parts of that pipeline are proved."
layout: hub.njk
series: docs-hub
series_order: 34
vocab: none
status: published
tests: tests/hub/post34_test.mjs
---

SPARQL has always had an extension seam: [§17.6 of the 1.1
spec](https://www.w3.org/TR/sparql11-query/#extensionFunctions) says a
query may call *any* function named by IRI, and an implementation that
does not know the IRI must return an error. This engine now fills that
seam the way [Comunica does](https://comunica.dev/docs/query/advanced/extension_functions/):
you register a JavaScript function — sync or async — under an IRI with
`fn.registerExtensionFunction(iri, f)`, and SPARQL expressions call it.

The dispatch itself is not JavaScript's decision. It is specified in
F\* ([`SPARQL11.Algebra.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL11.Algebra.fst)'s
`E_FunctionCall` arm, issue
[#463](https://github.com/danbri/factoidal/issues/463)): every
natively-implemented function family is tried first, the registry is
consulted **last**, and an IRI nobody registered is the spec-required
error. Your function receives its arguments already evaluated, as
SPARQL-Results-JSON-style term objects, and returns a term object, a
plain JS value, or a Promise of either.

## A two-person dataset

```observable-js
AGES_TTL = `
  @prefix : <http://example.org/> .
  :alice :name "Alice" ; :age 30 .
  :bob   :name "Bob"   ; :age 7 .
`
```

```observable-js
dataset = fn.parse(AGES_TTL)
```

## The error is the specification

Before registering anything, call a function that doesn't exist. §17.6
says that's an error — and in this engine's *total* evaluator, an
expression error is a value, not a crash: in `BIND` position the
variable comes out unbound; in `FILTER` position the row drops.

```observable-js
const bindRows = await fn.query(dataset, `
  # An unregistered extension function called in BIND: the error leaves
  # ?x unbound rather than failing the query.
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s ?x WHERE {
    ?s <http://example.org/age> ?a .
    BIND(fn:noSuchFunction(?a) AS ?x)
  }`);
const filterRows = await fn.query(dataset, `
  # The same unregistered function in FILTER: the error drops the row.
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s WHERE {
    ?s <http://example.org/age> ?a .
    FILTER(fn:noSuchFunction(?a))
  }`);
return {
  bindRowCount: bindRows.length,
  bindXBoundCount: bindRows.filter((r) => r.get("x") !== undefined).length,
  filterRowCount: filterRows.length,
};
```

Two `BIND` rows with `?x` bound in neither; zero `FILTER` rows.

## A synchronous function in FILTER

Register `fn:isAdult` and use it as a filter. The argument arrives as
a term object (`{type:"literal", value:"30", datatype:…}`); returning
a JS boolean is enough:

```observable-js
await fn.registerExtensionFunction(
  "http://example.org/fn#isAdult",
  ([age]) => Number(age.value) >= 18
);
const rows = await fn.query(dataset, `
  # fn:isAdult computes age >= 18; only rows where it holds survive the FILTER.
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s WHERE {
    ?s <http://example.org/age> ?a .
    FILTER(fn:isAdult(?a))
  }`);
return pretty(rows);
```

Alice only.

## An ASYNC function in BIND

Comunica's extension functions are async, and so are these — even
though the extracted engine underneath is a synchronous, total F\*
function. The bridge memoises each `(iri, arguments)` call and
re-evaluates the query until every pending Promise has resolved (a
bounded trampoline; the memo is also what guarantees the engine's
each-call-sees-one-stable-answer purity assumption). Your function
just uses `await`:

```observable-js
await fn.registerExtensionFunction(
  "http://example.org/fn#category",
  async ([age]) => {
    await new Promise((resolve) => setTimeout(resolve, 10));
    return { type: "literal", value: Number(age.value) >= 18 ? "adult" : "child" };
  }
);
const rows = await fn.query(dataset, `
  # fn:category classifies age as "adult" or "child"; the async function
  # must resolve before ?c gets its bound value.
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s ?c WHERE {
    ?s <http://example.org/age> ?a .
    BIND(fn:category(?a) AS ?c)
  }
  ORDER BY ?s`);
return pretty(rows);
```

## A WebAssembly-bodied function

The registered body is just a JavaScript function — so it can call
anything JavaScript can, including a WebAssembly instance. This cell
compiles a 49-byte wasm module (one exported `add : i32 × i32 → i32`)
and registers it as `fn:wasmAdd`; the SPARQL `SELECT` expression below
then computes inside WebAssembly:

```observable-js
const wasmBytes = new Uint8Array([
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,             // \\0asm v1
  0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f,       // (i32,i32)->i32
  0x03, 0x02, 0x01, 0x00,                                     // 1 func
  0x07, 0x07, 0x01, 0x03, 0x61, 0x64, 0x64, 0x00, 0x00,       // export "add"
  0x0a, 0x09, 0x01, 0x07, 0x00, 0x20, 0x00, 0x20, 0x01, 0x6a, 0x0b, // add impl
]);
const { instance } = await WebAssembly.instantiate(wasmBytes);
await fn.registerExtensionFunction(
  "http://example.org/fn#wasmAdd",
  ([a, b]) => instance.exports.add(Number(a.value), Number(b.value))
);
const rows = await fn.query(dataset, `
  # fn:wasmAdd adds 100 to each ?a, computed inside a WebAssembly instance.
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s (fn:wasmAdd(?a, 100) AS ?plus100) WHERE {
    ?s <http://example.org/age> ?a .
  }
  ORDER BY ?s`);
return pretty(rows);
```

`130` and `107` — arithmetic done by wasm, orchestrated by the
F\*-extracted evaluator.

## A function whose body is itself F\*-verified

That wasm `add` was hand-written and unverified — fine for a demo,
but it re-opens the question this whole project is about: *can the
function body be verified too?* Yes, when the body is F\* that was
extracted, exactly like the engine itself. This cell registers
`fn:sigmoid` whose implementation is
[`Math.Sigmoid.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/Math.Sigmoid.fst)
— a `Tot` (total, machine-checked terminating) fixed-precision
sigmoid, no floats anywhere — reached through the same extracted
bundle the engine runs in:

```observable-js
await fn.registerExtensionFunction(
  "http://example.org/fn#sigmoid",
  async ([x]) => {
    const pts = await fn.sigmoidPoints({
      k: "1", x0: "0", l: "1", xmin: x.value, xmax: x.value, n: 1,
    });
    return {
      type: "literal",
      value: pts[0].y.decimal,
      datatype: "http://www.w3.org/2001/XMLSchema#decimal",
    };
  }
);
const rows = await fn.query(dataset, `
  # fn:sigmoid computes the F*-verified sigmoid of ?a / 10 for each subject.
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s (fn:sigmoid(?a / 10) AS ?score) WHERE {
    ?s <http://example.org/age> ?a .
  }
  ORDER BY ?s`);
return pretty(rows);
```

σ(3.0) ≈ 0.95 for Alice, σ(0.7) ≈ 0.67 for Bob — every `exp` in
there computed by verified F\*, not by this page.

## What is actually verified here — and what is not

Be precise about the trust story, because the seam is the point:

- **The dispatch semantics are F\*-specified and verified.** Which
  IRIs reach the registry (only ones no native family claims), and
  what an unregistered IRI means (the §17.6 error), is proved
  machinery in `SPARQL11.Algebra.fst`. There are no `admit`s and no
  `--lax` anywhere in the engine.
- **The registry hook is an `assume val`** — an axiomatized host
  boundary (the same mechanism as file I/O and the SERVICE resolver),
  realised by ~20 lines of registry glue. It carries a stated
  contract: within one evaluation, each `(iri, args)` call sees one
  stable answer — which the bridge's memoisation enforces.
- **An arbitrary user function can never be verified by the engine**
  — it is arbitrary foreign code; that is the §17.6 deal on every
  SPARQL engine, and no amount of F\* changes it.
- **But a function body written in F\* is verified**, end to end:
  `fn:sigmoid` above runs `Math.Sigmoid.fst`'s proved-total code, so
  the only unverified links in that cell are the term-marshaling glue
  and the registry table. The roadmap issue
  ([#463](https://github.com/danbri/factoidal/issues/463)) tracks
  shrinking exactly that residue: a library of F\*-authored extension
  functions registered natively (no JS hop at all), with the
  marshaling done by the already-extracted SRJ serializers.

## Related

[Post 16](./16-the-verified-in-fstar-story.md) is the verification
story in full. [Post 28](./28-verified-math-rendered.md) is where
`Math.Sigmoid` came from. [Post 33](./33-correlated-federation-lateral-service.md)
does for `SERVICE` what this post does for functions.

The live cells above are pinned in
[`tests/hub/post34_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post34_test.mjs);
one layer down,
[`tests/unit/extension_function_unit.ml`](https://github.com/danbri/factoidal/blob/claude/main/tests/unit/extension_function_unit.ml)
pins the F\* dispatch with native OCaml closures, and
[`npm/factoidal/test/extension-functions.test.js`](https://github.com/danbri/factoidal/blob/claude/main/npm/factoidal/test/extension-functions.test.js)
pins the async trampoline.
