---
title: "Wikifunctions inside the query: two F* engines, one SPARQL seam"
description: "Real Wikifunctions — the wikifn-fstar corpus, translated to F*, checked, and extracted to JavaScript — registered as SPARQL §17.6 extension functions in this engine's FILTER and BIND clauses. Two independently F*-checked codebases meeting at one verified dispatch seam, live in this page."
layout: hub.njk
series: docs-hub
series_order: 35
vocab: none
status: published
tests: tests/hub/post35_test.mjs
---

[Post 34](./34-extension-functions.md) added SPARQL 1.1 §17.6
extension functions and ended on a question: the *dispatch* is
F\*-verified, but can the function *bodies* be too? Here is the
strongest available answer running live: the extension functions in
this page are **real Wikifunctions**, served by
[wikifn-fstar](https://github.com/danbri/wikifn-fstar) — the
Wikifunctions corpus translated into F\*, **checked by F\***,
extracted to OCaml, compiled to JavaScript. Two codebases that have
never heard of each other, each machine-checked by the same proof
assistant, meeting at one SPARQL seam:

- **This engine** (the SPARQL side): F\*-specified evaluator,
  extracted; the §17.6 dispatch — which IRIs reach the registry,
  unknown IRI = error — is proved machinery.
- **wikifn-fstar** (the function side): each of its compiled
  compositions is an F\* definition that F\* checks; `fn:Z10096(...)`
  below is a function call into that artifact, not a tree-walk. Where
  a ZID has no compiled form, the call falls back to its interpreter
  and the page *says so* rather than quietly answering differently.

The original demo of that artifact drives it from
[Comunica](https://danbri.github.io/wikifn-fstar/demo-sparql.html) via
`extensionFunctionCreator`; this page is the same integration story on
this engine's `fn.registerExtensionFunction`. The engine bundle is
vendored (snapshot + sha256 + licence in
[`assets/wikifn/README.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/web/hub/assets/wikifn/README.md)),
so nothing here calls the network.

## Why canals

Borrowed gratefully from the wikifn-fstar demo: a canal is a passage
you can transit in either direction; a palindrome is a string you can
read in either direction; the Panama Canal is where those facts meet,
thanks to Leigh Mercer's *"a man, a plan, a canal: Panama"* — a
palindrome only once the spaces go. So: waterways, each with a phrase,
and queries that ask which phrases survive being read backwards. That
is two Wikifunctions composed: `Z10052` (remove spaces), then
`Z10096` (is it a palindrome).

```observable-js
WATERWAYS_TTL = `
  @prefix : <https://example.org/waterway#> .

  :panama  :name "Panama Canal"   ; :country "Panama"  ; :opened 1914 ;
           :phrase "a man a plan a canal panama" .
  :suez    :name "Suez Canal"     ; :country "Egypt"   ; :opened 1869 ;
           :phrase "a man a plan a canal suez" .
  :corinth :name "Corinth Canal"  ; :country "Greece"  ; :opened 1893 ;
           :phrase "no devil lived on" .
  :kiel    :name "Kiel Canal"     ; :country "Germany" ; :opened 1895 ;
           :phrase "never odd or even" .
  :erie    :name "Erie Canal"     ; :country "United States" ; :opened 1825 ;
           :phrase "erie canal" .
  :grand   :name "Grand Canal"    ; :country "China"   ; :opened 609 ;
           :phrase "was it a rat i saw" .
`
```

```observable-js
dataset = fn.parse(WATERWAYS_TTL)
```

## Registering Wikifunctions by ZID

Load the vendored engine, then register each ZID under the
`https://wikifunctions.org/fn#` namespace. The marshaling mirrors the
wikifn demo: only strings, booleans, and natural numbers cross the
boundary (a list or record has no obvious RDF term — refused, not
guessed at); the compiled F\* function answers first, and a ZID with
no compiled form of that arity falls back to the interpreter,
recorded in the cell's return value rather than hidden:

```observable-js
wikifn = {
  await fn.loadWikifunctions();
  const XSD = "http://www.w3.org/2001/XMLSchema#";
  const toArg = (t) => {
    if (t.type !== "literal") throw new Error("only literals cross into Wikifunctions, got " + t.type);
    if (t.datatype === XSD + "boolean") return t.value === "true";
    if (t.datatype && /#(integer|int|long|nonNegativeInteger|positiveInteger)$/.test(t.datatype)) {
      return Number(t.value);
    }
    return t.value;
  };
  const fromResult = (zid, r) => {
    if (!r.ok) throw new Error(zid + ": " + r.message);
    if (r.result.type === "Z6") return r.result.text;                       // -> xsd:string
    if (r.result.type === "Z40") return r.result.value === true;            // -> xsd:boolean
    if (r.result.type === "Z13518") {
      return { type: "literal", value: String(r.result.value), datatype: XSD + "integer" };
    }
    throw new Error(zid + " returned " + r.result.type + ", which has no RDF term");
  };
  const call = (zid, args) => {
    const payload = JSON.stringify(args.map(toArg));
    let r = JSON.parse(globalThis.wikifnCompiledCall(zid, payload));
    if (!r.ok && /has no compiled function/.test(r.message ?? "")) {
      r = JSON.parse(globalThis.wikifnEngineCall(zid, "100000", payload));
    }
    return fromResult(zid, r);
  };
  const ZIDS = ["Z10052", "Z10096", "Z11040", "Z10627"];
  for (const zid of ZIDS) {
    await fn.registerExtensionFunction("https://wikifunctions.org/fn#" + zid,
      (args) => call(zid, args));
  }
  // Which of these answers through the interpreter rather than a
  // compiled F* function? Probe with this page's one-string-argument
  // shape, so the answer is computed, not asserted.
  const interpreted = ZIDS.filter((zid) => {
    const r = JSON.parse(globalThis.wikifnCompiledCall(zid, JSON.stringify([""])));
    return !r.ok && /has no compiled function/.test(r.message ?? "");
  });
  return { registered: ZIDS, interpreted };
}
```

## Palindrome canals

Two Wikifunctions composed inside `BIND` — `Z10052` strips the
spaces, `Z10096` reads the result backwards:

```observable-js
wikifn;
const rows = await fn.query(dataset, `
  # For each waterway's phrase: Z10052 removes spaces, then Z10096
  # checks whether the result reads the same backwards.
  PREFIX :   <https://example.org/waterway#>
  PREFIX fn: <https://wikifunctions.org/fn#>
  SELECT ?name ?phrase ?palindrome WHERE {
    ?w :name ?name ; :phrase ?phrase .
    BIND(fn:Z10096(fn:Z10052(?phrase)) AS ?palindrome)
  }
  ORDER BY DESC(?palindrome) ?name
`);
return pretty(rows);
```

Six rows; four come back `true` — Mercer's, plus three classics that
smuggled themselves into the dataset (`no devil lived on`,
`never odd or even`, `was it a rat i saw`). The two controls fail:
`"a man a plan a canal suez"` is one word away from Mercer's and that
one word ruins it — no amount of pattern-matching on "a man, a plan"
saves it, the function actually reads the string backwards — and
`"erie canal"` was never trying.

## Filter to just those

Same test as a `FILTER`, so only the surviving canals come back at
all — four of the six:

```observable-js
wikifn;
const rows = await fn.query(dataset, `
  # Same space-stripping-then-palindrome-check, as a FILTER: only
  # waterways whose phrase survives it are returned.
  PREFIX :   <https://example.org/waterway#>
  PREFIX fn: <https://wikifunctions.org/fn#>
  SELECT ?name ?country ?phrase WHERE {
    ?w :name ?name ; :country ?country ; :phrase ?phrase .
    FILTER(fn:Z10096(fn:Z10052(?phrase)))
  }
  ORDER BY ?name
`);
return pretty(rows);
```

## Any ZID you like — and the honest fallback, live

Nothing above is special-cased; the catalogue is the allow-list.
`Z10627` is ROT13 (compiled). `Z11040` is string length — which has
**no compiled function of this arity** in the current corpus
snapshot, so it answers through the interpreter, and the `wikifn`
setup cell's `interpreted` list above says so in so many words:

```observable-js
wikifn;
const rows = await fn.query(dataset, `
  # Three Wikifunctions in one query: Z11040 counts the letters of the
  # space-stripped phrase, Z10627 ROT13-encodes the waterway's name,
  # and Z10096 checks the palindrome as before.
  PREFIX :   <https://example.org/waterway#>
  PREFIX fn: <https://wikifunctions.org/fn#>
  SELECT ?name ?letters ?rot13 ?palindrome WHERE {
    ?w :name ?name ; :phrase ?phrase .
    BIND(fn:Z11040(fn:Z10052(?phrase)) AS ?letters)
    BIND(fn:Z10627(?name)              AS ?rot13)
    BIND(fn:Z10096(fn:Z10052(?phrase)) AS ?palindrome)
  }
  ORDER BY DESC(?letters)
`);
return pretty(rows);
```

Mercer's phrase wins on letters too, and every canal's name arrives
ROT13'd (`Cnanzn Pnany`) — an ordinary corpus function, reached by
ZID, in the same query as the palindrome test and SPARQL's own
`ORDER BY`.

## Two proofs, one seam — what would it take to make it one proof?

Today the two artifacts compose **post-extraction**: two JavaScript
bundles exchanging JSON. Each side keeps its own theorems — this
engine's dispatch and algebra proofs, wikifn-fstar's per-composition
checks and tester parity — but the *seam* between them is marshaling
code, verified by neither. Three escalating options, tracked in
[#464](https://github.com/danbri/factoidal/issues/464):

1. **Provenance for the seam we have**: pin the vendored bundle by
   content hash (done — see the asset README) so the artifact that
   was measured is provably the artifact that runs. That is
   supply-chain integrity, not proof composition — no cryptography
   makes two separately-extracted bundles share theorems.
2. **Join before extraction**: import wikifn-fstar's F\* modules into
   this build, verify both under one F\* run, and register the
   functions natively — the call becomes an ordinary verified
   function application, and cross-cutting lemmas become statable
   ("every corpus function reachable from a SPARQL literal terminates
   and yields a term-convertible `Z6`/`Z40`/`Z13518`").
3. **One artifact**: extract the joined development together, and the
   JS/JSON seam disappears from the trust surface entirely.

## Related

[Post 34](./34-extension-functions.md) — the extension-function
mechanism itself, including the async trampoline these cells ride on.
[wikifn-fstar's own demo](https://danbri.github.io/wikifn-fstar/demo-sparql.html)
— the same functions driven from Comunica, plus its
[engine browser](https://danbri.github.io/wikifn-fstar/demo-engine.html) and
[tester report](https://danbri.github.io/wikifn-fstar/tester-report.html).

The live cells above are pinned in
[`tests/hub/post35_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post35_test.mjs),
running the exact same cell source against the `npm/factoidal` typed
API with the vendored engine loaded from disk.
