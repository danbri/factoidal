# Caller-registered SPARQL extension functions in the Lean engine

Date: 2026-09-04.
Issue family: <https://github.com/danbri/factoidal/issues/463> (the F\*
side, already landed), <https://github.com/danbri/factoidal/issues/466>
(the Lean 4 port), <https://github.com/danbri/factoidal/issues/641> (the
`factoidal` command and its store host).

## The gap this closes

SPARQL 1.1 §17.6 ("Extensible Value Testing") lets a query name a
function by IRI. The Lean evaluator has that extension point as an
ordinary field:

    EvalEnv.ext : String -> List EvalResult -> Option EvalResult

Until this change every Lean query path installed one fixed table,
`L4Factoidal.Geo.extFns` (`Wasm/Ops/Query.lean`), which answers `geof:`
IRIs and `none` for everything else. A caller could not add a function.
The F\* engine could: `registerExtensionFunction` in
`npm/factoidal/index.js` and `npm/factoidal/browser.js` serves the F\*
in-memory `query()` only.

## 1. Registration and how the engine reaches the function

Three parts, in the order a call passes through them.

**The host table (JavaScript).** `npm/factoidal/bin/ext.mjs` keeps a
`Map` from IRI to the caller's function, plus a per-query memo table. It
installs one bridge function, `globalThis.__factoidalExtCall`, which
takes `(iri, argsJson)` and answers a JSON string.

**The boundary (C).** `formal/lean4/ffi/l4_ext.c` provides the symbol
`l4_ext_call`. Under Emscripten it is an `EM_JS` body that calls
`globalThis.__factoidalExtCall`. On a native build it answers "no host".
This is the same shape the tree already uses for HACL\* crypto
(`L4Factoidal/Crypto/Ed25519.lean`, `@[extern "l4_hacl_ed25519_sign"]`)
and for range reads (`Harness/PosixRangeIO.lean`,
`@[extern "l4_block_pread"]`): a declared `opaque`, realised by C, with
no `unsafe`, no `@[implemented_by]` and no user `axiom`.

**The Lean side.** `Wasm/ExtHost.lean` declares

    @[extern "l4_ext_call"]
    opaque extCallHost (iri : @& String) (argsJson : @& String) : String

and `Wasm/Ops/ExtFns.lean` builds the extension table:

    def extFnsWith (registered : List String)
        (iri : String) (args : List EvalResult) : Option EvalResult

It tries `Geo.extFns` first; only if that answers `none` AND `iri` is in
`registered` does it cross to the host. `registered` is a snapshot of
`Wasm/Ops/ExtFns.lean`'s `IO.Ref`, taken once per query by the IO
dispatch entry and passed as a plain argument into
`queryParsedDatasetWith`. The evaluator itself stays a total function of
its explicit inputs; the mutable part lives in `Wasm/*`, which is the
one layer permitted to hold it (`Wasm/Ops/Handles.lean`'s rule).

The wire ops are `extRegister(iri)`, `extUnregister(iri)`,
`extClear()` and `extList()`, served by `callIO` only. The pure
`L4Wasm.call` entry cannot reach the ref, so it keeps answering with the
`geof:` table alone.

Every query path takes the snapshot: `queryDataset` and `storeQuery`
through their `callIO`/`callBlobIO` arms, and `datasetQuery` and
`storeHandleQuery` inside their own IO bodies.

## 2. Argument and result encoding

The bridge sees SRJ binding-value objects — the encoding
`SPARQL/ResultsJson.lean` already defines, and the encoding the F\*
bridge uses, so a function written for one engine works on the other.

- Arguments: `EvalResult.toTerm?` on each argument, then `jsonOfTerm`,
  then a JSON array. An argument with no term form (a `.error`) makes
  the whole call a §17.6 error without crossing the boundary.
- Result: the host answers `""` for "no value" (the §17.6 error), or one
  SRJ binding-value object, decoded by `parseBindingValueJson`. A string
  that is not either of those is the §17.6 error.

## 3. Sync path

A synchronous JavaScript function answers inside the bridge call. The
engine sees an ordinary value and the query completes in one
evaluation. This is the path that landed.

## 4. Async path

An asynchronous function cannot answer inside the bridge call: the Lean
evaluator is synchronous and is inside WebAssembly, so it cannot suspend.

The F\* engine solved this and this design copies it rather than
inventing a second answer (`npm/factoidal/browser.js`,
`withExtensionRounds`): the bridge starts the promise, records it in a
pending list, and answers "no value" for this round. The host awaits
every pending promise, writes the answers into the memo table, and runs
the WHOLE query again. It repeats until a round adds no new pending
call, with a hard cap (`EXT_MAX_ROUNDS`, 25 in the F\* host) after which
the host raises "async resolution did not converge".

The cost is that a query with async functions is evaluated more than
once. The gain is that neither engine needs a suspendable evaluator, and
the two engines answer the same thing for the same registered function.

## 5. Determinism within one query

Two things make the same call answer the same way for the whole
evaluation.

1. **The memo table.** The bridge keys on `iri + " " + argsJson` and
   returns the memoised answer without calling the user function again.
   The table is created fresh for each top-level query, so a function
   whose answer changes over time changes it BETWEEN queries, never
   inside one.
2. **The re-evaluation rounds share that table.** Round *n+1* reuses
   every answer round *n* recorded, so the trampoline cannot make one
   call answer twice.

Without the memo table the results would not be well defined: SPARQL
1.1 §17.6 requires an extension function to behave as a function of its
arguments, and the physical-plan runners are free to evaluate an
expression a different number of times than the reference evaluator.

## 6. §17.6 error semantics

The evaluator reaches `env.ext` only after every built-in family has
been tried (`SPARQL/Expr.lean` line 2039: the `iri` arms for the
`fn:`/`xsd:`/SPARQL built-ins are all above it). So:

- **A built-in name is never overridden by a registration.** This holds
  by construction, not by a check.
- **`geof:` keeps working exactly as now.** `extFnsWith` consults
  `Geo.extFns` before the host, so a registration on a `geof:` IRI that
  the built-in table answers is not reached.
- **An unregistered IRI is the §17.6 error** (`.error`). In FILTER
  position §17.2.2's effective boolean value of an error is an error and
  §18.5's filter keeps only solutions whose expression is `true`, so the
  row is dropped. In SELECT-expression or BIND position §18.5's
  extend(μ, var, expr) leaves the variable UNBOUND when the expression
  errors, and the row survives.
- **A registered function that throws, returns `undefined`/`null`, or
  returns a value the SRJ decoder rejects, is the same §17.6 error**,
  with the same two consequences.

## 7. Registration scope

The Lean registry is per **module instance**: one loaded wasm module, or
one native process. It is not per handle and not per query.

For a long-lived server (the owner's context is an MCP server driving
LLM tool loops) that is not enough on its own, because one caller's
registration would be visible to another caller's query. The host layer
therefore offers `withExtensionFunctions(map, body)`, which registers,
runs, and clears in a `finally`. A server that serves more than one
trust domain must either use that wrapper or load one engine instance
per domain. `extClear()` exists so a caller can always return the engine
to the `geof:`-only table.

## 8. Cost

Crossing to JavaScript is measured, not assumed — a function called once
per row is on the hot path. The measurement and its method are recorded
in the landing report and in
`docs/claude-rules/performance.md`.
