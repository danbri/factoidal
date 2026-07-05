# Vendored W3C RIF Test Cases — Core dialect subset

This directory mirrors the **official W3C RIF Core dialect test suite
distribution** (not a hand-curated subset like
`third_party/testing/rif/tc/` — this is the complete, versioned
"Approved" Core-dialect zip as published by the working group), for
`bin/rif-runner/rif_runner.ml`'s corpus walker to drive beyond the
original 4 hardcoded SPARQL-manifest cases.

## Source

- Zip archive: <https://www.w3.org/2005/rules/test/repository/zips/Core_v1.22.zip>
- Manifest (all Core-applicable tests, machine-readable):
  <https://www.w3.org/2005/rules/test/repository/CoreTests.xml>
  (vendored here as `CoreTests.xml`)
- Individual test case repository (browsable, same content):
  <https://www.w3.org/2005/rules/test/repository/tc/>
- Format reference: [RIF Test Cases (Second Edition)](https://www.w3.org/TR/rif-test/),
  schema `rif-testcase.xsd`.
- Date of mirror: 2026-07-05.

Sibling BLD (`BLD_v1.22.zip`) and PRD (`PRD_v1.22.zip`) dialect zips
were fetched **for inventory only** (counted, not vendored) — see
"Inventory" below and `docs/claude-rules/scope.md`'s RIF paragraph for
why RIF-BLD/RIF-PRD stay out of scope.

## License

The RIF Test Cases are W3C documents distributed under the
[W3C Document License](https://www.w3.org/Consortium/Legal/2002/copyright-documents-20021231).
No modification has been made to the vendored `.rif`/`.rdf`/`.ttl`/
`.xml` test files themselves.

## Layout

```
Core_v1.22/
  VERSION.txt
  Approved/
    PositiveEntailmentTest/<TestName>/<TestName>-premise.rif
                                       <TestName>-conclusion.rif
                                       <TestName>-import*.{rdf,ttl}  (if any)
                                       <TestName>.xml                (W3C test metadata)
    NegativeEntailmentTest/<TestName>/<TestName>-premise.rif
                                       <TestName>-nonconclusion.rif
                                       ...
    PositiveSyntaxTest/<TestName>/...
    NegativeSyntaxTest/<TestName>/...
    ImportRejectionTest/<TestName>/...
CoreTests.xml   (manifest: all 46 tests below, with dialect/profile/purpose metadata)
```

A `PositiveEntailmentTest` asserts that saturating `-premise.rif`
under RIF Core forward-chaining entails every fact named in
`-conclusion.rif`. A `NegativeEntailmentTest` asserts the same
saturation does **not** entail every fact in `-nonconclusion.rif`.
`PositiveSyntaxTest`/`NegativeSyntaxTest` check RIF Core's dialect-
specific "safeness" grammar restriction (every body variable must be
"safe" — bound by a non-negated atom); `ImportRejectionTest` checks
that certain `<Import>` combinations (vocabulary-separation
violations, invalid DL formulas) must be rejected. See
`bin/rif-runner/README.md` for which of these categories the runner
actually evaluates vs. honestly skips, and why.

## Inventory (2026-07-05, counted from the three official dialect zips)

| Dialect | Total tests | PositiveEntailmentTest | NegativeEntailmentTest | PositiveSyntaxTest | NegativeSyntaxTest | ImportRejectionTest |
|---|---|---|---|---|---|---|
| **Core** (vendored here) | 46 | 29 | 5 | 3 | 3 | 6 |
| BLD (not vendored)       | 32 | 26 | 5 | 0 | 1 | 0 |
| PRD (not vendored)       | 10 | 5  | 2 | 0 | 3 | 0 |

- **BLD-only** (test names in `BLD_v1.22.zip` not already covered by
  Core): 31 — mostly `Equality_in_*`, `Factorial_Functional`/
  `_Relational`, `List*Equality*`, `Named_Arguments`,
  `Classification*`, `Chaining_strategy_*`. Out of scope (RIF-BLD:
  built-ins beyond what Core already needs, equality atoms, full
  Uniterm argument forms, list terms as first-class BLD constructs).
- **PRD-only** (not in Core or BLD): 6 — `Assert`, `AssertRetract`,
  `AssertRetract2`, `Modify`, `Modify_loop`, `Retract`. Out of scope
  (RIF-PRD: production rules, actions, retraction — this project
  targets logic/query semantics, not a production-rule action engine;
  see `docs/claude-rules/scope.md`).

Total distinct test names across all three dialect zips: 83 (union;
a test applicable to multiple dialects, e.g. `Frames`, appears in
more than one zip and is counted once here). The browsable repository
index at `tc/` lists 91 directories; the 9 names present there but
absent from all three "Approved" dialect manifests (e.g.
`Conflict_resolution`, `Ordered_Relations`, `Quantify_free_variables`,
several `YoungParentDiscount`/`UCR_4.1.*`/`Modify_noloop` variants)
are Proposed/Withdrawn-status or otherwise not part of any dialect's
Approved suite as of this mirror and are not vendored or counted
above.

## Why a vendor copy and not a git submodule

Per the same reasoning as `third_party/testing/rif/tc/`'s
`MANIFEST.md`: the W3C RIF Test Cases are not maintained in a public
git repository; the canonical distribution is this static HTTP zip.
A vendored copy is the only way to pin a stable, offline-runnable
corpus.
