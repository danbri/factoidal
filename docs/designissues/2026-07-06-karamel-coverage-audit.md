# 2026-07-06 — KaRaMeL coverage audit

Last refreshed: 2026-07-06 (measured on worktree at commit `9c3d160`,
F\* 2025.12.15, z3 4.13.3, krml from FStarLang/karamel git master per
[`2026-05-10-krml-install-notes.md`](2026-05-10-krml-install-notes.md),
4-core / 15 GB shared sandbox).

## Why

The wasm story most likely runs through KaRaMeL C for the data plane
(`clang -target wasm32`, per
[`2026-05-07-c-build-and-roaring-plan.md`](2026-05-07-c-build-and-roaring-plan.md)
§2.4): smaller binaries than the js_of_ocaml route and a path to
linkable `librdfcore.a`. Until now "low F\* KaRaMeL coverage" was a
vibe, not a number. This audit replaces it with a measured number, a
per-module blocker table, and a prioritized migration queue.

## Coverage numbers

Of the **134** `formal/fstar/*.fst` modules:

- **107 pass** (79.9%) — the module and its full dependency closure
  extract through `fstar.exe --codegen krml` and lower through `krml`
  to C with the pilot's warning policy (see "What PASS means" below).
  5 of the 107 are all-`assume val` modules that legitimately lower to
  a header only (`JSONLD.Loader`, `RDF.CottasInMem`,
  `RDF.CottasStore.LazyDictRegistry`, `RDF.CottasStore.OnDiskRuntime`,
  `RDF.Store.HDTTermCacheRegistry`).
- **8 blocked in their own right** (BLOCKED_SELF — every in-set
  dependency lowers clean; this module's own closure is the problem).
- **1 timeout** (`RDF.Vocabulary.Axioms` — krml's Inlining pass does
  not return within a 300 s solo re-probe; monomorphization completes
  in 12 ms).
- **18 blocked transitively** (BLOCKED_TRANSITIVE — the module fails,
  and at least one module in its dependency closure is itself blocked;
  fixing the dependency is the cheap unlock candidate, then retest).

So: **107 of 134 krml-clean today; up to 18 more unlock by fixing the
9 root blockers** (3 of the 18 carry their own distinct failure
signature and may need follow-up of their own — flagged below).

Every module was tested for real — no inferred statuses. An earlier
draft of the audit inferred "transitively blocked" from the DAG
without testing, and that produced measured false positives: 16
modules inferred-blocked in the first sweep **pass** when actually
tested, because a consumer's bundle only monomorphizes the
*reachable* part of a blocked dependency. 12 modules pass despite a
direct `SPARQL11.Algebra` dependency (`SPARQL.Explain`, `RML.Eval`,
`ShEx.Validation`, `XSD.Datatypes`, `RDF.Pretty`,
`RIF.Core.Eval`, `RIF.Core.Translation`, `CSVW.Conversion`,
`CSVW.URITemplate`, and the three `RDF.Store.Capabilities` modules) —
they use the algebra datatypes, never reach the evaluator, and krml
drops the rest. `RDF.Store.Combine` goes further still: it passes with
`SPARQL11.Store` (itself a failing module) as a direct dependency.
That is direct measured evidence for the stratification bet
(§ "Mapping onto the stratification roadmap").

## How to reproduce

```
eval $(opam env --switch=fstar)
tools/karamel-coverage-audit.sh [--scratch DIR] [--jobs N]
```

Per module (2 bounded stages, 120 s timeout each):

1. `fstar.exe --z3version 4.13.3 --codegen krml --odir <scratch>
   --cache_checked_modules --extract 'krml:*' <Mod>.fst` — F\* extracts
   the module and its whole dependency closure into one `out.krml`.
2. `krml -skip-compilation -skip-makefiles -warn-error -9-11-15+2
   -bundle '<Mod>=*[rename=Audit]' out.krml` — krml lowers with the
   module as bundle root, same warning policy as the pilot
   (`tools/karamel-c-build.sh`).

All scratch output lands outside `formal/fstar/`; the run reuses the
existing `.checked` cache read-only and never touches the
`build-ocaml.sh` extraction state. Full-tree run: ~14 min wall on 4
cores with a warm `.checked` cache (2196 s F\*-stage CPU + 212 s
krml-stage CPU across 4 workers).

Raw artifacts committed alongside this doc:

- [`2026-07-06-karamel-coverage-audit.tsv`](2026-07-06-karamel-coverage-audit.tsv)
  — one row per module: status, blocker category, first error line,
  direct in-set deps, per-stage timings.
- [`2026-07-06-karamel-coverage-audit-raw-failures.log`](2026-07-06-karamel-coverage-audit-raw-failures.log)
  — the captured F\*/krml output for all 27 non-PASS modules (long
  mid-sections trimmed; the full 1.3 MB log is reproducible with the
  script above).

## What PASS means (and does not mean)

PASS = the full F\* → `.krml` → `.c`/`.h` chain completes with the
pilot's warning policy: warnings 9 (static initializers), 11
(closures → function pointers), and 15 (GC types / mathematical
integers) downgraded, warning 2 (extern without implementation)
non-fatal because `assume val` externs get C-side stubs at link time
(the Group A demo links exactly such stubs, 10 pass, 0 fail, out of
10).

PASS does **not** mean Low\*-quality C. Most passing modules emit C
that uses krmllib's GC'd list/string representations and leaks memory
without a collector — "logically correct but not standalone", as the
`extract-c` Makefile target has documented since the first pilot. The
audit measures the *pipeline gate* (can krml swallow the module at
all); making a hot path allocation-clean (machine integers, buffers,
no lists) is a second, per-module effort on top. The migration queue
prices both.

Known caveat on the dependency labels: `fstar.exe --dep full` reports
interface-backed dependencies as `.fsti.checked` edges, which the
audit's parser (like `build-ocaml.sh`'s) drops. As of this run all 8
`.fsti`-backed modules pass, so no BLOCKED_SELF/TRANSITIVE label is
affected by the gap.

## Root blockers — every failure classified

9 root blockers (8 BLOCKED_SELF + 1 TIMEOUT), in 4 distinct failure
classes:

### Class 1 — krml monomorphization stack overflow (3 modules, blocks 16 more)

`Fatal error: exception Stack overflow` during krml's
Monomorphization pass.

| Module | Notes |
|---|---|
| `SPARQL11.Algebra` (5,845 lines) | The known blocker from the pilot's Group B, now reproduced module-precisely: the algebra + evaluator monolith's AST does not survive krml monomorphization (OCaml stack overflow at default ulimit; the pilot additionally measured > 20 min at 4.3 GB RSS with `ulimit -s unlimited`). |
| `Tableau` | Own overflow, independent of Algebra (its deps `OWL.Vocabulary`, `RDF.Graph.Executable` both pass). |
| `Parser.XPath` | Own overflow, same class. |

Transitively blocked by `SPARQL11.Algebra` (16): `OWL.QueryEval`,
`OWL.QueryRewrite`, `RDF.Store.Columnar.DeltaMerge`,
`RIF.Core.Builtins`, `RIF.Core.Tests`, `SHACL.Validation`,
`SPARQL.Diagnostics`, `SPARQL.HTTP.RunQuery`, `SPARQL.Plan.Explain`,
`SPARQL.Plan.Streamable`, `SPARQL.Query.Analysis`,
`SPARQL.Update.Analysis`, `SPARQL.Update.Sandbox`, `SPARQL11.Parser`,
`SPARQL11.Store`, `VC.Credential`. By `Parser.XPath` (1):
`XPath.Eval`.

Flag: `VC.Credential` and `RIF.Core.Tests` fail with the Class-2
`Failure("nth")` signature rather than their dependency's overflow —
after an Algebra fix they need their own retest and possibly their own
fix.

### Class 2 — krml internal error `Failure("nth")` in Simplify.remove_unused_parameters (4 modules, blocks 1 more)

`Fatal error: exception Failure("nth")`. Backtrace (captured with
`OCAMLRUNPARAM=b` on the `Parser.NQuads` reproduction, in the
raw-failures log): raised from `Krml__Simplify.unused.unused_i`
(`lib/Simplify.ml:254`) inside `remove_unused_parameters` — an
arity-table lookup out of range at a call site. Each affected run also
prints `Warning 16: Cannot enforce arity at call-site … is this a
partial application?` beforehand, so the trigger is
partial-application call sites feeding an inconsistent arity table.
This is an upstream krml defect worth a minimal reproduction + issue;
the local workaround is eta-expanding the offending partial
applications.

| Module | Blocks |
|---|---|
| `Parser.NQuads` | `Parser.Ballyhoo` retested clean (it passes — reachability again), so nothing hard-blocked, but N-Quads itself is a data-plane parser. |
| `JSONLD.Context` | `JSONLD.Expand` (same signature). |
| `CSVW.Metadata` | — (`CSVW.Conversion` passes on its own). |
| `ShEx.Schema` | — (`ShEx.Validation` passes on its own). |

### Class 3 — F\* `--codegen krml` Error 189, stale lemma signature (1 module)

`RDF.CottasStore.PageCache.Bounds` fails in the *F\** stage:

```
* Error 189 at RDF.CottasStore.PageCache.Bounds.fst(215,35-215,36):
  - Expected expression of type RDF.CottasStore.ColumnSeq.cottas_column
    got expression v of type Prims.list (FStar.Pervasives.Native.option Prims.string)
```

The `pcache_put_capacity_bound` lemma `val` still says
`v:list (option string)` where `RDF.CottasStore.PageCache`'s
`pcache_put` now takes a `cottas_column`. OCaml extraction never
notices (lemmas erase); the krml codegen path re-checks the `val`.
Module-local one-line fix.

### Class 4 — krml Inlining pass non-termination (1 module)

`RDF.Vocabulary.Axioms` (258 lines of literal axiomatic-triple
constants): the krml Monomorphization pass completes in 12 ms, then
the following Inlining pass produces no further output. Hit the 120 s
audit cap in both full runs; a solo re-probe with a 300 s cap also
timed out (exit 124). Not investigated further. Nothing is hard-blocked
by it — `RDFS.Closure`, its only in-set dependent, passes (bundle
reachability again).

## Blocker classes by module count

| Class | Root modules | + transitively failing |
|---|---:|---:|
| krml monomorphization stack overflow | 3 | 17 |
| krml `Failure("nth")` (Simplify arity bug) | 4 | 1 |
| F\* codegen-krml Error 189 (stale lemma type) | 1 | 0 |
| krml Inlining non-termination (timeout) | 1 | 0 |
| **Total non-PASS** | **9** | **18** |

(The 18 transitive column counts each module once, by the signature it
actually shows; `VC.Credential` and `RIF.Core.Tests` show "nth" but
sit in Algebra's closure and are counted under overflow's transitive
column where their blocked dep lives — see the TSV for exact
per-module categories.)

## Migration queue (perf value on hot paths × migration cost)

Hot paths named for the wasm/C data plane: COTTAS page decode, the
parsers' byte layer, hashing, rank/select, the delta log. Status:

- **COTTAS page decode — already green.** `RDF.CottasStore`,
  `.PageCache`, `.ColumnSeq`, `.OnDiskIndex`, `.PresenceBitmap`,
  `.CompoundPresenceBitmap`, all `.\*Writer` modules, and both lazy
  dict layers pass. Only the proof-side `PageCache.Bounds` fails
  (Class 3, one-line fix).
- **Parser byte layer — green except N-Quads.** `Parser.FastString`,
  `RDF.Bytes`, `Parser.TurtleScanner`, `Parser.Turtle`,
  `Parser.NTriples`, `Parser.TriG`, `Parser.XML`, `Parser.RDFXML`
  pass. `Parser.NQuads` is Class 2.
- **Hashing — not an .fst blocker.** The hash/signature `assume val`s
  are slated for HACL\* realisation (`skills/crypto-policy`), and
  HACL\* ships as Low\*-verified C already; the C build links it
  directly.
- **Rank/select — out of this audit's scope.** Lives in
  `formal/roaring/src`, not `formal/fstar/*.fst`; the Roaring plan
  already mandates KaRaMeL-compatible style. Measure it with the same
  script when it lands in the main tree.
- **Delta log — green.** `RDF.Store.Columnar.DeltaLog` passes (and is
  the pilot's Group C with a 12/12 linked demo). Its merge-on-read
  sibling `RDF.Store.Columnar.DeltaMerge` is blocked only by
  `SPARQL11.Algebra`.

Queue, ranked:

| # | Item | Value | Cost | Unlocks |
|---|---|---|---|---|
| 1 | Fix `PageCache.Bounds` lemma signature (Class 3) | Keeps the COTTAS proof surface inside the C-bundle path | One line + verify | 1 module |
| 2 | `Parser.NQuads` eta-expansion workaround + minimal krml repro filed upstream (Class 2) | N-Quads is a bulk-load data-plane parser; the repro also serves JSONLD/CSVW/ShEx | Small: find the partial-application site(s) flagged by Warning 16, eta-expand | 1 module now, 4+1 when upstream lands |
| 3 | `SPARQL11.Algebra` stratification — split algebra datatypes from evaluator (already planned, see next section) | Unblocks `RDF.Store.Columnar.DeltaMerge` (data plane), `SPARQL11.Parser`, `SHACL.Validation`, the Analysis pair, 16 total | Large but already roadmapped; the audit shows datatype-only consumers pass *today*, so the split's payoff is measured, not hoped | up to 16 modules |
| 4 | Low\*-ify the hot decode path (machine ints/buffers for `PageCache`/`ColumnSeq`/`PresenceBitmap` inner loops) | This is what actually makes the C fast — PASS-grade C still uses GC'd lists | Per-module, medium; follow the DeltaLog precedent (u32/u64-scale nat fixes in the pilot) | perf, not coverage |
| 5 | `RDF.Vocabulary.Axioms` inlining non-termination: report/riddle out (Class 4) | Nothing blocked; constant tables have no data-plane value | Investigation only | tidiness |
| 6 | `Tableau`, `Parser.XPath` own overflows | Reasoning/XPath are not data-plane | Same treatment as Algebra (split or upstream), defer | 1 module each (+`XPath.Eval`) |

## Mapping onto the stratification roadmap

The planned stratification
([`skills/fstar-module-style/SKILL.md`](../../skills/fstar-module-style/SKILL.md)
§"Planned stratification", from
[`2026-05-08-foundational-fstar-tier.md`](2026-05-08-foundational-fstar-tier.md))
names two splits. The audit prices both:

- **`RDF.Graph.Executable` split (`RDF.Term`/`RDF.Triple`/`RDF.Graph`
  + closures): already paid off for C.** All six split-out modules and
  the umbrella pass. The foundational core is krml-clean end to end.
- **`SPARQL11.Algebra` split (datatypes / evaluation / function
  library / numerics): this audit's single highest-leverage item.**
  The monolith is the last big BLOCKED_SELF, 16 of the 18 transitive
  failures sit in its closure, and the 12 passing modules that import
  it for datatypes only (e.g. `RDF.Pretty`, `SPARQL.Explain`,
  `XSD.Datatypes`, `RML.Eval`, `ShEx.Validation`) demonstrate that a
  datatypes-only module clears krml immediately. After a split,
  consumers of `SPARQL11.Algebra.Types` join the PASS column without
  further work; only the evaluator module itself remains a krml
  problem, and it shrinks to whatever the evaluator alone weighs.

A `docs/designissues/2026-07-06-fstar-directory-structure.md` split
list was referenced as a possible companion; that file is not present
at this worktree's HEAD (`9c3d160`), so the mapping above uses the
skill doc and the 2026-05-08 tier audit as the roadmap sources.

Score-floor note for future refreshes: re-run
`tools/karamel-coverage-audit.sh` after each stratification slice and
update the numbers here. The expected trajectory from item 3 alone is
107 → ~123 of 134.

## Appendix — full per-module table

Generated from the committed TSV (status, blocker category, first
error). PASS rows have empty blocker columns; "header-only" marks
all-`assume val` modules whose C output is legitimately a header with
extern declarations.

| Module | Status | Blocker category | First error line |
|---|---|---|---|
| `CSVW.Conversion` | PASS |  |  |
| `CSVW.Metadata` | BLOCKED_SELF | krml fatal: Failure("nth") | Fatal error: exception Failure("nth") |
| `CSVW.URITemplate` | PASS |  |  |
| `HDT.Container` | PASS |  |  |
| `HDT.Dictionary` | PASS |  |  |
| `HDT.Triples` | PASS |  |  |
| `JSONLD.Context` | BLOCKED_SELF | krml fatal: Failure("nth") | Fatal error: exception Failure("nth") |
| `JSONLD.Expand` | BLOCKED_TRANSITIVE | krml fatal: Failure("nth") [failing deps in closure: JSONLD.Context] | Fatal error: exception Failure("nth") |
| `JSONLD.Loader` | PASS | header-only (all-assume-val module, no C body emitted) |  |
| `OWL.Closure` | PASS |  |  |
| `OWL.DirectMapping.Filter` | PASS |  |  |
| `OWL.QueryEval` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: OWL.QueryRewrite, SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `OWL.QueryRewrite` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `OWL.Tests.Manifest` | PASS |  |  |
| `OWL.Vocabulary` | PASS |  |  |
| `Parquet.Footer` | PASS |  |  |
| `Parser.Ballyhoo` | PASS |  |  |
| `Parser.BallyhooBloom` | PASS |  |  |
| `Parser.BallyhooCOTTAS` | PASS |  |  |
| `Parser.BallyhooHDT` | PASS |  |  |
| `Parser.BallyhooHDTQ` | PASS |  |  |
| `Parser.CSVResults` | PASS |  |  |
| `Parser.Combinators` | PASS |  |  |
| `Parser.FastString` | PASS |  |  |
| `Parser.IRI` | PASS |  |  |
| `Parser.JSON` | PASS |  |  |
| `Parser.JSONLD` | PASS |  |  |
| `Parser.JSONResults` | PASS |  |  |
| `Parser.NQuads` | BLOCKED_SELF | krml fatal: Failure("nth") | Fatal error: exception Failure("nth") |
| `Parser.NTriples` | PASS |  |  |
| `Parser.OWLFunctional` | PASS |  |  |
| `Parser.RDFXML` | PASS |  |  |
| `Parser.RIFXML` | PASS |  |  |
| `Parser.SRX` | PASS |  |  |
| `Parser.TriG` | PASS |  |  |
| `Parser.Turtle` | PASS |  |  |
| `Parser.TurtleScanner` | PASS |  |  |
| `Parser.XML` | PASS |  |  |
| `Parser.XPath` | BLOCKED_SELF | monomorphization stack overflow | Fatal error: exception Stack overflow |
| `RDF.Bytes` | PASS |  |  |
| `RDF.Canonical` | PASS |  |  |
| `RDF.Canonical.Manifest` | PASS |  |  |
| `RDF.CottasInMem` | PASS | header-only (all-assume-val module, no C body emitted) |  |
| `RDF.CottasStore` | PASS |  |  |
| `RDF.CottasStore.BaseWriter` | PASS |  |  |
| `RDF.CottasStore.ColumnSeq` | PASS |  |  |
| `RDF.CottasStore.CompoundPresenceBitmap` | PASS |  |  |
| `RDF.CottasStore.CompoundPresenceWriter` | PASS |  |  |
| `RDF.CottasStore.DictWriter` | PASS |  |  |
| `RDF.CottasStore.LazyDict` | PASS |  |  |
| `RDF.CottasStore.LazyDictRegistry` | PASS | header-only (all-assume-val module, no C body emitted) |  |
| `RDF.CottasStore.OffsetsWriter` | PASS |  |  |
| `RDF.CottasStore.OnDiskIndex` | PASS |  |  |
| `RDF.CottasStore.OnDiskRuntime` | PASS | header-only (all-assume-val module, no C body emitted) |  |
| `RDF.CottasStore.PageCache` | PASS |  |  |
| `RDF.CottasStore.PageCache.Bounds` | BLOCKED_SELF | F\* codegen-krml error 189 | \* Error 189 at RDF.CottasStore.PageCache.Bounds.fst(215,35-215,36): |
| `RDF.CottasStore.PresenceBitmap` | PASS |  |  |
| `RDF.CottasStore.PresenceWriter` | PASS |  |  |
| `RDF.Dataset.Graphs` | PASS |  |  |
| `RDF.Dataset.Merge` | PASS |  |  |
| `RDF.Format` | PASS |  |  |
| `RDF.Graph` | PASS |  |  |
| `RDF.Graph.Executable` | PASS |  |  |
| `RDF.IRI` | PASS |  |  |
| `RDF.Indexed` | PASS |  |  |
| `RDF.List.Helpers` | PASS |  |  |
| `RDF.NQuads.Serialize` | PASS |  |  |
| `RDF.Pretty` | PASS |  |  |
| `RDF.Store.Capabilities` | PASS |  |  |
| `RDF.Store.Capabilities.Cottas` | PASS |  |  |
| `RDF.Store.Capabilities.Delta` | PASS |  |  |
| `RDF.Store.Columnar.DeltaLog` | PASS |  |  |
| `RDF.Store.Columnar.DeltaMerge` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `RDF.Store.Columnar.OffsetIndex` | PASS |  |  |
| `RDF.Store.Combine` | PASS |  |  |
| `RDF.Store.HDTTermCacheRegistry` | PASS | header-only (all-assume-val module, no C body emitted) |  |
| `RDF.Store.LazyTermCache` | PASS |  |  |
| `RDF.Store.Loader` | PASS |  |  |
| `RDF.Term` | PASS |  |  |
| `RDF.Triple` | PASS |  |  |
| `RDF.Turtle.Serialize` | PASS |  |  |
| `RDF.Vocabulary` | PASS |  |  |
| `RDF.Vocabulary.Axioms` | TIMEOUT | timeout (120s cap, krml lowering) | (timed out) |
| `RDFS.Closure` | PASS |  |  |
| `RIF.Core.Builtins` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `RIF.Core.Conformance` | PASS |  |  |
| `RIF.Core.Eval` | PASS |  |  |
| `RIF.Core.Syntax` | PASS |  |  |
| `RIF.Core.Tests` | BLOCKED_TRANSITIVE | krml fatal: Failure("nth") [failing deps in closure: RIF.Core.Builtins, SPARQL11.Algebra] | Fatal error: exception Failure("nth") |
| `RIF.Core.Translation` | PASS |  |  |
| `RML.Eval` | PASS |  |  |
| `RML.Mapping` | PASS |  |  |
| `RML.Sources` | PASS |  |  |
| `SHACL.Validation` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra, SPARQL11.Parser] | Fatal error: exception Stack overflow |
| `SPARQL.Diagnostics` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: RDF.Store.Columnar.DeltaMerge, SPARQL11.Algebra, SPARQL11.Store] | Fatal error: exception Stack overflow |
| `SPARQL.Eval.Limits` | PASS |  |  |
| `SPARQL.Eval.TimeBudget` | PASS |  |  |
| `SPARQL.Explain` | PASS |  |  |
| `SPARQL.GraphStore` | PASS |  |  |
| `SPARQL.HTTP` | PASS |  |  |
| `SPARQL.HTTP.Admin` | PASS |  |  |
| `SPARQL.HTTP.BackendInfo` | PASS |  |  |
| `SPARQL.HTTP.Client` | PASS |  |  |
| `SPARQL.HTTP.QueriesIndex` | PASS |  |  |
| `SPARQL.HTTP.Response` | PASS |  |  |
| `SPARQL.HTTP.Routes` | PASS |  |  |
| `SPARQL.HTTP.RunQuery` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `SPARQL.HTTP.StaticFiles` | PASS |  |  |
| `SPARQL.HTTP.Timing` | PASS |  |  |
| `SPARQL.JSON.Escape` | PASS |  |  |
| `SPARQL.Plan.AccessPath` | PASS |  |  |
| `SPARQL.Plan.Estimate` | PASS |  |  |
| `SPARQL.Plan.Explain` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `SPARQL.Plan.Loader` | PASS |  |  |
| `SPARQL.Plan.Pruning` | PASS |  |  |
| `SPARQL.Plan.Streamable` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `SPARQL.Protocol` | PASS |  |  |
| `SPARQL.Query.Analysis` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `SPARQL.ServiceDescription` | PASS |  |  |
| `SPARQL.Update.Analysis` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `SPARQL.Update.Sandbox` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `SPARQL11.Algebra` | BLOCKED_SELF | monomorphization stack overflow | Fatal error: exception Stack overflow |
| `SPARQL11.IRI.Resolve` | PASS |  |  |
| `SPARQL11.Parser` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `SPARQL11.Store` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: RDF.Store.Columnar.DeltaMerge, SPARQL11.Algebra] | Fatal error: exception Stack overflow |
| `ShEx.Schema` | BLOCKED_SELF | krml fatal: Failure("nth") | Fatal error: exception Failure("nth") |
| `ShEx.Validation` | PASS |  |  |
| `Tableau` | BLOCKED_SELF | monomorphization stack overflow | Fatal error: exception Stack overflow |
| `Util.Log` | PASS |  |  |
| `VC.Credential` | BLOCKED_TRANSITIVE | krml fatal: Failure("nth") [failing deps in closure: SPARQL11.Algebra] | Fatal error: exception Failure("nth") |
| `XML.Namespaces` | PASS |  |  |
| `XML.Wellformedness` | PASS |  |  |
| `XPath.Eval` | BLOCKED_TRANSITIVE | monomorphization stack overflow [failing deps in closure: Parser.XPath] | Fatal error: exception Stack overflow |
| `XSD.Datatypes` | PASS |  |  |
