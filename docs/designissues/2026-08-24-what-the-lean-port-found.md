# What the Lean port found, and why the findings have one shape

Written 2026-08-24, after 22 landings on branch
`claude/autoexec-scratchpad-assess-37oeok`.

The Lean 4 port started from zero code on 2026-08-22. It now covers 192
of 220 F\* modules: 325 files, 114,232 lines, `lake build` green at 772
jobs, zero `sorry`, zero user `axiom`, zero `native_decide`.

The line count is not the result. The result is fifteen findings.
Eleven of them have the same shape, and this document says what that
shape is and what follows from it.

## 1. The evidence

### Group A — eleven findings with one shape

| # | Finding | Where |
|---|---|---|
| A1 | `SPARQL11.Parser.AskBgpRoundTrip.fst` declares the payload-token round trip IMPOSSIBLE. `FStar.String.sub` exposes only a length refinement, so no branch of the scanner fires for any input. In Lean the tokenizer works on `List Char` end to end, and the same statement is an ordinary induction. | [#562](https://github.com/danbri/factoidal/issues/562) |
| A2 | `RDF.Entailment.RDFS.FixedPoint.fst` stops short of its theorem (a). In Lean the closure length test IS a fixed-point test, because `Graph.add t g = if g.mem t then g else g ++ [t]` — a membership-guarded append, never a key-sorted dedup. The theorem closes. | [#560](https://github.com/danbri/factoidal/issues/560) |
| A3 | Six F\* modules, 3,284 lines, exist to repair one non-injective composite string bucket key, or to supply the proof infrastructure that repair needs. The Lean tree needs none of them. | [#559](https://github.com/danbri/factoidal/issues/559) |
| A4 | `Parquet.Footer.fst` reads every byte of a Parquet file as a two-character hex string. All three of its I/O `assume val`s return hex text; the word `hex` appears 701 times in 3,349 lines. Confirmed on the hot path 2026-08-24: two full hex round trips per column chunk, and the OCaml side already holds the raw bytes. | [#566](https://github.com/danbri/factoidal/issues/566) |
| A5 | `Literal.eqb` folds language-tag case and compares `rdf:XMLLiteral` lexical forms by exclusive canonical XML. It is strictly coarser than literal term equality. The same over-coarse test was reached from the SPARQL end (finding SR-2) and from the simple-entailment end (finding SE-1). | `SPARQL/AlgebraRefinement.lean` |
| A6 | `Binding.compatible` tests every pair in the association list. `sval` sees only the first binding for a variable. So the engine decides a relation on LISTS and the specification states one on MAPPINGS, and they disagree on a duplicate-key list. | `SPARQL/AlgebraRefinement.lean` |
| A7 | Adding `HDT/Store.lean` made `SPARQL11.Store` — 1,452 lines, no Lean counterpart at all — disappear from the not-covered list, and took five more modules with it. Both names end in `Store`. | hazard #31 |
| A8 | An alias was added, the module was ported, and the coverage count did not move. A `git stash` cycle had dropped the edit to the measuring tool. The number on screen was correct for the state before the landing. | tenth correction, `2026-08-23-lean-port-gap.md` |
| A9 | `tools/lean-port-gap.py` read its Lean module list from a session scratchpad. It reported a module as not covered minutes after that module's file landed. | hazard #30 |
| A9b | The F\* proof that `C rdfs:subClassOf C` is not an axiomatic triple needs `--fuel 50 --z3rlimit 600 --split_queries always` and must EXCLUDE one unrelated symbol's facts, because that symbol's definition equation in the SMT context tips a borderline `assert_norm`. Raising the budget did not recover it. The Lean proof is a case split on a finite table with no budget, no splitting and no filtering. | `RDFS/ReflexivityWitness.lean` |
| A10 | Lean has its own wall, in a different place. `readIriRefBody` has ten match arms; generating its per-arm equation lemmas exhausts the container's memory. And the kernel does not reduce `String.mapAux`, so `decide` cannot evaluate `"en".toLower = "EN".toLower`. | [#565](https://github.com/danbri/factoidal/issues/565) |

### Group B — two ordinary defects, no pattern

| # | Finding | Where |
|---|---|---|
| B1 | `matchObject` did not recurse into RDF 1.2 triple terms. It fell straight to `termMatch`, which compares a triple term's interior by identity, so `_:a p <<( x q _:b )>>` matched only a premise carrying the same interior label. Simple entailment was incomplete. Fixed. | [#564](https://github.com/danbri/factoidal/issues/564) |
| B2 | `rdf:PlainLiteral` is never decoded in the Lean RIF tree. A missing case in `RIF.Translation.termOfConst`. | [#561](https://github.com/danbri/factoidal/issues/561) |

### Group C — one finding that is genuine mathematics

Finding C-1, ported this session into `RDFS/RhoDfCompleteness.lean`.
"RDFS entailment equals simple entailment of the RDFS closure" is
FALSE, and no fragment predicate on the two graphs repairs it. From
`[X rdfs:subClassOf Y]`, `CondSubClassOfIc` puts `X` in IC and
`CondSubClassOfRefl` forces `[X rdfs:subClassOf X]`. No closure of a
finite graph produces that triple. Both halves are now theorems:
`rdfsEntails_subclassSelfLoop` and
`rhoDf_not_entails_subclassSelfLoop`.

This one is about RDFS. It would appear in any faithful formalisation,
in any language, with any representation. It is here as the control: it
shows the method can tell the two kinds of finding apart.

### Group D — one proof-hygiene failure

A theorem whose hypothesis restated its conclusion type-checked and
proved nothing, under a heading claiming an obligation was closed
(hazard #29).

## 2. Three false leads

**"F\* is the problem."** No. A10 is Lean's own wall, and it blocks a
round-trip theorem the F\* tree also cannot state. Both trees have
places where the host language obstructs the proof. The walls are in
DIFFERENT places, and that difference is what makes the method work.

**"The port is a translation exercise."** No. A translation reproduces
the source's shapes. Every finding in group A came from NOT reproducing
them — from writing the Lean side against the W3C text and then
comparing.

**"These are fourteen unrelated bugs."** No. Two are unrelated (group
B), one is mathematics (group C), one is proof hygiene (group D). The
other ten share a form, stated next.

## 3. The cause

In each of the ten, an artefact of how something was WRITTEN was read
as a fact about what it MEANS.

- A1: a scanner's string primitive has no base-value equations. That
  was read as "the round trip cannot be stated".
- A2: `add` was a key-sorted dedup. That was read as "the fixed-point
  theorem does not follow from the length test".
- A3: a composite key was a concatenated string, so it was not
  injective. That was read as 3,284 lines of necessary repair.
- A4: bytes were carried as hex text. That was read as 3,349 lines of
  necessary decoding.
- A5, A6: the engine compares list representations. That was read as
  deciding the specification's relation on mappings.
- A7, A8, A9: a module name and an alias-table entry represent a
  module. Matching or missing them was read as the fact of coverage.
- A9b: an SMT context's sensitivity to which definitions are in scope.
  That was read as the difficulty of proving a fact about the RDFS
  axiom tables.
- A10: Lean's match compilation and string primitives. Those are being
  read correctly, as representation, which is why the blocker is filed
  as a refactor rather than as a limit on what can be proved.

The rule, stated literally, without figure of speech: **a property that
depends on how a value is encoded is a property of the encoding, and
carries no information about the specification the value denotes.** The
`counting-coverage` skill states the measurement instance of this rule
and its checks.

## 4. The method that exposed it

Two independent formal trees, written against the same W3C
specifications, with DIFFERENT representations:

| | F\* tree | Lean tree |
|---|---|---|
| strings | `FastString`, axiomatised primitives | `String` and `List Char` |
| graph insert | key-sorted dedup | membership-guarded append |
| bucket key | concatenated string | structured value |
| assumed values | `assume val` | records of functions, or parameters |
| bytes at the Parquet boundary | hex text | not ported yet ([#566](https://github.com/danbri/factoidal/issues/566)) |

A property that holds in both trees is about RDF or SPARQL. A property
that holds in one is about that tree's representation. The port is a
differential experiment, and the second tree is a control rather than a
spare implementation.

The strongest measured support is the by-design bucket. Fourteen
modules are classified as wanting no Lean counterpart. Here is every
one, with the reason:

| Modules | F\* lines | Why no counterpart |
|---|---|---|
| `Parser.FastString.*` (7) | 2,861 | an F\* string representation with axiomatised primitives; Lean's `String` and `List Char` need none of it |
| `RDF.Indexed.KeyInjectivity`, `RDF.Indexed.Completeness`, `RDF.Entailment.RDFS.SepFree`, `RDF.Entailment.RDFS.ChainWf` | 2,679 | repair a non-injective composite string key |
| `OWL.Semantics.MemLemmas` | 442 | the proof infrastructure that repair needs |
| `RDF.CottasStore.ColumnSeq` | 163 | an array shim for F\*'s pure fragment |
| `RDF.List.Helpers` | 195 | list lemmas Lean's standard library already has |
| **Total** | **6,340** | |

6,340 of the F\* tree's 169,736 lines say nothing about RDF or SPARQL.
They are there because of how the F\* side is written. That figure was
not estimated. Each module was read and classified, and the tool
recomputes the total on every run.

## 5. What follows

**1. `Parquet.Footer` is the largest instance, and question 1 is now
answered.** A4 is the same shape as A3, at 3,349 lines instead of
3,284. The owner's suspicion, raised 2026-08-23 — *"we already have a
basic SPARQL and it builds on Parquet so the huge size in F\* is
suspicious"* — was well founded.

Traced 2026-08-24 (structure, not yet benchmarked). The hex route is on
the HOT PATH: `parquet_read_range_hex` is called at data-page offsets,
and `parquet_zstd_decompress_hex` decompresses column-chunk data. One
compressed column chunk makes this journey: raw bytes → hex text in
OCaml → bytes again inside the C stub → `ZSTD_decompress` → hex text
again in C → per-byte hex indexing in F\*. Two full hex round trips and
four allocations, and steps 2, 4 and 6 exist only to change the type at
the F\*/OCaml boundary.

The finding that makes it fixable: **the OCaml side already has the raw
bytes.** `parquet_read_range` and `parquet_read_tail` are defined in
the glue at lines 113 and 126; `parquet_read_range_hex` calls the first
and then hex-encodes. The C stub decodes hex to bytes internally before
`ZSTD_decompress` and re-encodes after. Both sides want bytes. Only the
F\* type signature wants hex. So this is a boundary-type change, not a
rewrite of the Thrift decoder.

The representation also forced two caches into `experimental_ocaml_glue`,
and their own comments record the cost that bought them: without the
file-bytes cache, *"hundreds of file-opens per SELECT and hundreds of
zstd decompressions; the daemon hangs"*; without the hex cache, a query
walking every row group *"re-hex-encodes the SAME parquet-page byte
ranges once per sibling probe function"*. Neither cache has any
eviction.

⚠️ **A correction to this document's own first-pass claim.** The
2026-08-23 report said the cost was "twice the memory, as text". That
was wrong. With the caches the real shape is the whole file held once
as raw bytes, plus a hex string retained for every distinct range ever
probed, never released. The prediction was right about the cause and
wrong about the profile, which is the kind of error a first pass makes
and a trace corrects.

**2. The remaining 28 modules are three different jobs.** 14 want no
port and are counted above. 10 are engine code, 18,020 lines, and 6 of
those are the COTTAS and Parquet group that [#566](https://github.com/danbri/factoidal/issues/566)
may change. 4 are proof modules, 9,479 lines, and `OWL.Semantics.Soundness`
is 3,865 of them.

**3. The measurement rules are the same rules.** A7, A8 and A9 are the
coverage tool committing the same error as the code it measures. They
are written up in `skills/counting-coverage/SKILL.md` with the eight
checks that catch them.

## Related

- `docs/designissues/2026-08-23-lean-port-gap.md` — the running record
  of every time the coverage count was wrong, and the method that was
  wrong each time.
- `skills/counting-coverage/SKILL.md` — the measurement rules.
- `formal/lean4/PORT_NOTES.md` — one section per landing.
- <https://github.com/danbri/factoidal/issues/404> — the work tracker.
