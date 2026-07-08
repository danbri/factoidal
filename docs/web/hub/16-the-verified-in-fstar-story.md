---
title: "The verified-in-F* story"
description: "Why F*, what verified actually means here (with the standing qualifier quoted, not hidden), the skimmable core, one source extracted to four targets, and what proofs — and one proof gap — bought this project."
layout: hub.njk
series: docs-hub
series_order: 16
vocab: none
status: published
tests: tests/hub/post16_test.mjs
---

Fifteen posts in this series ran F\*-extracted code in your browser
without ever showing you F\* itself. This last post closes that gap:
why the project is built this way, what "verified" actually means for
this codebase, and — since the point of verification is to catch real
bugs — what it bought, and once didn't.

## Why F\*

This project's [`CLAUDE.md`](https://github.com/danbri/factoidal/blob/claude/main/CLAUDE.md)
states two rules before anything else:

> 1. **F\* is the source of truth.** All RDF/SPARQL logic lives in
> `.fst` files.
> 2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen
> OCaml` or KaRaMeL for C/WASM. Never vibe-code an implementation that
> "mirrors" the spec.

The reasoning is structural, not aesthetic: a hand-written parser or
evaluator that "mirrors" the RDF/SPARQL specs can drift from them
silently — a missed edge case just looks like a bug to fix later. An
F\* module that states RDF 1.1's rules as types and refinements (the
kind [post 01](./01-triples-rdf-from-first-principles.md) walked
through) and is checked by Z3 before it can extract at all doesn't
have that failure mode for whatever it does state — see the qualifier
below for what it doesn't yet.

## What "verified" means here — the qualifier, quoted

Every README, demo page, and PR in this project carries this exact
sentence until the recovery work it names lands, per `CLAUDE.md`'s
Iron Rule #11:

> parser and algebra spec verified in F\*; on-disk backend has
> unverified OCaml-side optimization layers being migrated back to F\*
> (see fstar-purity-unwind.md)

Concretely: the RDF/SPARQL parsers and the query algebra — the code
paths every post in this series exercised, in-memory, in your browser
— are F\*, checked under Z3 4.13.3 with no `--lax` and no
`--admit_smt_queries` (Iron Rule #10). The **on-disk** COTTAS reader is
where the qualifier still bites, though less than it did. The production
SPARQL query path — `RDF.Store.Capabilities.Cottas.fst`'s `sc_solve` /
`sc_estimate` / `sc_count_exact`, the functions
[post 15](./15-how-fast-the-performance-story.md)'s numbers run through
— was rewired to F\*-extracted token-direct (`_tok`) entry points in
`RDF.CottasStore.fst`, so those hot paths no longer go through the
hand-written OCaml in `experimental_ocaml_glue/cottas_ondisk_runtime.sh`.
That 928-line glue file has **not** been deleted, so the qualifier
stands: three non-production consumers still call the older id-based
entry points — a `tests/unit` buffer-vs-file baseline, the
`cottas-ondisk-smoketest` binary, and `factoidal-explain`. Retirement
(zero live callers, then patch deletion) is gated on migrating those
three, tracked in
[#118](https://github.com/danbri/factoidal/issues/118). The row-by-row
state lives in
[`docs/designissues/fstar-ocaml-boundary-audit.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/fstar-ocaml-boundary-audit.md),
which supersedes the older `fstar-purity-unwind.md` inventory. This post
doesn't soften that qualifier — it's the boundary of what "verified"
claims.

## The skimmable core

Most of this tree is written for F\* tooling first and a human reader
second — [`SPARQL11.Algebra.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL11.Algebra.fst)
alone is 5,777 lines. `RDF.Term.fsti` is a deliberate exception: it's
written, per its own banner, to be read start-to-finish by someone who
knows RDF but not F\*:

```fstar
module RDF.Term

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.1/§3.3 step 5; restructured 2026-07-05 per the owner's
// reading-order critique — see skills/fstar-module-style/SKILL.md's
// ".fsti reading-order convention". Full history/exclusion-list in
// RDF.Term.fst's banner.
// If you know RDF but not F*: skim the `///` comments; concepts run
// uninterrupted from "Blank nodes" to the "Appendix" divider below.
```

That's the whole opening block of
[`formal/fstar/RDF.Term.fsti`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Term.fsti)
on branch `claude/main` — a direct instruction to the reader about how
to read the file. What follows really does honor it: blank nodes, then
IRIs, then literals, then the three-way `rdf_term` sum type ([post 01](./01-triples-rdf-from-first-principles.md)
quoted that part), each concept in its own `///`-commented block, with
the mechanical stuff (XSD constant boilerplate, structural-equality
lemmas) pushed into an `Appendix` section clearly marked at the bottom
rather than interleaved. Reading this one file — not a tutorial about
it — is the fastest way to see what "F\* as source of truth" actually
looks like for RDF's term algebra.

## One source, four extraction targets

Nothing in this series' live cells is hand-written JavaScript
mirroring the spec — every cell called the *same* F\*-extracted
engine `bin/linux-x86_64/factoidal` runs, just compiled to a different
target:

```observable-js
return pretty([
  { target: "Native (OCaml)", command: "build-ocaml.sh extract && compile",
    output: "bin/<platform>/factoidal, w3c_runner", status: "full W3C pass counts" },
  { target: "JavaScript (js_of_ocaml)", command: "build-ocaml.sh js",
    output: "docs/fstar-extracted/factoidal.js",
    status: "runs in any modern browser or Node -- every live cell in this series" },
  { target: "WebAssembly (wasm_of_ocaml)", command: "build-ocaml.sh wasm",
    output: "docs/fstar-extracted/factoidal.wasm.js",
    status: "Wasm-GC engines (Chrome >= 119, Node >= 22); npm-entry ABI lags the JS build (post 12)" },
  { target: "C (KaRaMeL)", command: "build-ocaml.sh karamel",
    output: ".c/.h pilot bundle",
    status: "pilot: KaRaMeL-compatible core modules only, not yet the whole query engine" },
]);
```

Same `.fst`/`.fsti` sources, four different `fstar.exe --codegen`
targets. The native binary is what the W3C test runners score; the
js_of_ocaml build is what every `observable-js` cell in this series has
been calling; the wasm_of_ocaml build exists but (per
[post 12](./12-the-api-tour.md)) its capability surface still lags;
KaRaMeL's C output is a pilot over a KaRaMeL-compatible subset of
modules, not the whole engine yet — scoped in
[`docs/designissues/2026-05-07-c-build-and-roaring-plan.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-05-07-c-build-and-roaring-plan.md)
rather than rounded up.

## What proofs bought

Three concrete events — two where the proof discipline paid off
directly, one where it didn't yet reach:

**1. A proved round-trip lemma for the delta-log format.** Durable
UPDATE needs a crash-safe on-disk log of pending changes.
Per Iron Rule #11, the byte layout of that log had to be specified in
F\*, not assembled ad hoc in OCaml — and it was: `RDF.Store.Columnar.DeltaLog.fst`
states `lemma_term_roundtrip`/`lemma_triple_roundtrip`/a whole-log
round-trip lemma and F\* checks them before any OCaml ever touches a
delta-log byte. Commit
[`868a20b`](https://github.com/danbri/factoidal/commit/868a20b),
2026-07-06 — "delta-log entry format in F\* with a proved round-trip."

**2. A one-constant writer/reader mismatch caught by a failing
boot-time check, not a silent wrong answer.** The COTTAS on-disk
reader's dict-companion validator expected magic bytes `'COTD'`; the
F\* writer (`RDF.CottasStore.DictWriter.fst`) had been emitting
`'COKD'` since an earlier migration. The validator did its job — it
failed loudly ("header verify FAILED") on every boot rather than
trusting a file that didn't match its own contract, forcing a full
sidecar rebuild every time (57.3 seconds, per
[post 15](./15-how-fast-the-performance-story.md)'s table) until the
one-constant fix corrected it
([`4b9fd72`](https://github.com/danbri/factoidal/commit/4b9fd72)) — the
failure mode this project's own crypto/hash policy
calls out by name: fail loud on a format mismatch, never silently
trust unverified bytes.

**3. The reverse example: a real bug proof coverage did not yet
reach.** The CS-clustered on-disk store's compound-`(p,o)` search
path silently returned zero matches for a query that should have
returned one — not a crash, a wrong answer. Root cause:
`filter_candidates_by_compound_po` (in verified F\*,
`RDF.CottasStore.fst`) resolved its predicate/object IDs through the
OCaml `assume val` revmap (first-occurrence order over the physical
row scan), while the on-disk `.po.presence` bitmap the writer built
used a *different*, also-deterministic ID space (sorted lexicographic
rank). Both sides individually type-checked and individually verified
fine — F\*'s type system has no way to know "these two functions must
agree on an ID space" unless a lemma says so, and none did. The two
ID spaces happened to coincide on data small enough that physical row
order already correlated with alphabetical order, so nothing caught
the divergence until CS clustering reordered rows and a three-way
agreement check (CS-clustered vs. producer-order COTTAS vs. the
in-memory engine, same data) caught the wrong answer directly. Fixed
by routing the reader through the *same* sorted-rank encoding the
writer used, verified F\*, no `experimental_ocaml_glue/` change.
Commit [`1576873`](https://github.com/danbri/factoidal/commit/1576873),
2026-07-06 — "fix compound-po ID-space mismatch: silent wrong answers
on clustered stores." The lesson this project draws from it isn't
"verification failed" — it's that verification proves exactly the
properties someone wrote down as a type or a lemma, and this project's
own test suites (the ones every other post in this series cites pass
counts from) are what caught the property nobody had stated yet.

## The scale of the spec

The spec is large — on the order of 140 F\* modules and tens of
thousands of lines, split across the RDF term algebra, the SPARQL
parser and algebra, the storage layer, and the format codecs. A count
in any single doc is a claim about the tree at one moment; the tree
moves, which is why every `assume val` carries its own stub patch and
named open issue (Iron Rule #3) rather than a single trust-me total. To
count for yourself: `find formal/fstar -maxdepth 1 -name '*.fst*' | wc
-l` for modules and a `grep -c '^assume val'` sweep for the gaps. The
per-module `assume val` breakdown lives in
[`skills/ocaml-boundary/SKILL.md`](https://github.com/danbri/factoidal/blob/claude/main/skills/ocaml-boundary/SKILL.md)
and `current-state.md`'s "assume val inventory" section.

## Related

The delta-log proof story above is one piece of the read-write store.
[The next post](./17-mutating-and-serving-data.md) covers SPARQL 1.1
Update live in your browser, the durable delta-log write path, and what
`factoidal-http` and the Graph Store Protocol do and don't do.

The live cell above is pinned in
[`tests/hub/post16_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post16_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API the same way every other post in this series pins its cells.
