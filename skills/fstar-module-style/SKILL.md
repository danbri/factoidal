---
name: fstar-module-style
description: How Factoidal's F* source is organized and written — the semantic-core vs implementation-pragmatics split, module naming, the planned stratification of RDF.Graph.Executable and SPARQL11.Algebra, interface-file (.fsti) policy, verification requirements (no --lax, z3 4.13.3, --admit_smt_queries disclosure), F* syntax traps (comment nesting, reserved words), and KaRaMeL-compatible style. Use when creating or reorganizing .fst modules, when an F* "Syntax error" makes no sense, when deciding where a definition belongs, or when writing F* that should later extract to C.
---

# F\* module organization and style

The F\* specifications are the product (Iron Rule #1). This skill is
about keeping them readable as specifications: the standards' meaning
stated as clearly and abstractly as possible, with implementation
choices — indexes, fast paths, byte layouts, caches — visibly
elsewhere. The long-term goal is that someone can read the core of
RDF, RDFS, OWL, RIF, and SPARQL from the F\* alone.

## Layout today

All ~92 modules live **flat** in `formal/fstar/*.fst` — no `src/`
tree, no `.fsti` interface files (zero exist as of 2026-07). Domains
are expressed by dotted-name prefixes:

- `RDF.*` — terms, triples, graphs, datasets, formats, canonicalization
- `SPARQL11.*` / `SPARQL.*` — algebra, parser, protocol, update,
  planning, HTTP logic
- `Parser.*` — concrete syntaxes (N-Triples, Turtle, N-Quads, TriG,
  XML, RDF/XML, RIF-XML, SRX, CSV/JSON results)
- `OWL.*`, `RIF.*`, `SHACL.*`, `Tableau` — reasoning
- `Parquet.*`, `RDF.CottasStore.*`, `Parser.Ballyhoo*` — storage

New modules must be wired into **three lists** in `build-ocaml.sh`
(extract loop, `COMMON_MODULES`, `FSTAR_MODULES`) or you get
source-without-build-wiring (`workflow-gotchas-debugging` §3).

## The two tiers: spec core vs pragmatics

The codebase is deliberately bimodal. Keep it that way, and when
adding code, decide which tier it belongs to before writing it.

**Semantic core** (datatypes + declarative semantics; what the W3C
specs mean): `RDF.Graph.Executable` (terms/graphs), `SPARQL11.Algebra`
(algebra + evaluation semantics), `SPARQL11.Parser`, `RDF.Canonical`,
`Tableau`, `OWL.QueryRewrite`, `RIF.Core.*`, `SHACL.Validation`,
`SPARQL11.IRI.Resolve`, `XML.Wellformedness`, the pure
`SPARQL.HTTP.*` / `SPARQL.Plan.*` decision logic.

**Pragmatics** (implementation choices; how we make it fast or
persistent): `Parser.FastString` and the byte-indexed parser hot paths
(issue #70/#89 banners), `RDF.CottasStore.*` (page cache, mmap
indexes, presence bitmaps, dict/offset writers), `Parser.Ballyhoo*`
(HDT backends), `Parquet.Footer`, `RDF.Bytes`, `RDF.List.Helpers`
(tail-recursion), `SPARQL.Eval.Limits`/`TimeBudget` (circuit
breakers).

Rules of thumb:

- A pragmatic module should carry a banner comment naming the issue or
  design doc that motivates it, and should relate back to the abstract
  definition it accelerates — ideally with a correctness lemma of the
  shape `denote (optimised x) == denote (naive x)` (the recovery-plan
  pattern from
  `docs/designissues/2026-05-07-query-planning-fstar-recovery.md`).
- Never let a pragmatic concern leak into a core module when it can be
  a separate module that the core knows nothing about.
- Descriptive names only; **no new codenames** (Yod6/Tet3-style names
  are banned — `docs/code-name-glossary.md` is a decoder for the
  historical ones, not a licence for new ones).

## Planned stratification (the reorganization roadmap)

From `docs/designissues/2026-05-08-foundational-fstar-tier.md`; do
these opportunistically, one commit-sized slice at a time, with suite
runs before/after:

- Split `RDF.Graph.Executable` (~3,500 LoC) into `RDF.Term`,
  `RDF.Triple`, `RDF.Graph` plus `RDFS.Closure`, `OWL.Closure`,
  `XSD.Axioms` — today an OWL-closure edit fires every CI suite
  because everything imports the monolith.
- Split `SPARQL11.Algebra` (~6,000 LoC, 251 KB) along the same lines:
  algebra datatypes / evaluation semantics / function library /
  numerics-XSD value space.
- Maintain the foundational-tier discipline: class F modules
  (currently `RDF.Graph.Executable`, `RDF.Format`, `Parser.IRI`,
  `Parser.FastString`, `OWL.Vocabulary`) fire every suite on change;
  budget ≤10 modules in that class. Domain (D) and consumer (C)
  classes trigger their own suites via `.github/test-suites/*.yaml`.

### Interface files (`.fsti`) — policy

F\*'s `.fsti` mechanism is one way to separate "what" from "how", but
it is not the only one, and we have not adopted it yet. Considerations
before introducing them:

- `.fsti` shines when you want to **hide** a representation and force
  clients through an abstract signature — a good fit for the storage
  backends (`RDF.CottasStore.*`) where the F\* signature *is* the
  boundary contract realised by OCaml glue.
- For the semantic core, plain small modules + explicit lemmas often
  read better than signature/implementation splits, and they keep
  extraction wiring simple (one `.fst` = one `.ml`).
- Whatever is chosen, do it module-by-module with the full suite green
  at each step, and update the three `build-ocaml.sh` lists and the
  `.fst.checked` cache expectations. Don't convert the tree wholesale.

## Verification requirements

- **No `--lax`, no `--admit_smt_queries`** for new work (Iron Rule
  #10). One legacy exception exists: `SPARQL11.Parser.fst` is ~65%
  under `--admit_smt_queries true` — disclose this whenever claiming
  "verified", and shrink it when touching that file.
- z3 must be exactly **4.13.3**; the Makefile and `build-ocaml.sh`
  pass `--z3version 4.13.3`.
- `make verify` covers only the short `MODULES` list (5 core modules).
  Full-tree checking happens as a side effect of
  `./build-ocaml.sh extract` (every module through
  `--cache_checked_modules`). Don't read "make verify passed" as
  "whole tree verified".
- For interactive proof/diagnosis, use the F\* MCP server
  (`fstar-mcp` skill) instead of batch `fstar.exe` reruns.
- Every `assume val` is an acknowledged gap: stub patch in
  `minimal_regrettable_glue_code_each_with_an_open_issue/` named
  `<issue>_<description>.sh` + an open GitHub issue (Iron Rule #3).

## Syntax traps (memorize these)

**Comment rule (hard, owner-ratified 2026-07-04): all NEW F\* comments
use `//` line syntax.** No new `(* ... *)` blocks — a multi-paragraph
note is a run of `//` lines. Rationale: F\* block comments NEST, so a
stray `*)` inside — e.g. quoting `construct(*)` from ARQ algebra —
closes the comment early and F\* reports a syntax error hundreds of
lines later. `//` makes the failure mode unrepresentable. Existing
`(* *)` blocks may stay until a change touches them.

The same nesting trap exists in hand-written OCaml consumers
(`bin/<consumer>/*.ml`), and OCaml has NO `//` syntax, so there the
rule is: never write `*)`, `(*`, or a bare `F` + star inside a
comment — spell it `F-star`. This bit for real on 2026-07-04: a
subagent wrote "(parsers belong in F&#42;)" in `jsonld_runner.ml` and the
build failed with a bewildered syntax error 70 lines of prose later.
Subagent briefs that ask for `.ml` or `.fst` files MUST carry this
warning (see `subagent-prompting`).

**Reserved-ish identifiers with misleading errors.** F\* rejects some
innocuous names and points the error at the line *after* the
offender: `total` (banned as a let-bound name), `synth` (reserved
meta-keyword; caught in RIF Phase 3 #223), `in_mem` and anything where
a trailing `in` can be read as the keyword. Prefix with the domain
noun (`triples_total`, `mem_dataset`). When an unexplained "Syntax
error" appears, check the line **above** the reported one first.

**Extraction-facing gotchas** (details in `build-and-test`):
`Prims.int`/`nat` extract to zarith `Z.t` — a per-operation cost that
once made the Turtle parser unusable (see `perf-benchmarking`); use
the byte-indexed `Parser.FastString` primitives on hot paths.
Recursive string-function base cases must handle the single-element
case explicitly or lang tags/datatypes get dropped (anti-pattern #9).
Handle the promoted result types `ER_Num`/`ER_Dec`/`ER_Dbl`/`ER_Bool`
alongside `ER_Term (T_Literal _)` everywhere (anti-pattern #6).

## KaRaMeL-compatible style (write for C even before we extract to it)

The C/WASM path (`fstar.exe --codegen krml`, see
`docs/designissues/2026-05-07-c-build-and-roaring-plan.md`) imposes
constraints OCaml extraction doesn't. For modules that may ever go to
C, prefer:

- `Tot`/pure functions; no `IO`/`Exn`/`ML` effects.
- No `noeq` types (OCaml tolerates them; KaRaMeL doesn't).
- **No string-literal pattern-match arms** — `RDF.Format.fst` failed
  KaRaMeL with `todo: translate_pat [MLP_Const]`; use `if/else if`
  chains on strings.
- Monomorphic top-level functions where feasible.
- Trivial `assume val` signatures only.
- Note the precedent: `Parquet.Footer` works on hex-encoded strings
  rather than raw bytes to sidestep F\*'s weak `bytes` support, at ~2×
  memory cost — a deliberate, documented trade.

## What this skill does NOT cover

- Toolchain setup and z3 install — `fstar-env`.
- Extraction/build mechanics — `build-and-test`.
- What may live in OCaml at all — `ocaml-boundary`.
- Interactive proof workflow — `fstar-mcp`.
