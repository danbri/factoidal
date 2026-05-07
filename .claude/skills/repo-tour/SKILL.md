---
name: repo-tour
description: Get oriented in the Factoidal repository layout. Use when starting work on a fresh clone, when asked "where does X live?", or when a doc references a path that's unfamiliar. Maps the dual nature of the project (verified F* spec is the product; everything else is plumbing or build artifacts).
---

# Factoidal — repository tour

The product is the F\* spec. Everything else is plumbing for getting
the F\* code into runnable form (extraction, compilation, tests) or
project documentation. The directory layout makes that visible.

```
factoidal/
├── CLAUDE.md                     short-and-tight project rules
├── README.md                     public-facing project overview
├── formal/                       VERIFIED CORE
│   ├── fstar/                    main F* tree (the product)
│   │   ├── *.fst                 verified specs
│   │   ├── Makefile              verify target
│   │   ├── build-ocaml.sh        F* → OCaml → JS/WASM pipeline
│   │   ├── ocaml-patches.sh      applies all glue patches
│   │   ├── ocaml-output/         extracted .ml + symlinks to bin/
│   │   │   ├── *.ml              extracted F* OCaml output (tracked)
│   │   │   ├── factoidal_*.ml    hand-written CLI/HTTP wrappers (TBD relocated)
│   │   │   ├── w3c_runner.ml     W3C test runner (hand-written wrapper)
│   │   │   └── *_runner.ml       per-suite runners (rdfc10, owl)
│   │   ├── minimal_regrettable_glue_code_each_with_an_open_issue/
│   │   │   └── <issue>_*.sh      assume-val realisations + bug fixes
│   │   ├── experimental_ocaml_glue/    Layer-2 unwind targets (rule #11 violators)
│   │   ├── krml-output/          F* → .krml output (gitignored, C-build pilot)
│   │   └── c-output/             krml → .c output (gitignored, future)
│   ├── roaring/                  Roaring bitmap F* port
│   │   ├── src/
│   │   │   ├── Spec.fst              abstract roaring set
│   │   │   ├── Bits.fst              popcount/tzcnt
│   │   │   ├── Container.{Array,Bitmap,Run}.fst
│   │   │   ├── IODemo.fst            file round-trip demo
│   │   │   ├── Test.fst              verification-only tests
│   │   │   ├── Makefile              standalone verify/extract/demo
│   │   │   └── iterate.sh            one-shot verify-all loop
│   │   ├── README.md
│   │   └── paper/roaring.{pdf,txt}   reference paper
│   └── third_party/              future home for vendored F* deps
│       └── (e.g. hacl-star/ for SHA-256 — see io-verification doc)
├── bin/                          PRE-BUILT BINARIES (committed, per Iron Rule #9)
│   ├── darwin-arm64/             macOS Apple Silicon
│   │   ├── factoidal             CLI binary
│   │   └── w3c_runner            test runner
│   ├── linux-x86_64/             Linux x86-64 (statically linked)
│   │   ├── factoidal
│   │   └── w3c_runner
│   └── ci-linux-x86_64/          CI shadow build artifacts
├── third_party/                  VENDORED CORPORA + DATA
│   ├── testing/                  W3C test fixture submodules
│   │   ├── w3c/                  rdf-tests submodule
│   │   ├── rdf-canon/            RDFC-1.0 tests
│   │   ├── csvw/                 CSVW tests
│   │   ├── rml/                  RML tests
│   │   ├── shex/                 ShEx tests
│   │   ├── vc/                   Verifiable Credentials tests
│   │   └── did/                  DID tests
│   ├── data/                     vendored datasets (e.g. Wikidata samples)
│   └── README.md
├── docs/
│   ├── claude-rules/             expanded Claude rules
│   │   ├── anti-patterns.md      full text of the 25 numbered rules
│   │   ├── current-state.md      F* inventory, assume-val table, scores
│   │   ├── performance.md        Turtle parser audit, speed plan
│   │   ├── scope.md
│   │   └── README.md             index
│   ├── designissues/             architecture decisions
│   │   ├── 2026-05-07-c-build-and-roaring-plan.md
│   │   ├── 2026-05-07-query-planning-fstar-recovery.md
│   │   ├── 2026-05-07-io-verification-and-third-party.md
│   │   ├── fstar-purity-unwind.md (TBD)
│   │   ├── fstar-ocaml-boundary-audit.md (TBD)
│   │   └── (many historical drift / fix design docs)
│   ├── skills/                   narrative how-to docs
│   │   ├── testing.md
│   │   ├── measuring.md
│   │   ├── optimising.md
│   │   ├── improving-sparql.md
│   │   ├── rdf-format-conversion.md
│   │   └── periodic-review.md
│   ├── code-name-glossary.md     Yod6 / Tet3 / etc. — historical decoder ring
│   ├── test-results/
│   │   ├── latest.json           most recent W3C run
│   │   ├── history/              timestamped JSON snapshots
│   │   └── index.html            dashboard (deployed to gh-pages)
│   └── fstar-extracted/          js_of_ocaml output for browser demo
├── .claude/
│   ├── skills/                   skill files (this skill, fstar-env, etc.)
│   ├── settings.json             permissions, hooks
│   └── settings.local.json       local overrides
├── .github/
│   ├── workflows/                CI configs
│   │   ├── check-extraction.yml
│   │   ├── check-fstar-purity.yml      (Omega3 — rule #11 gate)
│   │   ├── w3c-tests.yml
│   │   └── (...)
│   └── scripts/
├── kgx/                          SPARQL CONSTRUCT queries (future)
├── design_issues/                older design notes (e.g. roaring_fstar_plan.md)
└── junk/do_not_use/              vibe-coded artifacts (DO NOT USE)
```

## "Where do I add a new ___?"

| Adding | Goes in |
|---|---|
| F\* spec module | `formal/fstar/<Module>.fst` (or `formal/roaring/src/` for roaring) — and add to the for-loop in `build-ocaml.sh extract` and to `COMMON_MODULES` |
| Hand-written CLI tool | Currently `formal/fstar/ocaml-output/<name>.ml`; **target home** is `bin/<consumer>/` per the recovery plan (Phase 8 of the F\*-only query-planning plan) |
| `assume val` realisation | A patch file in `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/<issue>_<desc>.sh` referenced by `ocaml-patches.sh` |
| Vendored 3rd-party F\* code | `formal/third_party/<lib>/` (see I/O verification design doc) |
| Architecture decision doc | `docs/designissues/<YYYY-MM-DD>-<topic>.md` |
| How-to / operational guide | `docs/skills/<topic>.md` (narrative) AND/OR `.claude/skills/<topic>/SKILL.md` (Claude-invocable) |
| Anti-pattern war story | New numbered entry in `docs/claude-rules/anti-patterns.md`; one-line summary in `CLAUDE.md` |
| W3C test data | Don't add — submodules. Update the submodule pin if the W3C suite version changes |

## "I see X in a commit message — what's it mean?"

- `Yod6`, `Tet3`, `Lamed3`, `Mem5`, `Pe5`, `Bet7`, `Tav5`, `Heth3`,
  `Vav3`, `Psi3`, …: see `docs/code-name-glossary.md`. **No new
  short-codes.** Use descriptive names for new things.
- `Omega3`: F\*-purity CI gate (`.github/workflows/check-fstar-purity.yml`).
- `Mim3`, `Mim2`: pre-warm fallback infrastructure (mostly retired).

The recovery plan
(`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`)
maps every short-code to a real name + target F\* module.

## What this skill does NOT do

- Doesn't navigate inside files — for that, just open them.
- Doesn't track every tweak to the layout — major moves are
  recorded in `docs/designissues/` plan docs.
