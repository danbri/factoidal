---
name: repo-tour
description: Get oriented in the Factoidal repository layout. Use when starting work on a fresh clone, when asked "where does X live?", or when a doc references a path that's unfamiliar. Maps the two formal trees (formal/fstar, the shipping engine; formal/lean4, the intended full-scope target) and the plumbing around them.
---

# Factoidal — repository tour

The product is the system: an RDF/SPARQL engine whose interfaces are
grounded in the W3C specifications through F\* and Lean 4 (CLAUDE.md,
founding view). Two formal trees carry it: `formal/fstar/`, the shipping
engine, and `formal/lean4/`, the Lean 4 port that is the intended
full-scope target since 2026-08-29 and already the home of the persisted
Shardborough store and the WASM module. Everything else is plumbing for
getting the formal code into runnable form (extraction, compilation,
tests) or project documentation. The directory layout makes that visible.

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
│   │   │   └── fstar_pure_hashes.ml   allowlisted hand-written assume-val realisation
│   │   ├── minimal_regrettable_glue_code_each_with_an_open_issue/
│   │   │   └── <issue>_*.sh      assume-val realisations + bug fixes
│   │   ├── experimental_ocaml_glue/    Layer-2 unwind targets (rule #11 violators)
│   │   ├── krml-output/          F* → .krml output (gitignored, C-build pilot)
│   │   └── c-output/             krml → .c output (gitignored, future)
│   ├── lean4/                    LEAN 4 PORT (self-contained Lake project; run lake only here)
│   │   ├── L4Factoidal/          the library: RDF, Syntax, SPARQL, RDFS, OWL, SHACL, ...,
│   │   │   └── Storage/          Shardborough codecs + *Theorems.lean round-trip proofs
│   │   ├── Harness/              CLIs: l4w3c, l4factoidal, l4block-* (pack/activate/query/...)
│   │   ├── Wasm/                 the ONE wasm module: Ops/, Dispatch.lean, build-wasm.sh, native-smoke.sh
│   │   └── .lake/build/bin/      built binaries (gitignored)
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
├── bin/                          BINARIES + CONSUMER SOURCES
│   ├── darwin-arm64/             committed binaries, macOS Apple Silicon
│   ├── linux-x86_64/             committed binaries, Linux x86-64 (static):
│   │                             factoidal, w3c_runner, owl_runner,
│   │                             rdfc10_runner, factoidal-http, …
│   ├── ci-linux-x86_64/          CI shadow builds (Fly deploy source of truth)
│   ├── ci-darwin-arm64/          CI shadow builds
│   └── <consumer>/               hand-written consumer .ml sources:
│                                 factoidal-cli/, w3c-runner/, owl-runner/,
│                                 factoidal-http/, factoidal-serve/, … (rule #11)
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
│   │   ├── fstar-purity-unwind.md
│   │   ├── fstar-ocaml-boundary-audit.md
│   │   └── (many historical drift / fix design docs)
│   ├── skills/                   RETIRED (pre-pivot Rust-era; see README there)
│   ├── code-name-glossary.md     Yod6 / Tet3 / etc. — historical decoder ring
│   ├── test-results/
│   │   ├── latest.json           most recent W3C run (CI-maintained)
│   │   ├── ukparliament-bench-modern.json   perf baseline (harness-maintained)
│   │   ├── history/              timestamped snapshots
│   │   └── index.html            dashboard (deployed to gh-pages)
│   ├── web/                      landing page + demo pages
│   ├── deploy/                   Fly.io / Cloudflare tunnel notes
│   └── fstar-extracted/          js_of_ocaml + wasm bundles for browser demo
├── skills/                       SKILL FILES (agentskills.io format)
│   └── <name>/SKILL.md           listed in CLAUDE.md's ## Skills section
├── tests/                        first-party harnesses (unit, local
│                                 regressions, beyond-w3c parity, web-demos)
├── tools/                        probes + benches (jena_arq_*, bench_ukpar_*)
├── .claude/
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
| F\* spec module | `formal/fstar/<Module>.fst` (or `formal/roaring/src/` for roaring) — and add to ALL THREE lists in `build-ocaml.sh` (extract loop, `COMMON_MODULES`, `FSTAR_MODULES`); see the `fstar-module-style` skill for which tier it belongs to |
| Hand-written CLI/runner/server tool | `bin/<consumer>/` (Phase 8 relocation is done — nothing hand-written goes in `ocaml-output/` except the two allowlisted assume-val realisations) |
| `assume val` realisation | A patch file in `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/<issue>_<desc>.sh` referenced by `ocaml-patches.sh` + an open GitHub issue |
| Vendored 3rd-party F\* code | `formal/third_party/<lib>/` (see I/O verification design doc) |
| Architecture decision doc | `docs/designissues/<YYYY-MM-DD>-<topic>.md` |
| How-to / operational guide | `skills/<topic>/SKILL.md` (agentskills.io format; add it to CLAUDE.md's `## Skills` section) |
| Anti-pattern war story | New numbered entry in `docs/claude-rules/anti-patterns.md`; one-line summary in `CLAUDE.md` |
| W3C test data | Don't add — submodules under `third_party/testing/`. Update the submodule pin if the W3C suite version changes |
| External (non-W3C) test suite | `tests/external/<project>/` + `THIRD_PARTY_NOTICES.md` (licence-clean only; see `test-suites` skill) |

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
