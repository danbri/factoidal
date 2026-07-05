# 2026-05-07 — F\* debt reduction + C build + Roaring continuation plan

Last refreshed: 2026-05-07 (suite scores re-measured against live runner).

## Objective

Three coordinated tracks, executed in parallel where independent:

1. **Reduce F\* debt.** Continue the OCaml→F\* migration; retire
   `assume val`s where realisable; shrink the
   `experimental_ocaml_glue/*.sh` patch surface.
2. **C build pilot.** Get *something* compiling end-to-end via
   KaRaMeL (`--codegen krml` → `krml` → `*.c` + `*.h` → linkable
   library). Aim: a verified RDF/SPARQL primitive callable from C.
3. **Roaring continuation.** Phase B → C → D → E of the existing
   phased plan in
   [`design_issues/roaring_fstar_plan.md`](../../design_issues/roaring_fstar_plan.md),
   each as a single-PR slice.

These tracks reinforce each other: the C-build pilot picks
KaRaMeL-compatible modules first (no `noeq`, no OCaml-runtime
deps), which is *also* the criterion for the Roaring phase work,
and *also* aligns with the cleaner OCaml→F\* migrations because
those tend to be `noeq`-free pure-data transforms.

## Status going in (2026-05-07 morning)

- **F\* test scores (re-measured 2026-05-07; OCaml→F\* migrations are
  pure refactors, so they shouldn't move the dial — and don't):**
  SPARQL 630 pass, 1 fail (out of 631; 99.84%). RDF 1031 pass, 0 fail
  out of 1031 (100%). Combined: 1661 pass, 1 fail (out of 1662).
- **OCaml glue:** ~4779 LoC across 9 `factoidal_*.ml` files; `S`-class
  semantic content has shrunk dramatically across the recent 13-PR
  migration cluster.
- **F\* modules:** 55 `.fst` files. **20** of them are `noeq`-free
  pure-data modules (KaRaMeL pre-flight candidates).
- **`assume val` count:** 122 across 26 modules — but most are
  realisations in the COTTAS/Parquet backend perf layer
  (rule-#11(c) compliant), not the verified core.
- **Roaring:** Phase A complete (PR #137 merged). Five containers
  worth of work to go before serialisation lands.

## Track 1 — F\* debt reduction (concrete next migrations)

Pick from the deferred list in
[`2026-05-06-overnight-followup-session-status.md`](2026-05-06-overnight-followup-session-status.md)
and the audit doc.

### 1.1 Quick wins (each one PR, no new infra)

- [ ] `bs_json` — JSON renderer for `bound_status` (depends on
  PR #155 which has merged; ready to go).
- [ ] `tp_explain` + `tpx_json` — Pe5 explain-row record and its
  JSON renderer (extends `SPARQL.Explain.fst`).
- [ ] `kind_label` + `is_test_type_iri` from `owl_runner.ml` —
  small RDF-test-runner helpers (lift to a new
  `OWL.Tests.Manifest.fst`).
- [ ] `term_nq` / `subj_nq` / `triple_nq` in `rdfc10_runner.ml` —
  duplicates of `RDF.NQuads.Serialize.fst`; replace with
  delegations.
- [ ] `escape_literal_lexical` in `rdfc10_runner.ml` — same
  duplicate-of-F\*-version pattern.

Total: ~5 small PRs, each ~−15 to −30 OCaml LoC.

### 1.2 Medium-complexity (each blocks on infrastructure)

- [ ] **Query-timeout migration** (`with_query_timeout`,
  `query_timeout_response`). Blocks on building F\*
  `time_budget` + `cancellation_polled` infrastructure
  (`assume val cancellation_polled : unit -> bool` glue + a
  fuel-bounded "check between every N evaluator steps"
  pattern). One design PR, then one migration PR. ~50 LoC
  retired.
- [ ] **503 Retry-After during COTTAS load.** Same blocker as
  query-timeout. Easier once the time-budget plumbing exists.
- [ ] **Pe5 `--explain` planner deduplication.** Walks BGP
  output to collapse equal triple-patterns. Pure structural
  analysis on the algebra; lift to
  `SPARQL.Query.Analysis.fst` (PR #149's target module).

### 1.3 Big-ticket structural cleanup

- [ ] **COTTAS perf layer migration** (Layer 2 of
  `fstar-purity-unwind.md`). Replace each `experimental_ocaml_glue/
  *.sh` patch with verified F\* code where feasible. ~14
  patches; multi-PR.
- [ ] **Sort `build-ocaml.sh` module list** so future migrations
  alphabetise their insertion point. Eliminates the recurring
  "two PRs adding adjacent lines" merge conflict (the dominant
  collision class during the 2026-05-06/07 push).
- [ ] **Restructure `SPARQL.HTTP.Response.fst`** by concern (cors
  / errors / status / head). Same conflict-prevention rationale.
  Defer until next round of PRs are queued.

## Track 2 — C build pilot

KaRaMeL is the F\*→C compiler. It has stricter constraints than
OCaml extraction; not every F\* module survives.

### 2.1 KaRaMeL constraints (from project experience)

- ✅ Pure / Tot effects only. No `IO` / `Exn` / `ML`.
- ❌ `noeq` types. KaRaMeL needs structural equality to lower
  records to C structs.
- ⚠️ Strings: KaRaMeL has limited string support; pure
  manipulations work, but the OCaml-style `string` type extracts
  as a pointer + length pair, with subtle ownership semantics.
- ⚠️ Lists: KaRaMeL extracts `list a` to a tagged union with
  manual memory management. Often viable but generates more code
  than OCaml's GC-friendly version.
- ❌ Polymorphic top-level functions (without explicit
  monomorphisation) — KaRaMeL specialises eagerly.
- ❌ `assume val` with non-trivial signatures — needs C-side stub
  that satisfies the type signature.

### 2.2 KaRaMeL-compatible inventory (today)

20 `.fst` modules are `noeq`-free in the current tree. The
**smallest** + **purest** ones are the most-likely candidates for
a first C build:

| Module | LoC | Verdict |
|---|---:|---|
| `RDF.Format.fst` | 92 | ✅ Likely. Pure string→variant mapper. |
| `SPARQL.JSON.Escape.fst` | 100 | ✅ Likely. Char-list manipulation, fuel-bounded. |
| `SPARQL.Update.Analysis.fst` | 31 | ✅ Likely. Single predicate over `update_op` ADT. |
| `SPARQL.Query.Analysis.fst` | 52 | ✅ Likely. Tree-walk over `query` ADT. |
| `SPARQL.Diagnostics.fst` | 76 | ⚠️ Depends on `SPARQL11.Algebra` (which has `noeq`). |
| `RDF.NQuads.Serialize.fst` | 111 | ✅ Likely. Pure string-of-`triple` shaping. |
| `RDF.Pretty.fst` | 201 | ⚠️ Depends on `SPARQL11.Algebra` (`noeq`). |
| `SPARQL.HTTP.Response.fst` | 243 | ⚠️ Mostly pure but uses `option string` heavily. |
| `SPARQL.HTTP.QueriesIndex.fst` | 108 | ✅ Likely. Pure string assembly. |
| `SPARQL.HTTP.StaticFiles.fst` | 77 | ✅ Likely. Pure string→string lookup. |
| `Parser.FastString.fst` | 131 | ⚠️ Has `assume val` realisations needed. |
| `Parser.IRI.fst` | 447 | ✅ Larger but pure. Good ambitious target. |
| `RDF.CottasStore.PageCache.Bounds.fst` | small | ✅ Likely. Pure. |

### 2.3 Pilot plan (this PR + next)

**Pilot results (updated 2026-07-05; original .krml-only run 2026-05-07):**

The chain now runs end to end for four modules:
`tools/karamel-c-build.sh` drives F\* → `.krml` → `krml` → `.c`/`.h`
→ `gcc` → a linked demo binary whose 10 checks (format lookup,
case-insensitivity, unknown-extension fallback, MIME lookup, JSON
escaping through the `Parser.FastString` byte stubs) all pass.

| Module | krml (.krml) | krml → C | gcc | Notes |
|---|---|---|---|---|
| `RDF.Format.fst` | ✅ Clean | ✅ | ✅ | `if/else if` refactor landed (#200 G3); demo calls `RDF_Format_format_of_extension(".ttl")` → `Some Turtle` from C |
| `SPARQL.JSON.Escape.fst` | ✅ Clean | ✅ | ✅ | C stubs realise the `Parser.FastString` `assume val`s (same trust boundary as the OCaml realisation) |
| `SPARQL.HTTP.StaticFiles.fst` | ✅ Clean | ✅ | ✅ | MIME lookup exercised from C |
| `SPARQL.HTTP.QueriesIndex.fst` | ✅ Clean | ✅ | ✅ | compiles + links; not demo-exercised (needs list construction from C) |
| `SPARQL.Update.Analysis.fst` | ✅ Clean | ❌ blocked | — | drags in `SPARQL11.Algebra`; krml monomorphizer blows the OCaml stack (default ulimit) or exceeds 20 min at 4.3 GB RSS (unlimited stack) |
| `SPARQL.Query.Analysis.fst` | ✅ Clean | ❌ blocked | — | same `SPARQL11.Algebra` blocker |

Measured (2026-07-05, 4-core sandbox): Group A F\* extraction ~2 min
(warm `.checked` cache), krml lowering < 5 s, gcc + link < 5 s,
demo 10 pass, 0 fail (out of 10). Generated `Factoidal_Pilot.c`
23 KB / `.h` 4.7 KB.

**Commit decision:** the generated `formal/fstar/c-output/*.{c,h}`
for the pilot bundle are committed (each carries KaRaMeL's
generated-by header with the exact invocation), mirroring rule #9's
committed-binaries spirit — a fresh clone can `gcc` and link the
pilot without an F\*/karamel toolchain. `.krml` intermediates, logs,
and objects stay gitignored (`formal/fstar/.gitignore`).

**Analysis-modules blocker (Group B):** both Analysis modules emit
`.krml` cleanly, but their dependency graph includes all of
`SPARQL11.Algebra` (which pulls `RDF.Graph.Executable`), and krml's
monomorphization/inlining passes do not survive that AST: OCaml
`Stack overflow` at the default stack limit, > 20 min at 4.3 GB RSS
with `ulimit -s unlimited`. `tools/karamel-c-build.sh --group-b`
reproduces. Unblocking needs either the planned `SPARQL11.Algebra`
stratification (split the ADT from the evaluator — see the
`fstar-module-style` roadmap) or upstream krml work; parked until
then.

**KaRaMeL install gap (SOLVED 2026-05-10, re-validated 2026-07-05):**
the opam-repo `karamel` v1.0.0 package is dead on Ubuntu 24.04
(wants `wasm = 1.1.1` → OCaml < 4.13, plus Python 2.7). Upstream
master already relaxed all three constraints — clone git master and
build. Full recipe:
[`2026-05-10-krml-install-notes.md`](2026-05-10-krml-install-notes.md).
2026-07-05 re-validation: karamel master commit `11bb8e1ac2f7`,
deps + `make minimal` in a dedicated `karamel` opam switch
(OCaml 4.14.1) took ~12 min on a fresh 4-core sandbox; `krml`
installed to `/usr/local/bin/krml`; checkout kept at
`/root/karamel` (its `include/` and `krmllib/dist/` headers are
needed at gcc time — `KRML_HOME` in the build script). The `fstar`
switch is untouched. One correction to the 2026-05-10 notes' dep
list: `sedlex` must also be in the `opam install` line.

### 2.3.1 Sequenced steps

1. ✅ **Landed**: `formal/fstar/build-ocaml.sh karamel` step that
   runs `fstar.exe --codegen krml` on the pilot allowlist and
   stages the `.krml` files; gitignored the output dir.
   Documented the install gap in this design doc.
2. ✅ **Landed 2026-07-05**: `krml` installed (git-master build —
   see install notes doc); `tools/karamel-c-build.sh` scripts the
   full chain; `formal/fstar/c-output/Factoidal_Pilot.{c,h}`
   produced and committed.
3. ✅ **Landed 2026-07-05** (folded into step 2's script):
   `formal/fstar/c-output/demo/format_demo.c` links the krml
   output; calls `RDF_Format_format_of_extension(".ttl")`,
   `SPARQL_JSON_Escape_json_escape("a\"b\n")`, and the MIME
   lookup end-to-end; asserts the same answers the OCaml path
   gives (10 pass, 0 fail, out of 10).
4. ✅ **Landed** (commit f7b72e0 tree): `RDF.Format.fst` string
   matches are `if/else if` chains; krml extraction is clean
   (zero Warning 250).
5. **Iterate**: add modules one at a time. Next candidates per
   §2.2: `RDF.NQuads.Serialize.fst`, `Parser.IRI.fst`,
   `RDF.CottasStore.PageCache.Bounds.fst`. The Analysis pair is
   parked on the `SPARQL11.Algebra` blocker above. Tracker in
   `docs/designissues/c-extraction-status.md` once it grows
   beyond a handful.

### 2.4 What this enables

- C consumers (`librdfcore.a`, FFI from Rust/Python/Go).
- WebAssembly via `clang -target wasm32` — a path independent
  of the current `js_of_ocaml` route, with much smaller binaries.
- Confidence that the verified core is genuinely portable, not
  accidentally OCaml-shaped.

## Track 3 — Roaring continuation

Per the existing plan in `design_issues/roaring_fstar_plan.md`.
Phase A landed in PR #137. Continue:

### 3.1 Phase B — bitmap container (this PR series)

- New file `formal/roaring/src/Container.Bitmap.fst`
  with:
  - `bitmap_container = { bits : seq u64; cardinality : nat }`
    plus the invariant `cardinality = sum (popcount bits[i])`.
  - `denote_bitmap`, `bitmap_contains`, `bitmap_insert`,
    `bitmap_remove`, `bitmap_cardinality`.
  - Reuses the pure-F\* `popcount_u64` from `Bits.fst` (already
    landed in PR #137).
  - Lemmas tying `popcount` to `denote_bitmap`.
- Test cases via `assert_norm` for empty, singleton, double-insert,
  remove-then-reinsert.

### 3.2 Phase C — run container (next PR)

- `Container.Run.fst`:
  - `run_container = list (start, length-1)` with non-adjacency
    invariant.
  - Standard ops + per-call cardinality computation.
- Single-run-spans-whole-chunk predicate as a separate def for
  use in serialisation.

### 3.3 Phase D — container sum type (next PR)

- `Container.fst` = sum type with promotion/demotion proofs.

### 3.4 Phase E — top-level Roaring (next PR)

- `Roaring.fst` = sorted assoc `list (u16 * container)`.

### 3.5 Phase F+ — set algebra, serialisation, integration (later)

Per the existing plan §4 phases F→J.

## Sequencing (concrete)

| # | What | Track | Estimated effort |
|---|---|---|---|
| 1 | This plan PR (this commit) | meta | 10 min |
| 2 | Roaring Phase B (bitmap container) | 3 | 1-2 hours |
| 3 | C-build pilot — minimal allowlist + 3 modules | 2 | 1-2 hours |
| 4 | Roaring Phase C (run container) | 3 | 1-2 hours |
| 5 | `bs_json` migration | 1.1 | 30 min |
| 6 | `term_nq` / `subj_nq` / `triple_nq` delegation in `rdfc10_runner.ml` | 1.1 | 30 min |
| 7 | C demo program (`format_demo.c`) | 2 | 30 min |
| 8 | Roaring Phase D (container sum) | 3 | 1-2 hours |
| 9 | `kind_label` migration to OWL.Tests.Manifest.fst | 1.1 | 30 min |
| 10 | Roaring Phase E (top-level Roaring) | 3 | 2 hours |

Each is a single self-contained PR. Continuing past #10 unlocks
the harder migrations in §1.2 (which need new F\* infrastructure
first).

## Done criteria

For Track 1 (debt): the LoC tracker in
`docs/designissues/fstar-ocaml-boundary-audit.md` shows
factoidal_http.ml's S-class surface < 200 LoC after this batch.
After full §1.2 lands, < 50 LoC. Goal is the qualified-verification
language in CLAUDE.md rule #11 can be unqualified.

For Track 2 (C build): `make c-extract` produces a working
`librdfcore.a` linkable by a C demo, and `RDF_Format_format_of_string`
is callable from C with byte-equivalent results to the OCaml path.

For Track 3 (Roaring): all five Phase A→E modules verify cleanly
under z3 4.13.3 with no `--lax`. The Phase F set-algebra lemmas
discharge against the Phase A spec.
