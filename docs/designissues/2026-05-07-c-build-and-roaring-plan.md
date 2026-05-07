# 2026-05-07 — F\* debt reduction + C build + Roaring continuation plan

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

- **F\* test scores (unchanged for weeks; OCaml→F\* migrations are
  pure refactors, so they shouldn't move the dial — and don't):**
  SPARQL 626 pass, 1 fail, 4 skip out of 631 (99.84% pass-vs-fail,
  99.2% pass-vs-total). RDF 1031 pass, 0 fail out of 1031 (100%).
  Combined: 1657/1658 = 99.94% pass-vs-fail.
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

**Pilot results (this PR, 2026-05-07):**

`fstar.exe --codegen krml` was run on the candidate allowlist.
Results:

| Module | krml result | Notes |
|---|---|---|
| `SPARQL.JSON.Escape.fst` | ✅ Clean | char-list manipulation, fuel-bounded |
| `SPARQL.Update.Analysis.fst` | ✅ Clean | tree-walk over `update_op` ADT |
| `SPARQL.Query.Analysis.fst` | ✅ Clean | tree-walk over `query` ADT |
| `SPARQL.HTTP.StaticFiles.fst` | ✅ Clean | extension→MIME mapping |
| `SPARQL.HTTP.QueriesIndex.fst` | ✅ Clean | pure string assembly |
| `RDF.Format.fst` | ⚠️ KaRaMeL failure: `todo: translate_pat [MLP_Const]` on `format_of_extension` and `format_of_string` (string-pattern match in match arms) | Refactor to `if/else if` chain |

The `.krml` files for the five clean modules are produced under
`formal/fstar/krml-output/` (gitignored). The next step — running
`krml` on those files to emit `.c` + `.h` — is blocked on a
toolchain install:

**KaRaMeL install gap:** `opam install karamel` fails on the
`fstar` switch (4.14.1) because karamel's transitive `wasm = 1.1.1`
constraint requires `ocaml < 4.13` and the upstream `conf-python-2-7`
package depends on a system Python 2.7 that's no longer available
on Ubuntu 24.04. Three paths forward (any one unblocks the C-build
demo):

1. **Build karamel from source** in a dedicated opam switch with
   `ocaml < 4.13`. Fragile but works.
2. **Use a pre-built karamel binary** from an HACL\* / EverCrypt
   release artifact on GitHub.
3. **Pin a newer `wasm` version** in karamel's opam file (it's
   pinned to `1.1.1` for historical reasons; recent `wasm`
   releases work on 4.14).

The .krml-emitting half of the pipeline is provably working with
the existing F\* install. Once any of the above lands a `krml`
binary on `PATH`, the rest of the pipeline lights up.

### 2.3.1 Sequenced steps

1. **This PR**: adds `formal/fstar/build-ocaml.sh karamel` step
   that runs `fstar.exe --codegen krml` on the pilot allowlist
   and stages the `.krml` files; gitignore the output dir.
   Documents the install gap in this design doc.
2. **Next PR**: install `krml` (one of the three paths above),
   plumb its invocation into the build script, produce
   `formal/fstar/c-output/*.{c,h}` for the pilot modules.
3. **Demo PR**: `c-demo/json_escape_demo.c` links the krml
   output and calls `SPARQL_JSON_Escape_json_escape("a\"b")`.
   Compares byte-for-byte against the OCaml path.
4. **Refactor PR**: convert `RDF.Format.fst`'s string-match arms
   to `if/else if` chains; unblock its krml extraction. (Other
   modules like `SPARQL.HTTP.StaticFiles.fst` already use
   `if/else if` — that's why they extracted cleanly.)
5. **Iterate**: add modules one at a time. Tracker in
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
