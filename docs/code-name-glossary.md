# Code-name glossary

The project's design docs and code comments are full of cryptic
short-codes (`Yod6`, `Tet3`, `Lamed3`, `Mem5`, `Pe5`, `Vav3`,
`Bet7`, …). They originated as **subagent task names** when work
was dispatched to multiple agents in parallel, then calcified
into pseudo-jargon used in commits, traces, and design docs.
They communicate nothing to anyone who wasn't in the room when
the agent was dispatched.

This file maps each code to a one-line description and a primary
artefact reference. **New code added to this project should use
descriptive names, not new short-codes.** When editing existing
docs, replace cryptic codes with descriptive phrases; keep the
short-code in parentheses on first occurrence if it's already
widely used.

When you see one of these in a commit message or comment, look
it up here. When in doubt, the doc references are authoritative.

---

## COTTAS / on-disk backend optimisations

| Short-code | Plain description | Primary artefact |
|-----|-----|-----|
| **Mem4** | Cross-query F\* page cache for DLBA column decode (avoids per-cell `Array.of_list`). | `RDF.CottasStore.PageCache.fst` |
| **Mem5** | Estimate-via-presence-bitmap fast path; per-rg cardinality from `.presence` without column decode. | `RDF.CottasStore.fst:cottas_ondisk_estimate` |
| **Pe4** | Per-row-group search trace stats (timings, candidate count). Emits `[pe4-trace]` to stderr. | `RDF_CottasStore.ml:891` |
| **Pe5** | `factoidal --explain` mode: plan-only dump of algebra + cardinality estimates, no execution. | `factoidal_explain.ml`; `2026-04-26-pe5-explain-mode.md` |
| **Vav3** | Persistent companion files (`.dict`, `.presence`, …) replacing the 107s / 1.4 GB in-memory pre-warm. mmap'd on demand. | `RDF.CottasStore.OnDiskIndex.fst` |
| **Psi3** | F\*-source-of-truth read API for presence-bitmap companion files. | `RDF.CottasStore.PresenceBitmap.fst` |
| **Mim2** | First iteration of mmap'd companion-file readers (pre-Vav3). | (mostly retired) |
| **Mim3** | Pre-warm lazy-fallback warning log line. Emits `[mim3-trace]`. | `RDF_CottasStore.ml` |
| **Bet5** | Earlier hashtable-cache iteration (largely retired by Vav3). | (historical) |
| **Bet7** | Lazy populate of in-RAM Hashtbls when companion files are absent / fail. Emits `[bet7-trace]`. | `cottas_ondisk_z_lazy_open.sh` (glue, retired in spirit) |
| **Tau3** | Audit doc reviewing whether Bet7 can be retired. | `2026-04-26-tau3-bet7-retire-audit.md` |
| **Yod6** | Predicate-presence row-group prune. Bitmap says "predicate X *might* appear in row-group Y"; lets the evaluator skip RGs that can't match. | `cottas_ondisk_zzz_yod6_pred_presence_prune.sh`; F\* equivalent in `RDF.CottasStore.fst:480-525` |
| **Tet3** | Subject + object presence row-group prune (analogous to Yod6 for S and O columns). | `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh` |
| **Lamed3** | Per-row-group predicate row-offset index (`.p.offsets` mmap'd file). Goal: `?s rdf:type ?o LIMIT 5` from 6s → <200ms. | `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` |
| **Qof3** | Distinct count discovery per dictionary column. Emits `[qof3-trace]`. | `RDF_CottasStore.ml` |
| **Aleph6** | Streaming COUNT(\*) + LIMIT pushdown fast paths. | `cottas_ondisk_zz_aleph6_count_limit.sh` |
| **Resh3** | Migration of `cottas_ondisk_search` / `_estimate` / `_search_limited` from OCaml glue back to F\* (Phases 2.5 of the purity unwind). | `2026-04-25-resh3-phase-A-fstar-purity.md`; PR #122 |

## HTTP server policy

| Short-code | Plain description | Primary artefact |
|-----|-----|-----|
| **Tav5** | Result-row cap circuit breaker. `--max-rows N`. Emits `[tav5-trace]` when triggered. | `factoidal_http.ml` |
| **Heth3** | SIGALRM-based per-query timeout (`--query-timeout SECS`, default 120s). Process-global; flagged in audit §A as architecturally wrong, retire-pending. | `factoidal_http.ml:with_query_timeout` |

## CI / process

| Short-code | Plain description | Primary artefact |
|-----|-----|-----|
| **Omega3** | The F\*-purity CI workflow (rule #11 recurrence guard) — soft-mode, scans diffs in OCaml glue + watched hand-written .ml files for net-new semantic logic. | `.github/workflows/check-fstar-purity.yml`; `2026-04-26-omega3-ci-purity-check.md` |

---

## Going forward

1. **No new short-codes.** Name new things descriptively. If the
   thing is too long for a function name, the codebase will accept
   `predicate_presence_prune_v2` over `Kaph7`. Future readers will
   thank us.
2. **In existing docs**, when you touch a section that uses a
   short-code, expand it on first occurrence: "Yod6 (predicate-
   presence prune)". Don't churn-rewrite docs that aren't being
   touched.
3. **In new commit messages**, always say what changed, not which
   short-code it pertains to. "fix predicate-presence prune for
   compound (s,p) bindings" beats "fix Yod6 for compound bindings".
4. **In F\* / OCaml comments**, prefer the descriptive name.
   Cross-reference the short-code only if needed for git-archaeology
   ("originally landed as Yod6").
5. **In trace tags** (the `[yod6-trace]`-style stderr lines),
   keep the short-codes for backward compatibility with existing
   greps and dashboards. Trace tags are an exception because
   third-party tooling may already match on them.

If a short-code is missing from the table above and you can't
figure out what it means from context, that's a bug — file a PR
adding it.
