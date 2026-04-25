# Yod5 — Issue #100 commit graph + safe merge plan (2026-04-25)

Read-only diagnostic. Do NOT commit. Untracked scratch.

## TL;DR

- `claude/main` and the two feature branches share a common ancestor at
  `be27bf9` (Phase 0 — already on main). Phase 0 + Phase 1 are already
  on main.
- The Phase 2 branch (`claude/100-phase2-cottas-ondisk`, PR #101) carries
  6 commits; none of those 6 are on main yet.
- The Phase 2.5 branch (`claude/100-phase2.5-backend-wiring`, PR #102) is
  branched off Phase 2 and adds 6 more commits — three of which are
  unrelated to issue #100 (paper-Q3 rewriter / closure docs / import
  guides) and have already been cherry-picked to main with new SHAs.
- PR #102's base is `claude/100-phase2-cottas-ondisk`, NOT `claude/main`,
  so it cannot merge until #101 lands first (or its base is retargeted).
- Three duplicate-pair sets exist (kaph2 doc, tav3 doc, import docs) and
  one near-duplicate (cloudflare tunnel + parquet-footer Gap B) where the
  same logical change exists with two SHAs.
- Nothing on the feature branches has the recent `claude/main` commits
  `7384b7d` (Wave 18 patch-65 fix), `a893fe8` (paper-Q3 gaps 1+3),
  `0362988` (Phase 1 compound indexes). Phase 2 branch will need a rebase
  before merge so it builds against the current `gs_indexed` graph_store
  shape.

## Branch geometry

```
claude/main           ── ... be27bf9 ──── 2ed10a8 ── 832d2f2 ── 3925b84
                                                                    │
                                                                    ├── 4162767 (parent7)
                                                                    │   ...
                                                                    ├── 08eaab4 (Phase 1 design doc)
                                                                    ├── 7d0dd84 (multi-row-group doc-only)
                                                                    ├── 359803f (CI shadow builds)
                                                                    ├── f3763a0 (multi-row-group F* + glue) ← real work
                                                                    ├── 81e4f21 (cloudflare tunnel) — duplicate of 79f985c
                                                                    ├── 0362988 (Phase 1 compound indexes)
                                                                    ├── 940239b (kaph2 doc) — duplicate of 6c0312b
                                                                    ├── bcd324b (COTTAS-on-Parquet v1 spec)
                                                                    ├── 1517810 (tav3 doc) — duplicate of 335b058
                                                                    ├── be99936 (import guides) — duplicate of 21958a8
                                                                    ├── a893fe8 (paper-Q3 gaps 1+3 closure)
                                                                    └── 7384b7d (HEAD: gs_indexed patch fix)

claude/100-phase2-cottas-ondisk ── be27bf9 ── e3ce364 ── 49e37b2 ── 92d56f3 ── 6fc3f31 ── 79f985c ── 4918e80 (HEAD)
                                                  │             │           │           │
                                                  │             └ multi-row-group doc-only (dup of 7d0dd84/92d56f3)
                                                  │
                                                  └ GB_CottasOnDisk + cottas_ondisk_*

claude/100-phase2.5-backend-wiring ── (off phase2 HEAD 4918e80)
                                       ── 6c0312b (kaph2 doc dup)
                                       ── eb54d8d (nun2 doc)
                                       ── ea7f286 (paper-Q3 rewriter gap 2)
                                       ── b958e50 (factoidal-http wiring)
                                       ── 335b058 (tav3 doc dup)
                                       ── 21958a8 (import guides dup)  (HEAD)
```

## Commit-by-commit table

| SHA       | Branch(es)                | Subject                                                    | Files                                                                     | Depends on                              |
|-----------|---------------------------|------------------------------------------------------------|---------------------------------------------------------------------------|------------------------------------------|
| be27bf9   | main, p2, p2.5            | Phase 0: indexed_graph through graph_store, drops patch 97 | `RDF.Graph.Executable.fst` (+103), `SPARQL11.Algebra.fst` (+50), `SPARQL11.Store.fst` (+28), patch 97 deleted | (root)                                   |
| 0362988   | main only                 | Phase 1: compound (S,P)/(P,O)/(S,O) indexes + BGP reorder  | `RDF.Graph.Executable.fst` (+38), `SPARQL11.Algebra.fst` (+81)            | be27bf9                                   |
| 08eaab4   | main only                 | Phase 1 scratch design doc                                 | docs/designissues only                                                    | —                                         |
| 7d0dd84   | main only                 | Parquet multi-row-group (#98 Gap B) — DOC-ONLY commit      | docs/designissues only (103 lines)                                        | —                                         |
| 92d56f3   | p2, p2.5                  | Parquet multi-row-group (#98 Gap B) — DOC-ONLY commit      | docs/designissues only (103 lines, identical to 7d0dd84)                  | DUPLICATE of 7d0dd84                      |
| f3763a0   | main only                 | Parquet multi-row-group (#98 Gap B) — REAL F* + glue       | `Parquet.Footer.fst` (+368), `cottas_runtime.sh` (16 changes)             | (none — actual code)                      |
| 81e4f21   | main only                 | Cloudflare tunnel setup helper + docs + launchd plist      | `tools/cloudflare-tunnel-setup.sh`, `tools/launchd/...`, `docs/deploy/...` | —                                         |
| 79f985c   | p2, p2.5                  | Cloudflare tunnel — same content                           | identical 530-line addition                                               | DUPLICATE of 81e4f21                      |
| e3ce364   | p2, p2.5                  | F*: GB_CottasOnDisk + cottas_ondisk_*                      | `Parser.BallyhooCOTTAS.fst` (+133), `SPARQL11.Store.fst` (+34)            | be27bf9                                   |
| 49e37b2   | p2, p2.5                  | Bet4 design doc                                            | docs/designissues only                                                    | —                                         |
| 6fc3f31   | p2, p2.5                  | Phase 2 OCaml runtime glue                                 | `experimental_ocaml_glue/cottas_ondisk_runtime.sh` (+688)                 | e3ce364                                   |
| 4918e80   | p2, p2.5                  | Phase 2 smoketest harness                                  | `build-ocaml.sh` (+24), `cottas_ondisk_smoketest.ml` (+94)                | 6fc3f31                                   |
| 940239b   | main only                 | kaph2 doc — Phase 2.5 scratch                              | docs/designissues only (74 lines)                                         | —                                         |
| 6c0312b   | p2.5                      | kaph2 doc — same content                                   | identical 74 lines                                                        | DUPLICATE of 940239b                      |
| eb54d8d   | p2.5                      | nun2 doc — paper-Q3 rewriter scratch                       | docs/designissues only                                                    | —                                         |
| ea7f286   | p2.5                      | OWL rewriter complementOf bnode (paper-Q3 gap 2)           | `OWL.QueryRewrite.fst` (+139)                                             | (independent of #100)                     |
| b958e50   | p2.5                      | Phase 2.5 factoidal-http wiring                            | `factoidal_http.ml` (+194/-33)                                            | e3ce364, 6fc3f31, plus indexed_dataset_backend symbol — needs Phase 2 + Wave 18 patches |
| 1517810   | main only                 | tav3 doc — paper-Q3 closure gaps 1+3                       | docs/designissues only (122 lines)                                        | —                                         |
| 335b058   | p2.5                      | tav3 doc — same content                                    | identical 122 lines                                                       | DUPLICATE of 1517810                      |
| be99936   | main only                 | Import guides (TriG/N-Quads/Turtle → COTTAS)               | `docs/import/*` + scratch                                                 | —                                         |
| 21958a8   | p2.5 only                 | Import guides — same content                               | identical 909-line addition                                               | DUPLICATE of be99936                      |
| a893fe8   | main only                 | OWL closure gaps 1+3 (paper-Q3 witness + disjointWith)     | `RDF.Graph.Executable.fst` (+173/-2)                                      | (independent of #100)                     |
| 7384b7d   | main only (HEAD)          | Wave 18 patches — gs_indexed across post-extract patches   | patches 57, 65 — fix `gs_graph={...}` literal shape after Phase 0          | be27bf9 (it's the patch that unblocks the OCaml compile after Phase 0) |
| bcd324b   | main only                 | COTTAS-on-Parquet v1 format spec                            | `docs/...`                                                                 | —                                         |
| 4162767   | main only                 | parent7 finish — strip query-bnode existentials in SELECT *| `SPARQL11.Algebra.fst` likely                                              | (independent)                             |
| 359803f   | main only                 | CI dual-platform shadow builds                             | `.github/workflows/...`                                                   | —                                         |

(p2 = `claude/100-phase2-cottas-ondisk`, p2.5 = `claude/100-phase2.5-backend-wiring`)

## Duplicates explained

Three pairs are identical-content cherry-picks of doc-only or
infrastructure commits where the same change was authored on two branches
nearly simultaneously:

1. **kaph2 Phase 2.5 scratch doc** — `940239b` (main) ≡ `6c0312b` (p2.5).
2. **tav3 paper-Q3 closure-gaps-1-3 scratch doc** — `1517810` (main) ≡ `335b058` (p2.5).
3. **import guides** — `be99936` (main) ≡ `21958a8` (p2.5).
4. **cloudflare tunnel** — `81e4f21` (main) ≡ `79f985c` (p2). The
   cloudflare commit is on the Phase 2 branch but is unrelated to
   issue #100 and snuck in during Bet4's branch work.
5. **Parquet multi-row-group (#98 Gap B) doc-only** — `7d0dd84` (main) ≡
   `92d56f3` (p2 + p2.5). The "real" code commit `f3763a0` (main only)
   is **separate** from the doc commit — `f3763a0` is the 368-line
   `Parquet.Footer.fst` addition + 16-line `cottas_runtime.sh` switch;
   `7d0dd84`/`92d56f3` are 103-line provenance notes about it. The
   commit's own message is honest about this: "the actual F\* + glue
   changes landed in 75315bc by accident". So the Gap B *implementation*
   exists exactly once on main (`f3763a0`) — the duplicate is just the
   note pointing at it. **The Phase 2 / Phase 2.5 branches do NOT carry
   the actual `Parquet.Footer.fst` Gap B code** (`f3763a0` is main-only).
   Phase 2 branch's `cottas_ondisk_runtime.sh` may or may not depend on
   the new `_in_row_group` helpers — needs verification at rebase time.

When Phase 2 / Phase 2.5 are rebased onto current `claude/main`, all the
duplicate pairs collapse automatically (git sees the patch is already
applied and drops it, or you `--strategy-option=ours` / drop them with
interactive rebase).

## PR status (gh pr view)

| PR  | State | Mergeable  | Base                              | Head                                  | Notes |
|-----|-------|------------|-----------------------------------|---------------------------------------|-------|
| 101 | OPEN  | MERGEABLE  | `claude/main`                     | `claude/100-phase2-cottas-ondisk`     | 6 commits — Phase 2 |
| 102 | OPEN  | MERGEABLE  | `claude/100-phase2-cottas-ondisk` | `claude/100-phase2.5-backend-wiring`  | 6 commits, base is PR #101 not main |
| 84  | OPEN  | (older)    | —                                 | `claude/rdf-sparql-test-status-3VW7j` | unrelated to #100, ignore |

Both #101 and #102 report MERGEABLE, but that is the GitHub
"no-merge-conflict" definition. **Build-correctness is a separate
question** because Phase 2 was branched before `7384b7d` (Wave 18 patch
fix that adds `gs_indexed` to graph_store literals in patches 57 and
65). After Phase 0 (`be27bf9`) reshaped `graph_store`, those patches
break the OCaml compile until `7384b7d` is in. Phase 2 branch sits at
the parent of `7384b7d`, so `./build-ocaml.sh` on the merged result is
expected to fail at patch-65 application unless the merge brings
`7384b7d` along (which it does, if main is the merge base).

## Dependency graph (logical, not git-topology)

```
be27bf9 (Phase 0 — on main)
   └─ 0362988 (Phase 1, on main)
   └─ 7384b7d (patches gs_indexed — UNBLOCKS post-Phase-0 OCaml build)
   └─ e3ce364 (Phase 2 F* GB_CottasOnDisk)
        └─ 6fc3f31 (Phase 2 OCaml runtime glue)
             └─ 4918e80 (Phase 2 smoketest binary)
             └─ b958e50 (Phase 2.5 factoidal-http wiring)
                   needs: e3ce364 + 6fc3f31 + indexed_dataset_backend (already in be27bf9)
                          + 7384b7d-style gs_indexed-aware patches
```

Independent of #100 chain (carried along by branches but should not
gate the merge):

- `ea7f286` (paper-Q3 rewriter gap 2) — pure F* in OWL.QueryRewrite.fst
- `a893fe8` (paper-Q3 closure gaps 1+3) — already on main
- import guides, cloudflare tunnel — docs/infra only

## Recommended merge order

State on entry: `claude/main` HEAD is `7384b7d`. Phase 0 + Phase 1 +
Wave-18 patch fix + `f3763a0` (real Gap B code) are already there. The
RDF-XML regression flagged in the request is from `a893fe8` (already on
main).

1. **(if regression must be cleared first)** Decide: revert `a893fe8`
   on main, OR fix-forward in a follow-up. Note that `a893fe8` is
   independent of issue #100 — reverting it does NOT block the Phase 2
   merge; it only matters if the user does not want to ship Phase 2
   on top of a known regression. If the regression is downstream
   (test-suite-only, no build break), keep it and merge Phase 2 anyway.

2. **Rebase PR #101 (`claude/100-phase2-cottas-ondisk`) onto current `claude/main`**.
   Expected outcomes:
   - `92d56f3` (Gap B doc) — drops as already-applied (≡ `7d0dd84`).
   - `79f985c` (cloudflare) — drops as already-applied (≡ `81e4f21`).
   - `e3ce364`, `49e37b2`, `6fc3f31`, `4918e80` — apply cleanly (they
     touch `Parser.BallyhooCOTTAS.fst`, `SPARQL11.Store.fst`, new
     `experimental_ocaml_glue/cottas_ondisk_runtime.sh`, new
     `cottas_ondisk_smoketest.ml`, no overlap with main).
   - Verify `./build-ocaml.sh` builds — `7384b7d`'s patch fixes are now
     present so `gs_indexed` is consistent.
   - Run `bin/<platform>/cottas_ondisk_smoketest` against parliament
     corpus to validate Phase 2 acceptance.
   Rationale: Phase 2 is a strict superset on top of main; rebase first
   shrinks the diff to only the four genuinely-new commits.

3. **Merge PR #101 → `claude/main`**. Now main has Phase 0 + Phase 1
   + Wave-18 + Phase 2.

4. **Retarget PR #102's base from `claude/100-phase2-cottas-ondisk`
   to `claude/main`** (`gh pr edit 102 --base claude/main` or via UI).
   This is essential — leaving `claude/100-phase2-cottas-ondisk` as
   the base after that branch is merged leaves PR #102 dangling.

5. **Rebase PR #102 (`claude/100-phase2.5-backend-wiring`) onto current
   `claude/main`**. Expected drops:
   - `6c0312b` (kaph2 doc) — drops as already-applied.
   - `335b058` (tav3 doc) — drops as already-applied.
   - `21958a8` (import guides) — drops as already-applied.
   - `eb54d8d` (nun2 doc), `ea7f286` (rewriter gap 2), `b958e50`
     (factoidal-http wiring) — apply cleanly.
   Result: PR #102 shrinks to 3 real commits.

6. **Verify PR #102's `b958e50` factoidal-http wiring still compiles**.
   The wiring references `indexed_dataset_backend` and
   `cottas_ondisk_dataset_backend` from `SPARQL11.Store.fst`. Confirm
   both are present in main after step 3.

7. **Merge PR #102 → `claude/main`**.

8. **(optional cleanup)** Decide what to do about `ea7f286` and
   `eb54d8d` — they are paper-Q3 rewriter work that bundled along with
   Phase 2.5. They are not strictly part of issue #100. They could be
   split into a separate PR before merging #102, but if they verify
   clean and don't touch issue-#100 code paths, leaving them in the
   Phase 2.5 merge is fine.

## Things the user should know

- **Phase 2 branch carries an unrelated cloudflare-tunnel commit
  (`79f985c`)** that is identical to `81e4f21` already on main. This is
  fine — rebase will drop it — but worth noting that branch hygiene
  slipped.
- **Phase 2.5 branch carries unrelated paper-Q3 work** (`eb54d8d` doc
  and `ea7f286` OWL.QueryRewrite.fst). The OWL closure side of paper-Q3
  (gaps 1+3, `a893fe8`) is already on main; the rewriter side (gap 2,
  `ea7f286`) is *only* on the Phase 2.5 branch. So that rewriter change
  effectively rides into main on PR #102 unless explicitly split out.
- **The Gap B parquet-footer code (`f3763a0`) is on main but NOT on the
  Phase 2 branch.** Only the doc-only sibling (`92d56f3`) is on Phase
  2. This means Phase 2's `cottas_ondisk_runtime.sh` (in commit
  `6fc3f31`, 688 lines of post-extract glue) was written against the
  multi-row-group dispatcher symbols that live in `f3763a0`. **Verify at
  rebase time** whether the runtime glue references those symbols (e.g.,
  `probe_parquet_column_decode_all_row_groups`); if it does, Phase 2
  cannot build standalone — it relies on `f3763a0` being on main first.
  This is fine because `f3763a0` IS on main; just keep it in mind if
  someone tries to compile the Phase 2 branch in isolation.
- **PR #102's base is the Phase 2 branch, not main.** GitHub will keep
  showing PR #102 as "MERGEABLE" against the Phase 2 branch right up to
  the moment that branch is deleted post-merge. After PR #101 lands,
  retarget PR #102's base to `claude/main` BEFORE deleting the Phase 2
  branch — otherwise PR #102 closes automatically.
- **Three doc-only duplicate pairs and one infra-duplicate pair will
  collapse automatically on rebase.** No manual cleanup needed; just
  expect git to say "patch is already applied" and skip them.
- **Stash entries `6aba080` and `c0d85c4`** are leftover WIP/index
  stashes from the Phase 2.5 branch (visible as "WIP on
  claude/100-phase2.5-backend-wiring"). They are not on any branch
  ref — purely refs/stash. Cleanup is `git stash drop` if confirmed
  unwanted.
- **No CI status was captured** — PR mergeability is "no conflicts",
  not "tests pass". Run `gh pr checks 101 --repo danbri/factoidal` and
  `gh pr checks 102 --repo danbri/factoidal` before merge.

## File-touched summary by branch

**Phase 2 branch unique additions** (4 real commits, 1085 lines net):
- `formal/fstar/Parser.BallyhooCOTTAS.fst` (+133)
- `formal/fstar/SPARQL11.Store.fst` (+34)
- `formal/fstar/experimental_ocaml_glue/cottas_ondisk_runtime.sh` (+688, NEW file)
- `formal/fstar/ocaml-output/cottas_ondisk_smoketest.ml` (+94, NEW file)
- `formal/fstar/build-ocaml.sh` (+24)
- design docs

**Phase 2.5 branch unique additions** (3 real commits, ~340 lines net,
of which ~140 are unrelated to #100):
- `formal/fstar/ocaml-output/factoidal_http.ml` (+194/-33) — issue #100 work
- `formal/fstar/OWL.QueryRewrite.fst` (+139) — paper-Q3 rewriter (NOT issue #100)
- design docs
