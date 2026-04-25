# 2026-04-25 — Tet2 retrospective: branch + stash turbulence (lost untracked work)

**Mode:** read-only investigation. **Status:** scratch doc, not committed.
**Author:** agent Tet2.

## TL;DR

8 stashes accumulated in ~3h between 12:52 and 14:48 BST. At least one stash
(`stash@{2}`, "kaph2 stash before phase2.5 branch", 2026-04-25 14:09:29 BST)
contains untracked files that were never committed and are not on disk:
`tools/ukparliament_trig_to_cottas.py`, `tools/ukparliament_trig_to_cottas_hybrid_escape.py`,
`tools/bench_ukpar_queries.py`, `tools/compare_rdf_parser_counts.py`,
the entire `third_party/data/ukparliament/` subtree (the 5.3M-line TriG snapshot
and ~25 vendored `.rq` queries), `codex_importer.sh`, and
`docs/2026-04-25-grand-synthesis.md`.

The stash is intact and recoverable. **One pop, in the right working tree
state, restores everything.** Recovery command at the end of this doc.

In addition: 13 branch checkouts in <90 minutes, 6 cherry-picks (5 of them
duplicating commits already on `claude/main`), and 4 `git reset` operations
including 2 destructive `reset HEAD~1` / `reset HEAD~2`. The reflog grew by
~70 entries today alone.

## Confirmed root causes

### 1. Single working tree shared across agents (the structural cause)

`git worktree list` shows one working tree at `/Users/danbri/working/factoidal`
on `claude/main`. There is a leftover branch `worktree-agent-a1a17907` pointing
at `9499c7e` from 2026-04-17 — a worktree was used in the past, then abandoned.
All today's agents shared one HEAD. Every `git checkout other-branch` swept the
tree out from under any agent mid-edit. Mitigation depends on this being
unblocked.

### 2. `git stash` (without `-u`) silently drops untracked files

stash@{0}, stash@{3}, stash@{4}, stash@{5} have no `^3` parent — they were
made without `--include-untracked`. Any new file created by an agent and
not yet `git add`-ed was simply LEFT IN PLACE and then OVERWRITTEN/REMOVED
by the subsequent `git checkout`. Some of the .py file losses described
in the prompt may have happened this way (though the kaph2 ukparliament
batch happens to have used `-u`, which is why we can recover it).

The user's report — "ukparliament_trig_to_cottas.py and a hybrid-escape
variant from last night with Codex are GONE" — matches a different
mechanism: those files were created externally (Codex), present in the
working tree on 2026-04-24 evening, then a subsequent agent ran
`git stash` (no `-u`) before a checkout. They survive **only because**
kaph2 did add them to a `-u` stash at 14:09:29.

### 3. Cherry-picking the same commit onto multiple branches

5 commit pairs have identical subjects on different branches. Examples:

| Subject                                      | On `claude/main` | On `phase2.5` |
| -------------------------------------------- | ---------------- | ------------- |
| `tav3 paper-Q3 closure-gaps-1-3 scratch doc` | 1517810          | 335b058       |
| `docs/import: TriG/N-Quads/Turtle → COTTAS`  | be99936          | 21958a8       |
| `kaph2 issue #100 phase 2.5 scratch doc`     | 940239b          | 6c0312b       |
| `parquet-footer: multi-row-group iteration`  | f3763a0          | 92d56f3 + 7d0dd84 (3 copies!) |
| `deploy: cloudflare tunnel`                  | 81e4f21          | 79f985c       |

Mechanism: agent commits to `claude/main`, second agent commits same work
on the feature branch, then someone cherry-picks one to the other.
Result: history will not fast-forward and cannot be cleanly merged.
This is the "spaghetti" the user noted.

### 4. Two `git reset HEAD~1`/`HEAD~2` events

- `13:25:51` `reset: moving to HEAD~1` (lost 75315bc temporarily — recovered)
- `13:35:17` `reset: moving to HEAD~1` (lost d6df176 — recovered as cherry-pick 4918e80)
- `13:16:09` checkout to phase2 then `reset: moving to be27bf9` (forced state)
- `13:15:57` `reset: moving to HEAD~2` (lost two commits)

Het's earlier note about "accidentally swept up other agents' staged changes"
is exactly this pattern. Of the four resets, two were `--soft`-equivalent
(checkout + reset combo), two destroyed reflog state of competing agents.
None of them lost work permanently because reflog still holds the SHAs
for now (90-day window).

## Specific incident — the lost ukparliament files

Reflog timeline:

```
2026-04-25 14:09:29  stash@{2}: "kaph2 stash before phase2.5 branch"  -u  ← LOST WORK SURVIVES HERE
2026-04-25 14:09:33  reset: moving to HEAD          (clean tree)
2026-04-25 14:09:36  checkout main → phase2-cottas-ondisk
...
```

`stash@{2}^3` (the untracked-files tree) contains:

```
tools/ukparliament_trig_to_cottas.py                       (589 lines, blob 78760fc44cddfad7...)
tools/ukparliament_trig_to_cottas_hybrid_escape.py         (114 lines, blob f8b8a0a36c5cf5e2...)
tools/bench_ukpar_queries.py                               (368 lines, blob 3893e61b0b07f249...)
tools/compare_rdf_parser_counts.py                         (196 lines, blob fdfe6c1f8a14e07a...)
third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig   (5,325,830 lines)
third_party/data/ukparliament/sparql/{detail,main}/*.rq    (25 files)
codex_importer.sh
docs/2026-04-25-grand-synthesis.md
```

These blobs are reachable, garbage-collection-safe (stash is a ref), and
will not be lost as long as the stash is preserved.

## Recovery — actionable RIGHT NOW

The two ukparliament Python tools the user specifically asked about:

```bash
mkdir -p tools
git show 'stash@{2}^3:tools/ukparliament_trig_to_cottas.py'                > tools/ukparliament_trig_to_cottas.py
git show 'stash@{2}^3:tools/ukparliament_trig_to_cottas_hybrid_escape.py'  > tools/ukparliament_trig_to_cottas_hybrid_escape.py
chmod +x tools/ukparliament_trig_to_cottas*.py
```

Or fully restore the whole untracked tree from kaph2's stash without
disturbing the index/working tree:

```bash
# Materialise the untracked tree from stash@{2} into the working dir
git checkout 'stash@{2}^3' -- .
# Then unstage so they remain untracked (review before committing)
git reset HEAD -- .
```

(Do NOT `git stash pop stash@{2}` — that also tries to apply the indexed
+ tracked-modified parts which conflict with current tree state. Use
the explicit `^3` checkout above.)

Other stashes contain genuine in-flight work and should be triaged
individually — see table at top of doc.

## Recommended discipline changes (proposed for `feedback_agent_discipline.md`)

Add as new rules 10-15 in that file:

10. **Branch switches require `git stash --include-untracked` or fail.**
    Never `git stash` without `-u`. Never `git checkout other-branch` while
    untracked files are present. The watchdog could enforce this with a
    pre-checkout hook that aborts on `git status --porcelain | grep '^??'`.

11. **Worktrees, not branch-hopping, for parallel agents.** Each agent
    that needs a different branch gets its own `git worktree add`.
    Top-level Claude never `git checkout`s on the shared tree once
    agents are running. There is already a leftover
    `worktree-agent-a1a17907` ref proving the workflow was tried —
    just be consistent about it.

12. **Stash names must encode purpose, agent, and untracked-or-not.**
    `git stash push -u -m "agent=kaph2 reason=branch-switch untracked=yes"`.
    Free-text "stash before X" is unreviewable an hour later.

13. **Main thread audits `git stash list` before declaring an agent done.**
    Specifically: any stash older than 30 minutes whose message doesn't
    map to a known follow-up commit is treated as lost work and either
    recovered or explicitly trashed.

14. **No `git reset HEAD~N` when other agents are live.** If the main
    thread accidentally stages another agent's work, use
    `git restore --staged <files>` (path-scoped), never a HEAD-moving
    reset. If a commit must be undone, use `git revert`, which leaves
    reflog clean.

15. **Cherry-picks are last-resort, and only across worktrees.** If a
    commit needs to land on two branches, it goes on the merge-base
    branch and both branches merge it. Never `git cherry-pick` to mirror
    a commit that already exists in the graph — it produces duplicate
    SHAs with identical subjects (5 such pairs today) and breaks
    `--ff-only` later.

## Files (absolute paths)

- This scratch doc: `/Users/danbri/working/factoidal/docs/designissues/2026-04-25-tet2-branch-turbulence-retrospective.md`
- Agent discipline rules to amend: `/Users/danbri/.claude/projects/-Users-danbri-working-factoidal/memory/feedback_agent_discipline.md`
- Lost files recoverable from: `stash@{2}^3` (commit d51eb87b2ef31d371bf49e35693a06af938d4857)
- Existing leftover worktree branch: `worktree-agent-a1a17907` → `9499c7e`
