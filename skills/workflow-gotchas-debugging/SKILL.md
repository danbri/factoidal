---
name: workflow-gotchas-debugging
description: Diagnostic playbook for the dev-loop hazards that recur in this repo. Use when a build mysteriously fails, a fresh clone breaks where local works, an agent's work doesn't appear on its branch, the same uncommitted file keeps coming back after `git checkout`, or "stop hook fires every turn but I'm not done." These are the seven hazards we've actually hit (see "Lessons from 2026-05-07" below) plus their detection + recovery steps.
---

# Workflow gotchas + debugging

This skill catalogues the seven hazards that have actually bitten this
project in production. Each section lists symptoms, root cause, the
recovery procedure, and (where applicable) the prevention now in place.

## 1. Subagent worktree-leakage

### Symptom

You spawn a subagent with `isolation: "worktree"`. Later you see
uncommitted changes in your **main** worktree (`/home/user/factoidal/`)
that you didn't make. Or your branch silently switches to one the agent
created. Or the same file (`Parser.RIFXML.fst`, `w3c_runner.ml`) keeps
coming back after you `git checkout` it.

### Root cause

Subagents have their own working directory (`$WORKTREE_PATH`), but if
the prompt context contains absolute paths to the main worktree
(`/home/user/factoidal/formal/fstar/...`), the agent uses those paths
directly with the `Edit`/`Write` tools and writes to the **main
worktree**, bypassing isolation entirely.

The agent's own worktree stays clean; nothing pushes from there. The
edits live in your main worktree, and `git status` shows them as
yours.

### Detection

```bash
# In main worktree:
git status -s | head
# Files you didn't touch will appear modified.

# Compare to agent worktree:
diff -q /home/user/factoidal/formal/fstar/<file> \
        /home/user/factoidal/.claude/worktrees/agent-<id>/formal/fstar/<file>
# If they differ AND the agent's copy matches origin, the agent edited
# your main, not its own.

# Spot the branch swap:
git branch --show-current
# If it's not the branch you started on, an agent ran `git checkout` here.
```

### Recovery

```bash
# Stash the leaked changes with a clear label so you can recover them later
git stash push -m "agent-leakage-<topic>" path/to/affected/files

# If branch was swapped, checkout the right one:
git checkout claude/<your-branch>

# Recover the agent's intended work later:
git stash list                    # find the stash
git stash show -p stash@{N}        # inspect
# Then either: cherry-pick onto the agent's branch, or git apply
# inside the agent's worktree.
```

### Prevention

The `subagent-prompting` skill mandates a path-discipline preamble.
Every agent prompt now includes:

> Your worktree is at `$WORKTREE_PATH`. Use ONLY paths under that root.
> Before any `Edit`/`Write`, verify `pwd` matches your worktree. If you
> see paths like `/home/user/factoidal/...` in this prompt, translate
> them to `$WORKTREE_PATH/...` first.

Plus a post-condition check the agent runs before pushing.

## 2. Concurrent F\* extracts racing the cache

### Symptom

`./build-ocaml.sh extract` hangs / dies midway. fstar.exe processes show
up in `ps` from multiple worktrees. Modules that should be `(up to date)`
get re-extracted in a fresh order. Compile fails with "Unbound module"
errors that don't make sense.

### Root cause

Different worktrees have separate `.ml` outputs but **share** the F\*
opam switch's `.checked.lax` hint cache. Concurrent fstar.exe runs
invalidate each other's cache entries; one process's `.checked` is
written while another reads it; downstream cache misses cascade.

### Detection

```bash
ps aux | grep "fstar.exe" | grep -v grep
# More than one fstar.exe = hazard.

ps aux | grep "build-ocaml.sh extract" | grep -v grep
# More than one extract loop = race.
```

### Recovery

```bash
# Pick the right one to keep, kill the others:
pkill -f "build-ocaml.sh extract"
# Wait, then run the extract serially.
```

### Prevention

`build-ocaml.sh` opens a `flock` on `.build.lock` at entry. Concurrent
invocations exit immediately with "another build in flight." See the
`build-and-test` skill for the lock semantics.

## 3. Source-without-build-wiring

### Symptom

A PR adds a new `.fst` module. F\* verifies it. The PR merges. Days
later, on a fresh clone, `./build-ocaml.sh compile` fails with
"Unbound module FooBar". Local builds were green only because the
`.cmx` was cached from before.

### Root cause

`build-ocaml.sh` has the F\* module list in **three** places:

- The `for fst in ... ; do` extract loop (around line 226)
- `COMMON_MODULES="..."` for native compile (around line 331)
- `FSTAR_MODULES=( ... )` for js_of_ocaml (around line 635)

It's easy to add a module to one and forget the others. PR #224 added
`RDF.List.Helpers.fst` source without updating any of the three;
SPARQL11_Algebra references `RDF_List_Helpers.assoc_tr` and the build
breaks. Same pattern hit `RIF.Core.Eval.fst` earlier.

### Detection

```bash
# After landing a new .fst, verify it appears in all three places:
grep -c "<NewModule>.fst" formal/fstar/build-ocaml.sh   # should be >= 1
grep -c "<NewModule>.ml"  formal/fstar/build-ocaml.sh   # should be >= 2
```

CI gate: build-ocaml.sh `compile` runs on every PR head, not just
post-merge on `claude/main`.

### Recovery

Add the module to all three lists. Re-extract + recompile.

### Prevention (planned)

Single source of truth: `formal/fstar/modules.txt`, sourced into
build-ocaml.sh. Each section reads from the same file. No more
3-place divergence.

## 4. Stale documentation numbers

### Symptom

`docs/designissues/2026-05-07-tableau-audit.md` cites
"51 pass / 70 total" for the entailment suite. Actual current score
is 69/70 — but the audit doc says 51/70 and triages "this is the
queue."

### Root cause

Test scores in design docs are written once and never refreshed. PRs
that improve scores don't update every doc that mentions the old
number.

### Detection

CI lint planned: scrape `\d+ pass / \d+ total` patterns from
`docs/designissues/*` and `docs/claude-rules/*`. Compare to
`docs/test-results/latest.json`. Flag mismatches in PR diff.

### Recovery

Update the affected docs with current numbers. Do this when you
notice a stale number — don't defer.

## 5. Build-aware stop-hook needed

### Symptom

A long-running build is in flight (extract takes 10-15 minutes).
Every turn-end the stop hook complains "uncommitted changes" because
the build is rewriting `.ml` files. User sees noise; assistant feels
pressure to commit partial state.

### Root cause

`~/.claude/stop-hook-git-check.sh` doesn't know about builds.

### Recovery

Don't commit partial extracted state. Wait for the build to finish.

### Prevention (planned)

`build-ocaml.sh` writes `.build-running` on entry, removes on exit /
trap. Stop hook checks for the marker and skips the warning when
present.

## 6. The `(* *)` F\* comment trap

### Symptom

F\* reports a syntax error hundreds of lines after the actual offender.
The reported line looks fine.

### Root cause

F\* block comments `(* ... *)` **nest**. Any `*)` inside a comment
prematurely closes it; any `(*` opens a new level. Common offenders:
ARQ-style notation containing `construct(*)`, COUNT(*) snippets in
explanatory comments.

### Detection

```bash
# After a syntax error, scan for problem patterns:
grep -nE '(\(\*|\*\))' <file>.fst | head -50
# Look for `*)` inside a comment, or unbalanced `(*`.
```

### Recovery

Reword to avoid `(*` / `*)` inside comments, or switch to `//` line
comments.

### Prevention

CLAUDE.md DANGER section. The `fstar-env` skill repeats the warning.

## 7. Worktree garbage accumulation

### Symptom

`.claude/worktrees/` has 33+ entries, most locked, some pointing at
branches that were merged weeks ago. `git worktree list` is enormous.
Disk usage drifts upward.

### Detection

```bash
git worktree list | wc -l    # Should be << 10 normally.
ls .claude/worktrees | wc -l  # Same expectation.
```

### Recovery

```bash
# Audit which worktrees are still relevant:
git worktree list
# For each agent-* worktree where the agent is finished:
git worktree remove --force <path>
git branch -D <branch>   # only if pushed + merged
git worktree prune
```

### Prevention (planned)

Daily `git worktree prune --expire 1.day.ago` plus a CI sweep that
deletes worktrees whose agent-id appears in the completed-agents
ledger.

## Lessons from 2026-05-07

This skill is the durable form of a single bad session:

- A 10-minute extract turned into 90 minutes because of #1 + #2
  (worktree leakage + concurrent races) compounding.
- PR #228 had to be force-pushed multiple times because the source
  files I committed kept getting reverted by leaked agent edits.
- "Stop hook fires every turn" pushed me toward partial commits;
  resisting that pressure was correct.
- The actual drift fix turned out to be just a build-script wiring
  issue + a patch script issue — the .ml drift wasn't real because
  main's .ml files compiled fine under the new F\* version. Title
  / scope creep in the PR was a leftover from an incorrect initial
  diagnosis.

## Quick checklist when something feels wrong

1. `git status -s` in main worktree — uncommitted files you didn't
   touch? → suspect agent leakage (#1).
2. `ps aux | grep fstar.exe | grep -v grep` — multiple? → race (#2).
3. `git branch --show-current` — wrong branch? → agent swap (#1).
4. New `.fst` in recent merges? → grep build-ocaml.sh for it (#3).
5. Build-running flag set? → wait, don't commit partial.
6. Doc number that "doesn't match what I just measured"? → stale (#4).
