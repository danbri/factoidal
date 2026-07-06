---
name: workflow-gotchas-debugging
description: Diagnostic playbook for the dev-loop hazards that recur in this repo. Use when a build mysteriously fails, a fresh clone breaks where local works, an agent's work doesn't appear on its branch, the same uncommitted file keeps coming back after `git checkout`, a secondary compile script poisons shared `.cmi`/`.cmx` files, a `set -e` + cleanup trap eats a failing build's log, or "stop hook fires every turn but I'm not done." Twelve hazards total (see "Lessons from 2026-05-07" below): subagent worktree-leakage, concurrent F* extract races, source-without-build-wiring, stale doc numbers, the build-aware stop-hook gap, the `(* *)` comment trap, worktree garbage, secondary-script `.cmx` poisoning, editing build inputs mid-build, cleanup traps eating diagnostics, old-base cherry-picks silently dropping build-list/consumer entries, and stale js/npm bundles failing hub cells — plus their detection + recovery steps.
---

# Workflow gotchas + debugging

This skill catalogues the twelve hazards that have actually bitten this
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

## 8. Secondary compile scripts poisoning shared .cmx (2026-07-04)

`build-ocaml-serializer.sh` used to compile its module subset INSIDE
`ocaml-output/`, overwriting `.cmi`/`.cmx` files the main compile
step had produced. Every later `ocamlopt` in that directory
(tests/unit/run-all.sh) then failed with "inconsistent assumptions
over implementation X" until a full recompile. Fix pattern: any
secondary script compiles in a `mktemp -d` scratch copy. Detection:
"inconsistent assumptions" errors right after running a secondary
build script.

## 9. Editing build inputs while a build runs (2026-07-04)

Adding a new module to `build-ocaml.sh`'s lists while
`.build-running` existed poisoned the running cycle: the compile
phase read the updated list, but the already-started extract never
generated the new `.ml`. Rule: treat build-script edits exactly like
running fstar.exe — only while the lock is absent. (Also in
`subagent-prompting`.)

## 10. Diagnostics eaten by cleanup traps (2026-07-04)

A script with `set -e` + a `trap 'rm -rf $SCRATCH' EXIT` that
compiles in $SCRATCH loses the compiler log when compilation fails:
set -e exits before the `cat`, the trap deletes the evidence. Always
capture rc explicitly (`CMD_RC=0; cmd || CMD_RC=$?`, anti-pattern
#14), cat the log, THEN exit on failure.

## 11. Old-base agent commit cherry-picked onto a much newer tip (2026-07-06)

### Symptom

You land a long-running agent's commit by cherry-picking it onto the
current tip. Conflicts look like binaries only; you take `--theirs`,
rebuild, and the build **succeeds** — but the feature isn't actually
there. The runner has no `--crypto` subcommand; the ShExC dispatch
never fires; a hub cell fails with "decode failed". `git log --oneline
-1 -- <the-consumer-file>` shows an *old* commit, not the one you just
picked.

### Root cause

The agent branched hours ago, before several other features landed.
Its commit's changes to shared files are relative to that old base.
Cherry-picked onto the newer tip, git does two silent bad things:

1. **`build-ocaml.sh` module lists auto-merge WRONG.** The agent added
   its module entries; the tip added other features' entries in the
   same list regions. Git's 3-way auto-merge drops a subset of the
   agent's entries with no conflict marker. The dropped module then
   simply isn't extracted/compiled — and the build still exits 0,
   because "module absent from the list" is not an error. The feature
   silently doesn't exist in the binary. (Measured: 12 of 21b5cf0's 27
   VC/HACL `build-ocaml.sh` lines survived the auto-merge; `VC.
   DataIntegrity` never built, yet PIPELINE_RC=0.)
2. **Consumer `.ml` files get the wrong side.** A blanket `git checkout
   --theirs` over the whole conflict set, or an auto-merge that keeps
   "ours", leaves `bin/<consumer>/*.ml` (runners, test drivers) at the
   *tip's* old version, dropping the agent's additions.

### Detection

```bash
# Did the feature's module actually make the build list?
grep -c 'VC_DataIntegrity\|<YourModule>' formal/fstar/build-ocaml.sh
# Compare to what the picked commit intended:
git show <picked-commit>:formal/fstar/build-ocaml.sh | grep -c '<YourModule>'
# Mismatch => auto-merge dropped entries.

# Did the consumer file keep the agent's changes?
git log --oneline -1 -- bin/<consumer>/<file>.ml   # old commit => dropped
grep -c '<feature-marker>' bin/<consumer>/<file>.ml  # 0 => dropped
```

### Recovery / prevention

Do NOT land an old-base agent commit with blanket `--theirs`. Instead:

- **Verify the module list explicitly** after the pick: every module
  the picked commit added must be present in `build-ocaml.sh`, in the
  right dependency position, in the right list (native-only vs the
  js/wasm `FSTAR_MODULES` — e.g. HACL-backed modules are native-only).
  Diff against `git show <commit>:formal/fstar/build-ocaml.sh` and
  hand-add any dropped entry, KEEPING the tip's other-feature entries.
- **Force consumer files that are ancestor-safe supersets.** If the
  tip's version of the file is an ancestor of the picked commit
  (`git merge-base --is-ancestor <tip-file-commit> <picked-commit>`),
  `git checkout <picked-commit> -- <file>` is safe — it's a superset.
  Verify with a marker grep afterward.
- The reliable move for a messy old-base landing is a **dedicated
  landing agent** in a fresh worktree branched from the current tip:
  it cherry-picks, reconciles the module list, forces the consumer
  files, does a full extract+compile+js, and runs every gate — then
  you verify floors + the feature's own gate and push. Cheaper than
  hand-untangling a partial `build-ocaml.sh` merge under time
  pressure, and it keeps the coordinator's context clean.

## 12. Stale js/npm bundle: a hub cell fails on a feature that IS built (2026-07-06)

### Symptom

A new hub post's live cells fail (`node --test tests/hub/postNN` shows
e.g. 6/9), with an error like `decode_shex_schema failed to decode
schemaJson` — the npm API got the new input but ran it through the old
code path. The native binary has the feature; the W3C floors pass; only
the browser/npm cells fail.

### Root cause

Hub cells run against the **js_of_ocaml npm bundle**
(`npm/factoidal/factoidal-npm-entry.js`, copied from
`docs/fstar-extracted/`), not the native binary. A hub page whose cells
depend on an F\* feature needs that bundle rebuilt. But
`build-ocaml.sh js` **incrementally SKIPS the npm-entry sub-bundle**
even when `bin/npm-entry/entry_jsoo.ml` changed (the `changed_modules=0`
footgun, hazard #9's cousin, applied to the js step). The stale bundle
lacks the new dispatch, so the cell runs the old path. A "Built
npm-entry" log line does NOT prove it regenerated.

### Detection

```bash
# Is the docs bundle newer than the js-build start? (mtime, not the log line)
ls -la --time-style=+%H:%M docs/fstar-extracted/factoidal-npm-entry.js
# Is the npm PACKAGE copy in sync with the docs one?
ls -la --time-style=+%H:%M npm/factoidal/factoidal-npm-entry.js
# The real test: run the failing hub cell and read the assertion error.
node --test tests/hub/postNN_test.mjs 2>&1 | grep -A3 'not ok'
```

### Recovery / prevention

- Force the npm-entry rebuild: `touch bin/npm-entry/entry_jsoo.ml
  ocaml-output/<NewModule>.ml` before `./build-ocaml.sh js`, and CONFIRM
  the bundle's mtime advanced (don't trust the log line). If it still
  didn't regenerate, run the js build's npm-entry ocamlfind +
  js_of_ocaml sub-invocation (build-ocaml.sh ~line 1520-1570) directly.
- **Sync the npm package copy**: `npm/factoidal/*.js` are copies of
  `docs/fstar-extracted/*.js`; the npm tests load the copies. If the
  docs bundle is fresh but `npm/factoidal/`'s is older, run the repo's
  established sync step (grep build-ocaml.sh / package scripts) — the
  hub/npm tests use the copies, not the docs originals.
- Whenever a docs landing adds live cells that call a new F\* feature,
  the landing is NOT docs-only — it needs the js/npm bundle rebuilt and
  the `node --test tests/hub/postNN` gate green, or the cells ship
  broken. A hub page whose cell exercises a native-built feature can
  still fail in the browser; the bundle is the thing under test.

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
7. Landed an old-branch agent commit and the feature "isn't there"
   despite a green build? → `grep -c <module> build-ocaml.sh` vs the
   picked commit; check `git log -1 -- bin/<consumer>.ml` (#11).
8. Hub cell fails but the native binary has the feature? → stale
   js/npm bundle; force the npm-entry rebuild + sync the copy (#12).

## What this skill does NOT cover

- The prevention rules themselves (path-discipline preamble,
  post-condition check, build-lock timing, comment-trap wording) —
  `subagent-prompting` owns the text agents must be given; this skill
  owns what to do when those rules were skipped and the hazard fired
  anyway.
- Build lock / `.build-running` marker mechanics in depth —
  `build-and-test`.
- `.checked` cache correctness and safe parallel verification (the
  root cause behind hazard #2) — `fast-verify-extract`.
