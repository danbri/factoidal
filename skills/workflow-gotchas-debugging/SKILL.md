---
name: workflow-gotchas-debugging
description: Diagnostic playbook for the dev-loop hazards that recur in this repo. Use when a build mysteriously fails, a fresh clone breaks where local works, an agent's work doesn't appear on its branch, the same uncommitted file keeps coming back after `git checkout`, a secondary compile script poisons shared `.cmi`/`.cmx` files, a `set -e` + cleanup trap eats a failing build's log, or "stop hook fires every turn but I'm not done." Thirty-three hazards total (see "Lessons from 2026-05-07" below): subagent worktree-leakage, concurrent F* extract races, source-without-build-wiring, stale doc numbers, the build-aware stop-hook gap, the `(* *)` comment trap, worktree garbage, secondary-script `.cmx` poisoning, editing build inputs mid-build, cleanup traps eating diagnostics, old-base cherry-picks silently dropping build-list/consumer entries, stale js/npm bundles failing hub cells, old-base agent branches reverting content fixes you just made, `>=` test floors on decreasing metrics breaking on progress, missing test submodules in worktrees/fresh containers producing lying 0/0 scores and phantom ENOENT failures (fix: tools/ensure-test-env.sh), the node hub harness masking browser-only fn-surface gaps (missing hub.njk wrappers, Turtle-vs-N-Quads convention mismatches), shallow-clone pushes hanging in boundary negotiation (fix: fetch --deepen, not retry loops), and a serializer labelled "display, not wire" whose every consumer was a wire path (silent store data loss, #339/#443) — plus their detection + recovery steps.
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

### Reinforcements from the 2026-07-19 session (many agents, many hours)

- **Leakage is not only edited files — it's UNTRACKED output too.** An agent
  authoring NEW files (e.g. `.github/test-suites/owl-*.yaml`) wrote them into
  the MAIN checkout, so `git status` in main showed untracked files nobody in
  the main session created. Detection: after dispatching an agent, a
  `git status` in main that shows files you didn't touch — tracked OR
  untracked — means leakage. Also seen: the main checkout ended up switched
  ONTO the agent's branch (`git branch --show-current` was the agent's
  branch), which then collided with the agent's own `checkout -b`.
- **The deeper mitigation is COMMIT-FIRST** (`subagent-prompting` Rule 3):
  because the agent pushes its verified source to a branch before doing
  anything else, leakage into main becomes recoverable-by-design — you reset
  main clean (`git checkout -B claude/main origin/claude/main`) and merge the
  agent's pushed branch, rather than salvaging stashes. If an agent is
  actively leaking and you can see its deliverable is essentially done,
  `TaskStop` it and finish the last mechanical step (the commit) yourself
  rather than let it keep contaminating main.
- **Agents WILL kick their own extract/compile despite an explicit
  "do not build" instruction** — recurring, in most long agent runs. Don't
  fight it: commit-first makes the stray build harmless, and you kill it by
  `/proc/<pid>/cwd` match (see `autonomous-time-discipline` §6b), never by
  `pkill -f build-ocaml`.

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

⚠️ **That lock does NOT protect you across worktrees** (2026-08-14). The
lock file lives at `formal/fstar/.build.lock`, and every worktree has its
own copy — so two agents in two worktrees each take *their own* lock,
both proceed, and both write the *shared* `.checked` cache in the opam
switch. The protection you think you have is per-worktree; the resource
being raced is global.

Seen while running a #445 agent and a #362 agent side by side:

```
$ for p in $(pgrep fstar.exe); do readlink /proc/$p/cwd; done
.../worktrees/agent-ae7023ee6a5643cdd/formal/fstar
.../worktrees/agent-ae7023ee6a5643cdd/formal/fstar
.../worktrees/agent-a416c018c10ef24d0/formal/fstar
```

Two agents, three `fstar.exe`, one cache, no lock contention reported by
either.

**The danger is not the wasted cycles — it is the MISDIAGNOSIS.** The race
surfaces as a module failing verification that nobody touched, which reads
exactly like a semantic regression from whatever you just changed. That is
the same presentation as hazard #16 and as issue #444 (a proof sitting
marginally under its rlimit). Before believing such an error: run
`pgrep fstar.exe`, wait for the other processes to clear, and re-verify
that one module serially. Rule out the race before you rule in a
regression.

When dispatching two or more agents that will build, either stagger them,
or say in both briefs that a concurrent agent shares the `.checked` cache
and name the files each one owns — so a content race is caught as well as
a cache race.

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
- ⚠️ **The inverse direction bites harder, and it recurred 2026-08-03:
  ENGINE landings invalidate the bundle.** The bundle went unrebuilt
  from July 21 to August 2 while engine behaviour moved (rdfs4a/4b
  rows, RL comprehension-witness maturation). Consequences arrived all
  at once: an external reviewer's bug report against a month-stale
  bundle (issue #345 — the engine had long been correct), a fixed
  EXISTS bug that STAYED live on the npm surface until the bundle was
  rebuilt, and seven hub cells failing in a single gate when the fresh
  bundle finally met their July expectations. The rule: **rebuild the
  js/npm bundle as part of landing any engine change that alters
  query, parse, or entailment results.** A bundle older than the last
  such landing is not "stale docs" — it is a live behavioural
  divergence shipping to users, and its drift compounds silently until
  someone pays for all of it at once.

## 13. Old-base agent branch OVERLAPS a file you just corrected (2026-07-08)

### Symptom
You land an agent's doc/hub branch by `git checkout <agent-branch> --
<files>`. The build is green, but a correctness fix you committed an hour
earlier has silently vanished — e.g. a doc that said "production runs F\*
`_tok`" is back to the stale "718-line OCaml shadow" wording, or a
de-timestamped intro has "this week" reinstated.

### Root cause
The agent branched BEFORE your fix, so its copy of the shared file is the
pre-fix version. `git checkout <branch> -- file` is wholesale replace,
not merge — it reverts your fix along with taking the agent's intended
change. This is hazard #11's cousin, but for **overlapping content edits**
rather than build-list/consumer drops.

### Detection
Before landing, `git diff origin/claude/main..<agent-branch> -- <file>`
for every file the agent touched that you ALSO touched recently. If the
diff shows your own recent lines being reverted (as `-` on the main side,
stale text as `+`), it's an overlap.

### Recovery / prevention
- Split the agent's files into two sets: (a) files you did NOT touch —
  safe to `git checkout` wholesale; (b) files you DID touch — **3-way
  merge by hand**. For (b), decide which version is the better BASE
  (usually the agent's, if it did more work on that file), take it, then
  **re-apply your fix on top** — the "both, not either" merge. Never pick
  one and lose the other.
- A whole-command `git checkout <branch> -- a b c` is **atomic**: if any
  pathspec doesn't match, it checks out NOTHING and errors. So a stray
  path (e.g. a doc that only exists uncommitted in the worktree) silently
  aborts the entire landing — verify with `git status` after, don't
  assume it took.
- When an agent's base is old, its regenerated BINARIES/bundle are stale
  too (hazards #11/#12) — bring only its SOURCE, rebuild artifacts fresh.

## 14. A `>=` test floor on a DECREASING metric breaks on progress (2026-07-08)

### Symptom
A pinning test fails — `expected >= 151 assume val declarations, found
142` — but nothing regressed; the tree got BETTER.

### Root cause
The test asserted a growth floor (`count >= N`) on a metric that
legitimately shrinks as work lands. `assume val` count goes DOWN every
time a gap migrates to F\* (the whole point). Module/line counts grow;
assume-val, TODO, glue-line, skip counts shrink. A `>=` floor on a
shrinking metric fails on success and trains you to ignore red.

### Detection / prevention
- Before writing a `>=` (or `<=`) assertion on a measured tree count, ask
  which DIRECTION progress moves it. Growth metrics (modules, tests
  passing) take floors; shrink metrics (assume-vals, glue LoC, skips)
  take ceilings or a loose band (`0 < n <= K`), never a growth floor.
- If a doc/test pins a specific number, prefer "on the order of N" prose
  + a self-serve command (`grep -c ...`) over a brittle exact figure —
  the number is a claim about one moment; the tree moves.

## 16. mtime rebuild-skip serves a stale binary after any git touch (2026-07-29)

### Symptom
`./build-ocaml.sh compile` prints `Native binaries already up to date;
skipping ocamlopt rebuild` and `BUILD_STATUS=OK`, and the suite you then
run reports the numbers from BEFORE the change you just landed.

### Cause
`needs_rebuild_from_sources` compares mtimes (`[[ "$src" -nt "$target" ]]`,
build-ocaml.sh:241). This repo COMMITS its binaries (iron rule #9), so any
git operation that materialises one — `merge`, `checkout -- bin/`,
`stash pop`, conflict resolution with `--ours` — stamps it with `now`,
newer than every source. mtime answers "when did this file appear here",
which for a committed artifact is unrelated to "what produced it".

### Detection (do this before trusting ANY measurement after a landing)
Compare source against binary, not source against clock:
```bash
grep -c <marker-from-the-new-source> bin/<consumer>/<consumer>.ml
strings bin/<platform>/<binary> | grep -c <marker>
```
A non-zero count in the source and zero in the binary is the signature.

### Recovery
`touch` the consumer's `.ml`, re-run `./build-ocaml.sh compile`, and
re-check the marker before measuring.

### War stories, both 2026-07-29
- Landing #326: `git checkout -- bin/` (restoring `.cmi` a no-op compile
  had deleted) reverted the merged `owl_runner` with a fresh timestamp.
  `type-consistency` measured 352 pass, 0 fail — the pre-fix number —
  and the agent's correction to 337 pass, 15 fail looked wrong. It
  wasn't; the binary was.
- `factoidal-dump-nq` still emitted mojibake after the #325 parser fix
  (#330). Same shape, different root cause: that binary is not in
  build-ocaml.sh at all.

Tracked as #331. Related: hazard #11 (old-base cherry-picks dropping
build-list entries) — same family, different trigger.

## 15. Missing test submodules: worktrees + fresh containers silently lose fixtures (2026-07-09)

### Symptom
Three disguises of one cause: (a) a dashboard row reads **0 pass / 0
fail** (SHACL/ShEx shipped that way publicly); (b) a runner reports "0
tests" and a naive reader logs it as a pass; (c) hub/npm tests fail
with ENOENT on fixture paths and the failures get misread as engine
regressions (post09/13/18 all did this to multiple agents in one day).

### Root cause
Test fixtures live in 14 `third_party/testing/*` git submodules.
`git worktree add` populates NONE of them, and a fresh container
populates none until something inits them. The old bootstrap only
initialised two (w3c, rdf-canon) — every other suite depended on luck.
Each worktree subagent then improvised (hand-init, copying from the
main checkout), wasting tokens and occasionally shipping stale-fixture
results.

### Detection / recovery / prevention
- **`tools/ensure-test-env.sh`** is the single source of truth: inits
  all testing submodules (idempotent, worktree-safe — resolves the
  checkout via `git rev-parse --show-toplevel`) and verifies a
  per-suite sentinel path, printing a labelled table naming what each
  gap breaks. `--check` verifies without network. Exit 1 = do NOT
  trust any suite score from that checkout.
- The SessionStart hook runs it on the main checkout; **worktrees must
  run it themselves** — every worktree-subagent brief includes it as
  step 0 (see `subagent-prompting`).
- Before diagnosing any 0/0 row, "0 tests" run, or fixture-ENOENT test
  failure: run `tools/ensure-test-env.sh --check` FIRST. If it exits 1,
  the score is an environment artifact, not an engine result.

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

## Hazard 16: extract manifest-hash skip is dependency-blind

Found 2026-07-17 during the RDF 1.2 term-model landing. `build-ocaml.sh
extract` skips modules whose OWN .fst/.fsti digest is unchanged — it
does not track dependencies. After a foundational change (e.g. a new
`rdf_term` constructor in `RDF.Term.fsti`), consumers whose source is
untouched keep their stale extracted `.ml` and are silently NOT
re-verified: the phase-1 agent measured 142 stale `.ml` files hiding
unverified consumers. Detection: a foundational-type change that
compiles suspiciously fast. Recovery/rule: any change to a widely-
imported type (RDF.Term, RDF.Triple, core algebra types) MUST rebuild
with `./build-ocaml.sh extract --force-full` (all modules re-verified,
0 skipped) before compile. Targeted extracts remain fine for leaf-module
edits.

## Hazard #17 — `pgrep -f <script>` matches your OWN shell, so a dead job reads as RUNNING

2026-07-31. A W3C gate battery died silently ~3.5 hours before anyone
noticed, because every liveness check was

```bash
pgrep -f "w3c-tests.sh" >/dev/null && echo RUNNING || echo STOPPED
```

`pgrep -f` matches against the full command line of every process — and
the checking shell's own command line **contains the string
`w3c-tests.sh`**. So the check matches itself and can never report
STOPPED. A `Monitor` armed with the same idiom in its death-branch
inherits the bug and never fires.

The tell, when it finally showed: `ps -o etimes=` on the "found" PID
returned `0` — a process that has been running for zero seconds is the
grep, not the job.

**Detect liveness by the artifact advancing, not by process name.**

```bash
AGE=$(( $(date +%s) - $(date -r "$LOG" +%s) ))
[ "$AGE" -gt 3000 ] && echo "STALLED OR DEAD after $(grep -c '^  done\.' "$LOG") suites"
```

A log that has not been written in N minutes is stalled or dead, and the
answer is the same either way. This also catches the case a process check
never can: a job still resident but wedged.

If a process check is genuinely wanted, match the *binary* rather than
the script name (`pgrep -f "bin/linux-x86_64/owl_runner"`), and confirm
with `ps -o etimes=` that the elapsed time is plausible.

⚠️ Related: the same run showed that launching three verification agents
while a gate battery runs is enough contention to kill the battery. The
previous gate passed the same suite cleanly. Stagger heavy work, or
expect to re-run the gate.

### Hazard #17 addendum — the same self-match DEADLOCKS a wait loop (2026-08-14)

Hazard #17 was written about a check that reads RUNNING forever. The
same bug in a *wait* loop is worse: it never returns at all.

```bash
# Waits forever. The loop's own shell command line contains
# "build-ocaml.sh", so pgrep always finds it and the negation is
# never true.
until ! pgrep -f "build-ocaml.sh" > /dev/null; do sleep 20; done
```

Two such waiters were armed on 2026-08-14 during the #443 fix. Both hung,
and the second one carried the follow-on `extract compile` in its `&&`
chain, so the next build never started either — a silent stall, not an
error. It surfaced only when `pgrep -af` was run with the full command
lines visible and the waiters appeared in their own results.

**Wait on a PID, not on a name.** `kill -0 <pid>` cannot match itself:

```bash
while kill -0 "$BUILD_PID" 2>/dev/null; do sleep 20; done
```

Better still for a long build: launch it with `run_in_background: true`
so the harness reports its exit code, and do not write a waiter at all.

## Hazard #18 — the container can be recycled mid-session, and an uncommitted edit can silently un-happen

Observed 2026-08-02. A source edit (`SPARQL11.Store.fst`, applied by a
python heredoc whose uniqueness assertion passed, then verified clean by
F\*) was later found reverted on disk to the committed content, with a
fresh mtime. The commit that was supposed to carry it listed the file in
`git add`, succeeded, and silently contained everything EXCEPT that file
— `git add` on a clean file is a no-op, so nothing failed. The stale
binary then reproduced the very bug the edit fixed, which is the only
reason anyone noticed.

Forensics after the fact, on the machine itself:

* `uptime -s` showed the CURRENT VM had **booted 183 seconds ago** —
  the session had just been recycled again, invisibly, between two
  turns. Recycles are routine, not exceptional.
* The workspace survives recycles (untracked `.claude-runs/` logs from
  hours earlier persisted; tracked files kept their original mtimes —
  no wholesale re-clone).
* The loss was SELECTIVE: another file edited five minutes earlier in
  the same working session kept its uncommitted edit and made it into
  the commit. The one file reverted carried a restore-time mtime.
* In-flight background builds spanning the event completed with clean,
  continuous logs — consistent with the harness restarting them on the
  new VM.

The exact restore mechanism is underdetermined by what survives a
recycle (the process-level evidence dies with the old VM). The best
supported story: session state is restored from a point-in-time
snapshot, and an edit made after the last snapshot but before the
recycle is the casualty. Do not spend hours on the forensics; the
countermeasure is total regardless of mechanism:

1. **Commit and push IMMEDIATELY after any material source edit** —
   before verification, before builds, before anything long-running.
   A pushed commit survives every recycle variant; an uncommitted edit
   survives none of the bad ones. Amend later if needed.
2. **Never trust "the commit succeeded" as proof the edit is in it.**
   `git show --stat HEAD` after committing; a listed-but-clean file
   vanishes from the commit without any error.
3. **Bracket builds with a content check** on the files the build must
   see: `sha256sum` the edited source before kicking the build and
   verify it again from the build script's last line. A build that read
   a reverted source produces a plausible, wrong artifact.
4. **After any rebuild that carries a fix, re-run the reproducer**
   against the fresh artifact. The revert above was caught exactly this
   way, and no other check would have caught it.
5. **Long-running jobs must stay harness-tracked, or a recycle kills
   them silently and permanently.** 2026-08-04: a full gate launched
   with shell `&` inside an already-completed background wrapper died
   with a mid-run recycle and nothing restarted it -- the harness only
   re-arms jobs it is tracking (`run_in_background: true` on the
   command itself). Detection was hazard-#17 style (no runner process,
   artifact mtime 20+ minutes old, boot time four minutes ago). Never
   `&`-detach anything that matters; give the harness the whole
   command.

## Hazard #19 — a cleanup step that can silently no-op is a lie (the five-week dead purge)

Found 2026-08-03. `build-ocaml.sh`'s stale-artifact purge —
`rm -f "$OUTDIR"/*.cmi ...` — had been a **silent no-op since a
2026-07-29 refactor** moved it inside the rebuild branch, which sits
below a `cd "$OUTDIR"`. From there the glob expanded to
`ocaml-output/ocaml-output/*.cmi`, matched nothing, and `rm -f` said
nothing. Every build for five weeks linked against whatever stale
artifacts were lying around; the visible symptom was two
`inconsistent assumptions over interface Factoidal_serve` link
failures, each read at first as a one-off and cleaned by hand.

Two lessons, distinct:

1. **After moving code within a shell script, re-verify every relative
   path against the cwd AT THE NEW LOCATION.** A `cd` anywhere above
   the moved block changes what its globs mean, and `rm -f` converts
   the mistake into silence. This is the same species as hazard #10
   (cleanup traps eating diagnostics): cleanup code fails quieter than
   any other code.
2. **The mechanism had two halves, and cleaning the visible one did
   not fix it.** Deleting the `ocaml-output` duplicates cured one
   build; the next failed the same way, because ocamlopt also reuses
   CONSUMER-dir `.cmx` files (`bin/factoidal-cli/`,
   `bin/factoidal-serve/`, …) whose `.ml` did not change — and after
   any extract that moves a shared interface those disagree with the
   freshly compiled modules at link time. A recurring "one-off" is a
   mechanism you have not fully found: the second occurrence is the
   tell, and the fix is complete only when it covers the path that
   produced BOTH failures. Fixed in the purge itself (bare globs +
   consumer-dir sweep, failure reported not swallowed).

## Hazard #20 — a suite score certifies only the path the runner exercises

2026-08-02: 631 of 631 W3C SPARQL stayed green while `FILTER EXISTS`
dropped **every row** on the CLI, npm, and HTTP entry points. The
runner evaluates through `eval_select_query` (pure algebra path); the
user-facing entries evaluate through `SPARQL11.Store`'s backend path,
which had the bug. Two evaluation paths, one certificate, and the
uncertified one is the one users run.

The rule that follows: **every user-facing entry point carries its own
regression pins** under `tests/local/cli_*.sh` — currently
`cli_exists_regressions.sh`, `cli_owlrl_witness_strip.sh`,
`cli_sr1_sr2_regressions.sh` — and any new divergence-class fix adds
its case THROUGH THE CLI BINARY, not through the runner. When quoting
a suite score, know which path it certifies; "631 of 631" was true and
useless for the bug that mattered. Full statement of the discipline:
`skills/test-suites/SKILL.md` § "A suite score certifies only the
evaluated path".

## Hazard #21 — a score line in a build log certifies the build's own CWD, not the suite (the phantom RIF regression)

2026-08-06: an engine-restructure landing was followed by the full
gate batch, whose log showed the SPARQL suite at 627 pass, 4 fail
(out of 631) against a 631 pass, 0 fail baseline — all four failures
RIF entailment-regime tests, "expected 1 row, got 0". A regression
investigation followed: old-vs-new binary comparison, fixture
archaeology, submodule history. The binary was innocent. The
score line came from `build-ocaml.sh` Step 3, which ran
`w3c_runner --all` from `formal/fstar/` — and the runner's RIF
dispatch (`rif_rules_path_for`, `bin/w3c-runner/w3c_runner.ml`)
resolves `third_party/testing/rif/tc/` relative to CWD. From
`formal/fstar/` those four tests false-fail on EVERY full build;
from the repo root everything passes. `generate-report.sh` had a
comment saying exactly this ("Always run from repo root so the
runner's relative third_party/ paths resolve") — the self-test
step never got the same treatment. Fixed 2026-08-06: Step 3 now
cds to the repo root (see the comment at the invocation).

Costs and rules:

1. **Before investigating any cross-build score delta, re-run the
   suite by hand from the documented CWD** — one minute — before
   binary archaeology — hours. A diff in scores between two runs is
   only meaningful if the runs' environments match; CWD is part of
   the environment for any runner with relative fixture paths.
2. **A first comparison that reproduces the failure IDENTICALLY on
   the old artifact is a hint the harness, not the artifact, is the
   variable.** Here the old binary "failed" too — from the wrong
   directory. That result was initially read as "environmental,
   fixture missing" when it was really "my reproduction inherited
   the same wrong CWD".
3. **When a script warns about a path-resolution requirement, grep
   for the OTHER invocations of the same binary** — the fix that
   added the warning probably missed one. The warning and the bug
   coexisted in sibling scripts for months.
4. Background bash jobs die when the session suspends (hazard #18's
   sibling): the batch's REAL suite run never executed, its log
   truncated mid-self-test at the exact moment the container idled,
   and the partial `latest.csv` it left behind had to be reverted.
   Treat a background job's missing final RC echo as "the script
   did not finish", never as "the tail got cut off".

## Hazard #22 — the node hub harness binds `fn` to the NODE package, so browser-only fn-surface gaps ship green (2026-08-07/08)

### Symptom

A hub post's `node --test tests/hub/postNN` suite is fully green, the
merge gate passes, the post deploys — and the owner reports live cells
broken on the deployed page. Two shapes, both shipped on post 32:

1. **Loud**: `TypeError: fn.rhoDfFragmentCheck is not a function` — the
   cell REJECTS in the browser (2026-08-07).
2. **Silent, worse**: every cell resolves, no rejection anywhere, but
   the theorem-backed ASK prints `false` where the prose promises
   `true` (2026-08-08). The browser wrapper passed raw Turtle to an ABI
   whose parser is N-Quads-only; the parse silently dropped every
   prefixed statement, the certified closure closed the EMPTY graph
   with `ok: true`, and the fragment checker answered `fragment: true`
   VACUOUSLY on that empty graph. The same sweep found post 28's
   `fn.sigmoidFormulaMathml` / `fn.sigmoidPoints` missing entirely.

### Root cause

The reactive node harness (`runReactivePost`) binds `fn` to the node
npm package (`npm/factoidal/index.js`), whose api.js normalises every
input to N-Quads before calling the ABI. The browser page binds `fn`
to the hand-curated wrapper object in `docs/_includes/hub.njk`, backed
by `npm/factoidal/browser.js` (served as `docs/npm/factoidal/browser.js`).
Those are two different surfaces: a name can exist on one and not the
other, and a calling convention (input format) can differ between
them. Node tests certify only the node surface.

### Detection / prevention

- `tests/hub/fn_surface_parity_test.mjs` — text-level pin, runs in the
  normal hub suite: every `fn.<name>(` in every published post must
  have an `async <name>(` wrapper in hub.njk, and same-name
  `Factoidal.*` delegations must be browser.js exports. Catches shape
  1 cheaply.
- `tests/web-demos/hub_browser_all.sh` — headless-Chromium sweep of
  every post; catches rejected cells (shape 1) in a real browser.
  **Run it before publishing any new hub post.** Post 32 shipped
  broken precisely because this existing harness was not run.
- `tests/web-demos/hub_post32_value_check.sh` — VALUE-level browser
  assertions (the ASK cell prints `true`, derivedTriples > 1000).
  Only this class catches shape 2: a wrapper that exists but silently
  computes over nothing. When a post's cells make a checkable claim
  in prose ("// true — and that true is the theorem"), pin the VALUE
  in a browser check, not just the absence of rejections.
- When adding a NEW fn wrapper to hub.njk: check the browser adapter
  function's input contract against what page cells actually pass
  (`owlClosure` takes N-Quads; page cells hold Turtle — convert in
  the wrapper). "ok: true with empty output" is the silent-drop
  signature (#344's class) — treat empty engine output on non-empty
  input as a bug until proven otherwise.

## Hazard #23 — a SHALLOW clone's push hangs in negotiation, mimicking network failure (2026-08-09)

### Symptom

`git push` hangs for minutes and dies at any timeout you give it, while
`git ls-remote` answers instantly and small fetches work. Retry loops
with backoff burn hours (this cost most of a working day across ~10
attempts: two live-page fixes and the RDFS-Plus batch all queued behind
it). Occasionally a push DOES get through (small pack, recent base),
which makes it look like network flakiness. It is not the network.

### Root cause

The remote-execution container clones shallow (and treeless:
`[tree:0]`). A push from a shallow clone advertises `shallow` boundary
commits and the server must compute reachability across that boundary;
with enough boundary commits (ours listed dozens) the negotiiation
stalls indefinitely. Pack SIZE is irrelevant — a 2.7MB pack that
builds locally in 3 seconds hung the same way a binary-laden one did.
Diagnose with `GIT_TRACE_PACKET=1 timeout 45 git push ... 2>&1 |
tail`: if the last lines are `git> shallow <sha>` rows and a server
`shallow` response with no pack writing after, it is this hazard.

### Fix / prevention

- `git fetch --deepen=100 origin <default-branch>` (took ~1 minute),
  then push — the same push that hung for 570s completed instantly.
  Deepen more if it recurs as history grows past the boundary.
- Diagnose BEFORE retrying: one `GIT_TRACE_PACKET` run beats ten
  blind retries with exponential backoff. "Retry with backoff" is
  for transient transport errors; a DETERMINISTIC hang retries
  forever at full cost.
- `http.version HTTP/1.1` + `http.postBuffer` did nothing here (they
  fix proxy-killed streaming uploads, a different failure with the
  same surface symptom). Applying them first wasted a cycle; the
  packet trace distinguishes the two in under a minute.

### Addendum (same day): the recurrence trigger is post-merge branch deletion

GitHub auto-deletes the work branch on every PR merge, so the next
push RE-CREATES it — full negotiation from zero against a shallow
clone, and the hang returns even after a deepen. The reliable
pre-push sequence after any merge: `git fetch origin <default-branch>`
(the merged history gives the negotiation common ground), delete the
stale remote-tracking ref (`git update-ref -d refs/remotes/origin/
<branch>` — it breaks `--force-with-lease` and confuses status), then
push. With that sequence the same push that hung for 570 seconds
completes in under five.

## Hazard #24: subagent transcript mtime is not a liveness signal (2026-08-11)

The orchestrator watched three freshly dispatched subagents for ~4
hours because their transcript files' mtimes kept updating to "now"
every check. All three had in fact died during setup at 09:01 — the
LAST ENTRY inside each transcript was 4 hours old while the file
mtime stayed current (the harness touches the files). Cost: ~4 hours
of wall clock with an empty pipeline, across three heartbeat cycles
that each "confirmed" liveness from mtime.

Rules:
1. NEVER conclude a subagent is alive from its transcript file's
   mtime. Parse the transcript and read the LAST ENTRY's `timestamp`
   field (`tail -1 ... | python3 -c 'json.loads(...)["timestamp"]'`).
2. A dispatched proof/build agent that has pushed NOTHING to its
   branch after ~60-90 minutes deserves a last-entry-timestamp check
   even if a coarser signal says it is active.
3. Dispatch briefs must order agents to push a first commit EARLY
   (setup done, or first sub-result) — a dead agent with zero commits
   is indistinguishable from a slow one until you parse its
   transcript.
4. Cap cache-restore/setup time in briefs (~10 min) — all three
   deaths happened during .checked-cache copying; a cold verify of
   one target module beats an expensive copy that a container event
   can kill.

### Hazard #24 addendum — "COMMIT-FIRST" must mean a DEADLINE, not an ordering (2026-08-11)

Second loss the same day, worse than the first. The #334 Turtle agent ran
~7 hours (250k tokens, 167 tool calls), reported a working fix and repeated
extract/compile/suite cycles — and committed NOTHING. When it died, its
worktree was clean: the fix was gone, unrecoverable. Its brief did say
"COMMIT-FIRST", but as an ORDERING ("commit before building"), which the
agent satisfied vacuously by never reaching a build it considered final.

Rule: every dispatch brief states a WALL-CLOCK deadline for the first
commit — "commit and push whatever verifies within 15 minutes of starting,
even a partial edit with the test still failing" — and repeats it for each
subsequent milestone. An agent that has been running an hour with no branch
on origin is failing regardless of what its narration says; check the branch,
not the narration (that check is hazard #24's first rule).

Corollary for the orchestrator: when a long-running agent's first push has
not appeared, SendMessage it a direct "push what you have now" before its
next build cycle, rather than waiting for its report.

## Hazard #25 — a serializer labelled "display, not wire" whose every consumer is a wire path (2026-08-14)

`RDF.Pretty.term_to_ntriples` rendered an N-Triples term without escaping
the literal's lexical form. That was deliberate, documented in two module
banners, and defended as a division of labour: RDF.NQuads.Serialize is the
byte-correct wire serializer, RDF.Pretty is display.

Nobody checked who was calling it. All three consumers were wire paths:

| consumer | what it produces | consequence |
|---|---|---|
| `factoidal --dump` | N-Triples that tools re-read | our own parser rejected our own output (#339) |
| COTTAS store object column | a cell re-parsed on read | `import` -> `query` DESTROYED every literal containing `"`, LF or `\` (#443) |
| npm-entry jsoo store writer | same cell | same, in the browser build |

The `--dump` half was found in July, filed as #339, pinned as an XFAIL,
and read for two weeks as a cosmetic defect — "dump-nq and dump-turtle are
correct; this is one function carrying a second, weaker notion". Correct
as far as it went, and it stopped one call site short of the store. Three
of six literal classes were being silently destroyed on the way to disk the
whole time.

Rules:

1. **A "display-only" claim is a claim about consumers, so enumerate
   them.** `grep` for every call site before accepting the label. In this
   repo the ratio was three wire consumers to zero display consumers.
2. **Two functions rendering the same syntax will diverge.** The fix was
   to DELETE the second one, not to make it escape — making it escape
   would have produced a byte-identical copy under a second name, which is
   how the two drifted in the first place. One notion of how a literal is
   written, in the module that holds the round-trip proofs.
3. **A term-level round-trip theorem says nothing about which term
   function a consumer picked.** `RDF.NTriples.RoundTrip.fst` was sound
   throughout; it just did not cover the function the CLI called. Proof
   coverage is a property of the wiring, not only of the statement — this
   is the same trust-surface shape as the vacuity findings (#333, #429).
4. **When triaging a known defect, ask what else calls the broken
   function** before classifying it as cosmetic. #339's scope table listed
   the other *serializers* and concluded "one function, not a systemic
   gap". The missing column was the other *callers*.

Standing pin: `tests/local/cli_literal_escape_roundtrip.sh` — six literal
classes across the `--dump` and store paths, with an anti-vacuity arm that
corrupts the dump the exact way the bug did and requires the pin to go red.

## Hazard #26 — a batching edit script reports success for edits it discarded (2026-08-23)

**Symptom.** A `python3` heredoc makes five edits to one file, prints
`ok` after each, exits 0. The build that follows is green. The
measurement that follows is taken. The commit message describes five
fixes. Three of them are not in the file.

**Mechanism.** The script reads the file once, applies every
replacement to the string IN MEMORY, and writes at the END:

```python
s = open(p).read()
s = s.replace(a1, b1, 1); print("ok")     # in memory only
assert a2 in s; s = s.replace(a2, b2, 1)  # <-- raises here
open(p, 'w').write(s)                     # never reached
```

An `AssertionError` on ANY later replacement discards every earlier
one — after the progress lines have already been printed. Nothing
distinguishes this from success: the file still parses, the build
still passes, and the suite still runs.

**Cost, 2026-08-23.** The Lean OWL wave-2 commit claimed five
performance fixes. Three were absent (the threaded search budget,
the `labelsOf` lookup, the hoisted per-axiom label reads); a sixth
item was defined and never called. The measurement taken against
that build said the fixes "bought nothing", and that conclusion went
into `PORT_NOTES.md`, the parity ledger and a GitHub issue as a
methodology lesson about premature optimisation. With the edits
ACTUALLY applied the same suite went from 26 m 34 s to 4 m 30 s — a
5.9× speedup — and the score went UP by one case. The wrong lesson
had to be retracted from three documents.

**Rules.**

1. **Write after each replacement, or verify the write.** One
   `open(p,'w').write(s)` per edit, or a final `assert b1 in
   open(p).read()` per claim.
2. **A green build is not evidence that an edit landed.** The
   unchanged file also builds. This is anti-pattern #27's family:
   the tooling reports success for work that did not happen.
3. **`grep -c` the file for every claim before writing it into a
   commit message.** Five claims, five greps, under a minute. It
   would have caught all three.
4. **A measurement is a measurement OF A BUILD.** If an edit was not
   verified to land, the number that follows is about the old code.
   Re-measure.

**Related.** Hazard #18 (a container recycle silently un-happens an
uncommitted edit) and anti-pattern #27 (a landing drops module-list
entries; the build exits 0 and the feature is not built) are the same
shape: success reported for work that did not happen.

## Hazard #27 — a hand-built guard proves a rule CORRECT and says nothing about whether it FIRES (2026-08-23)

**Symptom.** A new engine rule is written, a `#guard` is built by
hand to exercise it, the guard passes, the rule is landed. The corpus
score does not move by a single case.

**Cost, 2026-08-23.** The Lean OWL ≤-rule (identify two successors of
a node over its cardinality bound) was implemented by REWRITING
EDGES: redirect every tableau-internal edge mentioning the absorbed
node. A hand-built graph reproducing `WebOnt-description-logic-003`
refuted correctly. On the corpus the rule fired zero times, because
the `--dl` regime runs a materialisation pass FIRST and that pass
writes its own existential witnesses INTO the graph — where an edge
cannot be rewritten at all. Every successor that mattered came from
there.

**Rule.** A synthetic input built from the rule's own preconditions
tests the rule's LOGIC. It cannot test whether the real pipeline ever
presents those preconditions. For a rule meant to move a suite score,
the guard is necessary and the SCORE is the evidence — and if the
score does not move, instrument whether the rule fired at all before
assuming it is merely incomplete.

This is `skills/measuring-inference`'s "synthetic shapes lie about
real vocabularies", in the place it is least expected: not the data,
the PIPELINE. The upstream stage had changed the shape of the input
the rule was written against.

## Hazard #28 — an audit that finds nothing is evidence about the AUDIT first (2026-08-23)

**What happened.** `tools/lean-port-gap.py` measures how much of the F\*
tree the Lean 4 port covers, by matching F\* module names against Lean
module names. One false negative turned up by hand: `DID.Key` had been
covered by `L4Factoidal/VC/DidKey.lean` all along and the alias table
did not know.

So I audited the rest — by squashed MODULE NAME. It found nothing more.
I wrote, in the gap document and in a GitHub comment: "An audit of the
whole not-covered list found no other false negative."

**What was actually true.** Four more modules were already covered,
1,298 F\* lines:

| F\* module | Lines | Actually covered by |
|---|---|---|
| `RDF.Entailment.Simple` | 182 | `L4Factoidal/RDF/Entailment.lean` |
| `RDF.Entailment.Regime` | 271 | the same file |
| `Parser.CSVResults` | 610 | `L4Factoidal/SPARQL/ResultsCsvTsv.lean` |
| `RDF.Pretty` | 235 | — |

The reported coverage was 120 of 220. The real figure was 125 of 220.
The gap document, the PORT_NOTES sections and a GitHub status comment
all carried the wrong number for the length of the session.

**Why the method could not have worked.** Module-name matching cannot
see two things, and both were present:

1. **A consolidation.** One Lean module covers simple entailment AND
   the D / RDF / RDFS regimes, which the F\* tree splits across two
   files. No name relates `RDF.Entailment.Simple` to `RDF.Entailment`
   more strongly than it relates a dozen unrelated modules.
2. **A rename that changes more than punctuation.** `Parser.CSVResults`
   became `SPARQL.ResultsCsvTsv`. Squashing case and dots does not
   bridge that.

The audit was silent about exactly the two failure modes it was
structurally blind to, and I read its silence as coverage.

**What found them.** Comparing DEFINITION NAMES rather than module
names: every `let` / `val` / `type` of each not-covered F\* module
against every `def` / `abbrev` / `structure` / `inductive` / `theorem`
in the Lean tree, normalised for case and underscores, ranked by the
fraction of the F\* module's definitions that have a Lean counterpart.
`RDF.Entailment.Simple` scores low on that test too (the Lean names are
`termMatch` and `matchSubject` where F\* has `match_term` and
`match_subj`) — it was caught by reading the Lean module's own header,
which says in its first sentence which two things it covers.

### The rules

1. **An audit that finds nothing is a claim about the audit's REACH
   before it is a claim about the code.** Say what the method can and
   cannot see, next to the result. "Checked by squashed module name;
   this cannot detect consolidations or substantive renames" would have
   made the residual risk visible instead of silently absorbed.
2. **Pick a method that can see the failure you are looking for.** The
   question was "is this module's CONTENT present somewhere in the Lean
   tree". Module names are a proxy for that and a weak one. Definition
   names are closer. The module's own header is closer still, and it is
   what actually settled it.
3. **A correction to a measurement is not done when the number is
   fixed.** The wrong number had already been written into a design doc,
   PORT_NOTES and a GitHub comment. All three need the correction, and
   the correction needs to say what the old claim was — otherwise the
   next reader cannot tell which of the two numbers they are looking at.
4. Same family as hazard #26 (a green build is not evidence an edit
   landed) and hazard #27 (a passing guard is not evidence a rule
   fires). In all three, a check produced a reassuring result while
   being structurally incapable of detecting the thing it was trusted
   for.

## Hazard #29 — a theorem that assumes its own conclusion type-checks fine (2026-08-23)

**What happened.** Porting `RDF.CottasStore.PresenceWriter` to Lean put
the `.presence` WRITER and the `.presence` READER in one tree as pure
functions of a `ByteArray`. Both trees' soundness lemma for the
row-group prune holds only GIVEN `BuiltCorrectly` — the on-disk bitmap
agrees with the ground truth — and neither tree proves that premise,
because in the F\* tree the writer is OCaml.

So the port ended with a theorem, under a section heading reading "the
producer-side obligation, closed":

```lean
theorem buildPresence_correct …
    (hagree : ∀ rg tok, rg < numRgs → tok < numTokens →
                rgContainsToken h rg tok = occurs rg tok) :
    BuiltCorrectly h occurs
```

It type-checked. It is worthless. `BuiltCorrectly h occurs` unfolds to
`∀ rg tok, rg < h.header.numRgs → tok < h.header.numTokens →
rgContainsToken h rg tok = occurs rg tok`, and two other hypotheses said
`h.header.numRgs = numRgs` and `h.header.numTokens = numTokens`. The
hypothesis IS the conclusion with its bounds re-indexed. The proof body
was `exact hagree …`.

**What it would have cost.** The commit message, the design doc and a
`PORT_NOTES` section would all have said an open proof obligation was
discharged. Anyone later reading "the producer-side obligation is
closed" would have stopped looking for the real proof. The reader's own
`rgContainsToken_sound` would then have appeared to rest on a proved
premise when it rests on nothing.

**How it was caught.** By re-reading the statement against the
definition of `BuiltCorrectly` before writing the commit message — not
by the type checker, which was perfectly happy, and not by any test.

### The rules

1. **A hypothesis that restates the conclusion is not a hypothesis.**
   Before claiming a theorem discharges an obligation, unfold the
   conclusion and check no premise contains it. `Prop`-valued
   definitions make this easy to miss, because the two read differently
   at the source level while being the same statement.
2. **The proof body is the tell.** `exact h` for some hypothesis `h`,
   where the theorem claims to establish something substantive, means
   the work is in the hypothesis and the caller has to supply it.
3. **Delete it; do not weaken it.** A theorem that assumes its
   conclusion is worse than no theorem, because it makes prose claim the
   obligation is met. What replaced it here is a paragraph naming what
   would actually close the gap (a bit-packing lemma over a `UInt8` fold
   of `|||`) and what is established instead (computational evidence at
   four shapes, including two that cross byte boundaries).
4. **State the difference the port DID make, separately from the one it
   did not.** Here: the proof is now POSSIBLE — both sides are pure
   functions in one tree instead of split across an OCaml writer — and
   it is not done. Those are two different sentences and collapsing them
   is what produced the bad theorem in the first place.
5. Same family as hazard #24's vacuous theorems (unsatisfiable
   hypotheses), #26 (a green build is not evidence an edit landed), #27
   (a passing guard is not evidence a rule fires), #28 (an audit that
   finds nothing is evidence about the audit) and #30 (a tool that
   reads a cached input reports the cache). In all of them a check
   returned a reassuring result while being structurally incapable of
   detecting what it was trusted for.

## Hazard #30 — a measurement tool that reads a cached input reports the cache, not the tree (2026-08-23)

`tools/lean-port-gap.py` answers one question: which F\* modules have a
Lean counterpart. It read both module lists from two text files in the
session scratchpad.

The F\* list stayed right, because `formal/fstar/` had not changed. The
Lean list was a snapshot taken earlier in the session, so the tool
reported a module as NOT COVERED minutes after its Lean file landed in
the tree. The number the tool exists to produce was wrong, and nothing
in its output said the input was old.

The second failure mode is worse and had not fired yet: the scratchpad
directory is per-session and is deleted with the container, so on a
fresh session the tool would have crashed, or — if someone recreated
the files from an older checkout — reported an older answer with no
warning.

### The rule

**A measurement tool derives its inputs from the repository on every
run.** If a tool needs a list of files, it walks for them. A cached
input is acceptable only when the tool verifies the cache is current
and fails loudly when it is not.

Two supporting habits:

- **Fail on an empty walk.** `lean-port-gap.py` now exits non-zero if
  either walk returns zero modules. A wrong working directory then
  produces an error rather than "0 of 0 covered".
- **Write reports to a temp path, not the repository root**, unless the
  report is a tracked artefact. A generated file that lands in the tree
  turns up in the next `git status` and gets committed by accident.

This is the same family as hazards #25, #26, #27, #28 and #29: a check
returned a reassuring result while being structurally unable to detect
what it was trusted for. Here the check was arithmetic over a list, and
the list was the stale part.

## Hazard #31 — a name-similarity heuristic silently inflates a coverage count (2026-08-23)

`tools/lean-port-gap.py` decided that an F\* module had a Lean
counterpart if an explicit alias matched, OR if the last name component
matched, OR if the last two matched. The bare last-component rule is
the problem.

Adding `L4Factoidal/HDT/Store.lean` made `SPARQL11.Store` — 1,452 lines,
not ported, not close to ported — disappear from the not-covered list,
because both names end in `Store`. The count went UP by two when one
module landed, and the second increment was a module that had not been
touched.

Auditing the rest found fourteen modules resting on a bare-leaf match.
Seven were wrong: `SPARQL11.Store` ← `HDT.Store`, `RIF.Core.Tests` ←
any of fifteen `*.Tests` modules, `RDF.Store.Loader` ←
`JSONLD.Loader`, `Math.Expr` ← `SPARQL.Expr`, `SPARQL.Protocol.Client`
← `HTTP.Client`, and two `*.Serialize` modules ← `JSON.Serialize`.

The count had been over by five for the whole session before this
landing, and the heuristic predates it.

### The worse half: a broken alias hidden by the heuristic

Two aliases pointed at `RDF.Serialize`, a Lean module that DOES NOT
EXIST. The alias silently did nothing, the leaf rule matched
`JSON.Serialize` instead, and both modules counted as covered. A lookup
table whose misses are absorbed by a fallback cannot report its own
breakage.

### The rules

1. **Coverage is an explicit decision, not a name resemblance.** Only
   an alias, or a match on the last TWO name components, counts. A
   bare last-component match is a suggestion to audit, never a result.
2. **A lookup miss must be loud.** The tool now prints every alias
   whose target module is absent, before the report. A silent
   fallback behind a table is how a broken entry survives.
3. **A count that moves without a cause is a bug report.** One module
   landed and the number rose by two. That is the signal; chase it
   before writing the number down.
4. **Audit by reading the target's own header.** Each alias kept after
   this audit was verified against the Lean module's own "Port of
   `formal/fstar/<X>.fst`" line, or — for the three RIF modules, which
   carry no such line — by subject matter, which is the weaker
   evidence class and is labelled as such in the table.

This is the third measurement defect in this tool in one day (hazards
#28, #30, #31). All three shared a shape: the tool answered, the answer
looked reasonable, and nothing in the output said which evidence it
rested on.

---

## Hazard #32 — two sessions in ONE worktree: `git commit -a` absorbs the other session's in-flight edits (2026-08-24)

### Symptom

An agent finished a change, verified it, then ran `git status` to stage
its own commit and got **`nothing to commit, working tree clean`** — with
its edits present in the files. `git log -- <the changed file>` named a
commit about an unrelated subject, authored minutes earlier. The agent
had no commit of its own to report.

### Root cause

Two agent sessions were running against the SAME container and the SAME
checkout of `claude/autoexec-scratchpad-assess-37oeok`. The other session
was landing Lean work every ten minutes, some of it with a whole-tree
`git commit -a`. Every such commit swept up whatever the first session
had written so far.

Measured on 2026-08-24: one F-star change and its glue patch and its two
doc edits were split across three commits belonging to a Lean porting
session — `2a2d50ddee2`, `3d9b9c47188`, `c4ff99d94e5` — none of whose
messages mention the on-disk store.

Two costs, and the second is the larger one:

1. The change has no commit of its own, so its message, its rationale and
   its score line are absent from history. A later `git log --oneline`
   cannot find it, and a bisect blames a Lean parser commit for an F-star
   backend change.
2. **A `-a` commit can capture a half-written edit.** The absorbing
   commit lands whatever is on disk at that second, verified or not. A
   session that has changed three files out of five and is still editing
   gets its middle state committed, and the branch carries source that
   nothing has type-checked.

### Detection

- `git status` reports clean when you know you have unstaged work.
- `git log -1 --format=%ad --date=iso` shows a commit minutes old that
  you did not make.
- `git log --oneline -S '<an identifier you just introduced>' -- <file>`
  names someone else's commit.
- `git reflog` shows commits interleaved with your own timeline.

### The rules

1. **Check for a co-tenant BEFORE the first edit.** `git log -1
   --date=iso` at session start, and again before committing. A commit
   timestamp inside your own session window that you did not author means
   you are sharing the checkout.
2. **Share a branch, never a working directory.** A second session in the
   same container works in its own `git worktree`. This is the same rule
   `skills/subagent-prompting` already applies to subagents; it applies
   to sibling sessions for the same reason.
3. **Never `git commit -a` in a shared checkout** — stage the paths you
   changed by name. `-a` is a claim that every modified file in the tree
   is yours, and in a shared checkout that claim is false.
4. **Report what actually happened.** If your work landed inside another
   session's commit, say so and give that SHA. Do not synthesise a commit
   that "represents" the change, and do not report a SHA that does not
   contain it.

## Hazard #33 — an annotated-but-uncited semantics default plus zero suite pressure: two engines shipped opposite unexercised behaviors, and the first proof contact blamed the wrong layer (2026-08-25)

### Symptom

The unified-semantics program's D-entailment stage found the Lean
executable and the Lean model theory disagreeing on RDF 1.2 graphs
whose only ill-typed literal sits inside a triple term. The
disagreement was machine-checked (`dEntailsMt_tt_gap`), filed as
[https://github.com/danbri/factoidal/issues/602](https://github.com/danbri/factoidal/issues/602),
and attributed to the EXECUTABLE ("the collector must not treat
triple-term-interior literals as asserted"). The attribution was
wrong: the current RDF 1.2 Semantics Working Draft (7 April 2026, §5
`I(E) = IT(I(E.s), I(E.p), I(E.o))` composed with §7.1) and the W3C
rdf12 `malformed-literal` test ("Malformed literals are allowed in
triple terms, but cause inconsistency") side with the executable. The
defective layer was the totalized model theory, whose exclusion clause
was top-level-only.

### Root cause — three layers, none sufficient alone

1. **A semantics default annotated but not cited.** `Term.literals`
   was born (2026-08-22) recursing through `tripleTerm`, with a
   docstring saying so — a typed decision, but naming no
   specification clause. Its top-level-only counterparts
   (`hasRangeClash`, F\* `has_ill_formed_recognized_literal`,
   `hasIllFormedRecognizedLiteral` in a SECOND Lean module) each made
   the OPPOSITE choice through catch-all `_` arms. One tree carried
   both polarities of the same check, silently.
2. **The term type was one spec version ahead of the semantics
   modules' cited anchor.** Every fold over `Term` was written against
   an RDF 1.2-shaped type while the semantics modules cited RDF 1.1
   Semantics §7, which has no triple-term clause — so each fold
   contained a decision its cited spec could not answer, and each fold
   decided independently.
3. **Zero test pressure, itself layered.** The one suite that decides
   the question (rdf12 `rdf-semantics`) never loaded in the Lean
   harness — an upstream manifest defect (undeclared `test:` prefix)
   met a strict manifest parse, so every umbrella run reported
   0 pass, 0 fail (out of 0) with `no_manifest=1`; and the F\* runner
   skips that suite's `mf:result false` inconsistency verdicts
   entirely. Between 2026-08-22 and 2026-08-25 NOTHING exercised any
   of the folds' interior polarity.

Cost: a wrong fix direction stood in an open issue with owner
visibility; the model-theory defect was pinned in-source as a theorem
whose name (`_gap`) blamed the executable; one session-day of repair
work had to start by re-deciding the spec anchor. Full post-mortem:
the investigation comment on
[https://github.com/danbri/factoidal/issues/602](https://github.com/danbri/factoidal/issues/602).

### The rules

1. **A semantics default in a fold over a syntax type MUST name the
   specification clause that licenses it** — in the arm or the
   docstring. "Annotated" is not "anchored": the interior recursion
   WAS documented, and still carried no authority a reviewer could
   check. If the cited spec has no clause for a constructor (the type
   is a spec version ahead), that absence goes in the docstring and
   into an issue — it is a decision nobody has made yet.
2. **No catch-all `_` arms over a semantics-bearing inductive in a
   verdict fold.** Write every constructor. The compiler then flags
   every fold when the type grows, and reviewers see each polarity as
   a decision instead of an omission. (Applied 2026-08-25:
   `Term.mentionedLiterals` / `assertedLiterals` are the canonical
   collector pair in `RDF/Entailment.lean`, all four constructors
   explicit, each collector citing its WD clause; every
   D-inconsistency check routes through them by name.)
3. **A suite that reports `0 out of 0` is not a suite.** `no_manifest`
   / `zero_tests` diagnostics existed and were printed for two months;
   nothing escalated them. Treat a persistent zero-denominator suite
   as a broken gate, not as background noise — the F\* runner's
   lenient-with-report manifest policy
   ([https://github.com/danbri/factoidal/issues/334](https://github.com/danbri/factoidal/issues/334))
   is now in the Lean harness too (`parseManifestTextLenient`,
   `MANIFEST-RECOVERY` warning lines).
4. **A machine-checked divergence names TWO suspects.** A theorem that
   pins "layer A disagrees with layer B" proves neither side correct;
   which layer must move is a spec-anchor decision to make FIRST,
   against the current specification text and its test suite, before
   any repair — and before the theorem gets a name. `dEntailsMt_tt_gap`
   type-checked while blaming the wrong side; the repaired tree states
   the same separation as `topLevel_exclusion_insufficient_for_tt`,
   named for the superseded variant it refutes.
5. The F\* side of the same defect family (opaque scan + missing
   rdf12 inconsistency path) is tracked in
   [https://github.com/danbri/factoidal/issues/604](https://github.com/danbri/factoidal/issues/604)
   — out of scope of the Lean repair, referenced here so the polarity
   decision is not re-made independently a third time.

## Hazard #34 — an absorbed `.ml` is a mid-build artifact: the sweep unpatched the shipping engine (2026-08-26)

### Symptom

`npm-publish.yml` run 1 — the workflow's first ever run — failed its
extraction drift check: 8 files changed, 2736 insertions, 213 deletions
between the committed `formal/fstar/ocaml-output/*.ml` and a fresh
extraction of the same commit. `git status` had been clean the whole
time. No test score had moved. No build had failed.

### Root cause

The same two commits as hazard #32 (`2a2d50ddee2`, `3d9b9c47188`, both
titled "Lean N-Quads: ...", both 2026-08-24), plus `6e6f7171ce9` the
same day. Hazard #32 records what the absorbed session LOST. This
records what the absorbing commits GAINED.

The files they swept in were extraction output captured between
`fstar.exe --codegen OCaml` and `./ocaml-patches.sh`. Extraction writes
the `.ml`; the patch step then realises every `assume val` into it. A
`.ml` read off disk between those two calls is a real file, compiles,
and is missing every glue realisation.

What the shipping engine lost for two days: the whole COTTAS on-disk
companion chain (`Cottas_offset_idx`, `Cottas_compound_po_writer`,
`Cottas_subject_offset_idx`, the token-lookup dictionary realisation,
the page-cache decoders), the `SPARQL11_Algebra` extension-function
registry, the Parquet footer runtime glue, and `SHACL_Validation`'s
`sh:sparql` dispatch marker. `bin/linux-x86_64/factoidal` was rebuilt
from that state at 20:46 the same evening and committed.

Nothing detected it. `git status` cannot: the files are tracked and the
commit is clean. The build cannot: unpatched extraction output compiles.
`check-extraction.yml` could not: it ran `extract` + `compile` and never
diffed the result against the committed `.ml`, so it checked that
extraction succeeds, not that the committed output matches it — and it
triggered on `pull_request` only, while all three commits were direct
pushes.

### Detection

- `./ocaml-patches.sh <a copy of ocaml-output>` — run the patch step
  alone against a copy of the committed `.ml`. Anything it CHANGES is a
  patch the committed output is missing. This needs no `fstar.exe` and
  runs in about one second; it is the fastest way to separate patch
  drift from extraction drift.
- `grep -c '<marker>' ocaml-output/<M>.ml` for a marker string a patch
  script inserts. Every patch here has one, for its own idempotency
  test.
- `git log --format='%h %ad' --date=short -- ocaml-output/<M>.ml` against
  the date the patch landed. A `.ml` regenerated AFTER a patch, without
  the patch's marker, was committed without the patch step.

### The rules

1. **A `.ml` under `ocaml-output/` is only committable straight after a
   COMPLETE `./build-ocaml.sh extract`.** Extraction alone leaves the
   tree in a state that compiles and is wrong. Never commit `.ml` from a
   checkout where the extract step was interrupted, or where only
   `fstar.exe` was run by hand.
2. **Stage extraction output by explicit path, never `git add -A` / `git
   commit -a`.** Hazard #32 gives the same rule for the shared-checkout
   case; this is the reason it holds even in a checkout you believe is
   yours alone.
3. **A commit whose subject names one tree must not carry files from
   another.** Three Lean-titled commits carried an F\* backend refactor
   and its build artifacts. If `git status` shows files from a
   workstream your message does not describe, they belong in their own
   commit or in `git stash`, not in yours.
4. **A CI job named "Check X" must diff X, not merely run it.** See
   anti-pattern #28. `check-extraction.yml` now runs
   `extract --force-full` and fails on `git diff --exit-code` against
   `ocaml-output/*.ml`, on push as well as pull_request.
5. **`build-ocaml.sh extract --force-full` was a no-op from 2026-08-15
   to 2026-08-26** — the multi-step argument loop read `--force-full` as
   a step name. If you are reading a log from that window that claims a
   full re-extraction, it did not happen. Full write-up:
   [`docs/designissues/2026-08-26-extraction-drift-root-cause.md`](../../docs/designissues/2026-08-26-extraction-drift-root-cause.md).

## Hazard #35 — a routing change on a path no suite exercises: FILTER NOT EXISTS answered zero rows for a day (2026-09-02)

### Symptom

`tools/w3c-persisted-census.sh` reported 0 eligible tests instead of 535.
Its manifest-extraction query, run through the `l4factoidal` CLI, uses
`FILTER NOT EXISTS { ?a qt:graphData ?g }` and returned no rows. The same
query through the browser module (`datasetQuery`) also returned no rows.
Every gate was green: `lake build` (909 jobs), `Wasm/native-smoke.sh`
(61 pass), the hub suite (408 pass), CI's Lean corpus check.

### Root cause

Commit b8061bead (the same morning) routed SELECT/ASK in
`Wasm/Ops/Query.lean` through the physical-plan runners
(`runSelectQueryBackendDataset`) for the speed-up on hub post 50. The
reference evaluator sets `env.dataset` itself before evaluating (§18.6:
EXISTS evaluates against the query's dataset); the backend runners read it
from the environment the caller supplies, and the caller supplied
`{ base, ext }`. `substituteExistentials` then left the EXISTS pattern in
place and `ebvOrFalse` dropped every row. The persisted harness `finish`
had the same latent gap with `emptyEnv`.

No suite covered the path: the Lean W3C runner (`l4w3c`) evaluates on the
reference path, `native-smoke.sh` had no EXISTS query, and no hub cell uses
EXISTS. The change was gated by suites that could not see the failure
(anti-pattern #28).

### Detection

Cheapest signal, in order: the census script's eligible count (it is
already a FILTER NOT EXISTS query over the W3C manifests); the two
`queryDataset FILTER (NOT) EXISTS` checks in `Wasm/native-smoke.sh`; the
`#guard`s at the end of `L4Factoidal/SPARQL/StoreDataset.lean`;
`tests/hub/l4_exists_regression_test.mjs` against the committed module.

### The rules

1. **Any change that moves a query shape from the reference evaluator to
   a backend runner must be gated by a query that only the reference
   semantics decide.** EXISTS / NOT EXISTS, MINUS with shared variables,
   OPTIONAL with a filter, and sub-SELECT are the shapes; put one of each
   in the smoke for the path you changed, not in a suite that does not
   run through it.
2. **A backend runner needs `env.dataset`.** `runSelectQueryBackendDataset`
   and `runAskQueryBackendDataset` do not set it; every caller must (the
   WASM op passes the parsed dataset; the persisted harness passes the
   base-plus-delta graph it answers from).
3. **Run `tools/w3c-persisted-census.sh` after any change under
   `Wasm/Ops/Query.lean`, `SPARQL/StoreDataset.lean` or the harness query
   CLI.** It takes about 20 s when broken and a few minutes when working;
   an eligible count below 535 is a failure, whatever the rest says.
4. **The census doc pins a tip.** `docs/20260901-persisted-executability-census.md`
   records the commit it measured; re-measure before quoting it against a
   newer tip.

## Hazard #36 — worktree agents filled the disk and every tool call failed (2026-09-03)

### Symptom

Every `Bash` call, including `df -h`, returned
`ENOSPC: no space left on device` while trying to create the harness's own
output file. The session could not read the disk to find out what filled
it, could not delete anything, and could not report. Agents already running
kept writing.

### Root cause

Each `isolation: "worktree"` agent copies the Lean build cache into its
worktree so its builds are incremental (`rsync -a
formal/lean4/.lake/ <worktree>/formal/lean4/.lake/`). One worktree costs
1.5 to 2.8 GB. Seven were live at once, five of them for agents that had
already reported and been landed; nothing removed them. Free space went from
comfortable to 2.4 GB to zero while three more agents were dispatched.

### The rules

1. **Check free space before dispatching a worktree agent.** `df -h /`. If
   free space is under about 10 GB, land or remove a worktree first.
2. **Remove the worktree in the same turn you land the commit.**
   `git worktree remove -f -f <path>` then `git branch -D <branch>` then
   `git worktree prune`. Do not leave it for later; later is when the disk
   fills.
3. **Cap concurrent worktree agents at three.** That is a disk and CPU
   limit, not a style preference: more than three concurrent Lean builds
   also makes every timing measurement on this machine meaningless
   (`docs/20260902-persisted-query-ladder.md`, the machine-stall caveat).
4. **Before deleting a worktree, check it for unlanded commits**:
   `git -C <path> log --oneline origin/claude/main..HEAD`. On 2026-09-03 a
   deletion sweep found `docs/designissues/2026-08-23-spec-coverage-ledger.md`,
   301 lines written twelve days earlier by an agent whose branch was never
   landed. It was rescued by cherry-pick (`d99beb10f`). Anything else in
   that worktree would have gone silently.
5. **Recovery, when every command already fails:** stop background agents
   with `TaskStop` first (that tool needs no disk), which frees their output
   files, then delete worktrees. Do not try to diagnose first — the
   diagnosis command is itself what cannot run.

## Hazard #37 — a measurement tool that cannot run on the developer's platform reports silence, and silence reads as success (2026-09-03)

### Symptom

`tools/lean-shacl-scores.sh` printed its table with `?` in every Lean
cell and exited 0. Nothing in the output said the tool had failed. An
audit needing SHACL figures had to run the probe binaries by hand and
transcribe the numbers.

### Root cause

Two defects, and the second is the one that matters.

1. The script parsed the probe's `TOTAL` line with `grep -oP`. `-P`
   (Perl-compatible regular expressions) is a GNU grep extension. BSD
   grep, which is the `grep` on macOS, rejects it. Every extraction
   produced an empty string.
2. The script had `|| echo "?"` on each extraction and a header saying
   "Always exits 0 — this reports, it does not gate". So a tool that
   measured NOTHING exited the same way as a tool that measured
   everything.

Anti-pattern 30 already required a measurement tool to derive its
inputs from the repository on every run. This is the other half of the
same rule: it must also SAY when it walked nothing.

### Detection

Run every measurement tool once on the platform the developer actually
uses, and check the exit code, not only the output. `echo $?` after
each. A tool whose only failure signal is a `?` in a column has no
failure signal.

### The rules

1. **Every measurement tool exits non-zero on an empty walk.** No rows,
   no files, no parsable output — exit 1 with a message naming what it
   could not find. Reporting and gating are different jobs; a tool may
   decline to gate on the SCORES and still must gate on having
   measured them.
2. **No GNU-only flags in a tool a developer runs locally.** `grep -P`,
   `sed -i` without an argument, `readlink -f`, `date -d`. Use
   `grep -E`, `sed -E`, or `python3`. The macOS versions of these tools
   are BSD.
3. **A placeholder is not a result.** `?`, `n/a`, `0/0` and an empty
   cell must each come with a non-zero exit or a line on stderr naming
   the cause. A number that is missing is not a zero and not a pass.
4. **Run the tool on this machine before quoting it.** The corrected
   script reports SHACL 1.0 core 98 pass, 0 fail (out of 98); SHACL 1.2
   core 103 pass, 30 fail (out of 133); SHACL 1.2 sparql 22 pass, 3
   fail (out of 25); SHACL 1.2 node-expr 140 pass, 0 fail (out of 142);
   SHACL 1.2 rules 88 pass, 0 fail (out of 88).

### The same class, in a second tool the same day

`tools/lean-hygiene-audit.py` was written to fail the Lean CI gate on a
`sorry`, a user `axiom`, `native_decide`, `unsafe`,
`@[implemented_by]`, or an increase in the `partial def` count. Its
first run reported one `sorry` and 184 `partial def` against a measured
217. Both figures were wrong: the tool's comment-and-string stripper
treated the Lean character literal `'"'` (in `escapeChar '"'`) as the
opening of a string, and blanked the next two hundred lines of real
code. A tool that under-reports looks like good news; check a new
counting tool against a figure you already trust, and investigate a
disagreement in EITHER direction before believing the tool. Corrected,
it reports 0 and 217, which matches.

A raw `grep -c 'partial def'` over the same tree returns 227. Ten of
those are prose — this project writes "no `sorry`, no `axiom`, no
`native_decide`, no `partial`" as a header comment on nearly every
file. Strip comments and string literals before counting anything in
Lean source.
