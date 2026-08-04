---
name: workflow-gotchas-debugging
description: Diagnostic playbook for the dev-loop hazards that recur in this repo. Use when a build mysteriously fails, a fresh clone breaks where local works, an agent's work doesn't appear on its branch, the same uncommitted file keeps coming back after `git checkout`, a secondary compile script poisons shared `.cmi`/`.cmx` files, a `set -e` + cleanup trap eats a failing build's log, or "stop hook fires every turn but I'm not done." Twenty hazards total (see "Lessons from 2026-05-07" below): subagent worktree-leakage, concurrent F* extract races, source-without-build-wiring, stale doc numbers, the build-aware stop-hook gap, the `(* *)` comment trap, worktree garbage, secondary-script `.cmx` poisoning, editing build inputs mid-build, cleanup traps eating diagnostics, old-base cherry-picks silently dropping build-list/consumer entries, stale js/npm bundles failing hub cells, old-base agent branches reverting content fixes you just made, `>=` test floors on decreasing metrics breaking on progress, and missing test submodules in worktrees/fresh containers producing lying 0/0 scores and phantom ENOENT failures (fix: tools/ensure-test-env.sh) — plus their detection + recovery steps.
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
