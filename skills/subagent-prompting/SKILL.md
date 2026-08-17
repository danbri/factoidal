---
name: subagent-prompting
description: How to write subagent prompts for the Factoidal repo so the agent's work actually lands cleanly. Use whenever you dispatch a subagent with the Agent tool, especially with `isolation: "worktree"`. Three load-bearing rules. (1) Path discipline — agents must use only paths under their worktree, not absolute paths from your prompt context. (2) Post-condition checks — agent must verify its main-worktree footprint is zero before reporting back. (3) COMMIT-FIRST — an F* agent's deliverable is VERIFIED SOURCE, not a binary; the agent pushes the verified `.fst` to a branch the moment it verifies clean, BEFORE building, so stalls / container recycles / stray self-builds are non-events and the orchestrator merges+builds+gates. Also carries MANDATORY brief inclusions for build-list edits (only while `.build-running` is absent), the F*/OCaml comment-nesting trap, and iron rule #11 (no hand-editing extracted `.ml`) — plus the one-agent-one-commit and ship-code-sketches rules. Pairs with workflow-gotchas-debugging (which catalogues recovery steps when these rules are violated).
---

# Subagent prompting for Factoidal

This repo runs many parallel subagents, each in its own git worktree
under `.claude/worktrees/agent-<id>/`. The Agent tool's `isolation:
"worktree"` setting is supposed to keep their work isolated — but the
isolation can be silently bypassed if the agent uses absolute paths
from your prompt instead of paths under its own worktree.

When that happens, the agent's edits land in your **main** worktree,
not in its isolated copy. Your `git status` shows uncommitted changes
you didn't make. The agent's branch has nothing to push. Recovery
takes 10-30 minutes per incident.

This skill exists because we hit this hazard 3+ times in one session
(2026-05-07; see `skills/workflow-gotchas-debugging/SKILL.md` for the
full incident report).

## The two rules every agent prompt must include

### Rule 1 — path discipline preamble

Every agent prompt MUST start with this block (copy-paste, then fill in
the worktree path placeholder if you know it; the agent figures it out
from `pwd` if you don't):

```
## Path discipline (MANDATORY)

Your worktree is at $WORKTREE_PATH (run `pwd` to confirm). All file
operations — Read, Edit, Write, Bash commands — MUST use paths under
that root.

If this prompt mentions paths like `/home/user/factoidal/formal/...`,
those refer to the MAIN worktree. Translate them to your worktree by
substituting the prefix:

  /home/user/factoidal/<rest>
  → $WORKTREE_PATH/<rest>

Do NOT edit files under /home/user/factoidal/ directly. That is a
different working tree; your edits will not appear on your branch and
will pollute the main tree's git status.

Verify before each Edit/Write:
  - `pwd` returns a path under $WORKTREE_PATH
  - The file path you're about to edit also starts with $WORKTREE_PATH

If you find yourself about to use an absolute path that doesn't start
with $WORKTREE_PATH, STOP and translate it.
```

### Rule 2 — post-condition self-check before pushing

## Rule 3 — COMMIT-FIRST: push VERIFIED source before building (load-bearing)

The single highest-leverage agent-orchestration discipline, learned over
~25 agent dispatches in one multi-day session. **An F\* agent's deliverable
is VERIFIED SOURCE, not a built binary.** Full builds take 15-25 min;
agents routinely stall, get killed by container recycles, or (despite
explicit instructions) kick their own long build and then dead-wait on a
completion event that never reaches them. Every one of those is a total
loss IF the verified source is still sitting uncommitted in the agent's
worktree.

The fix makes all of it a non-event. Every F\*-editing agent brief MUST say:

> The MOMENT your F\* source verifies clean (`fstar.exe --z3version 4.13.3
> --cache_checked_modules <Module>.fst`, no `--lax`/admits), IMMEDIATELY
> `git checkout -b <branch>`, commit the verified `.fst`, and
> `git push -u origin <branch>` — BEFORE attempting any build, and before
> anything else. Then, if you find a further verified improvement, commit
> and push it too. Never sit on verified source.

Then the orchestrator — not the agent — merges the branch into main,
builds ONCE under the disciplined-build recipe (see
`autonomous-time-discipline`), and gates. Consequences that follow:

- An agent killed mid-build loses nothing — its verified source is on
  origin. You salvage by merging the branch, not by reconstructing work.
- "The agent kicked its own build again" stops mattering — kill the stray
  worktree build (by `/proc/<pid>/cwd` matching the worktree, never by
  name) and build in main yourself. Agents WILL do this; plan for it
  rather than fighting it.
- ALWAYS check the returned worktree for a 2nd/3rd uncommitted verified
  fix the agent made after its commit-first push (`git -C <worktree>
  status` filtered to `*.fst`); commit+push it to capture full value.
- The agent's F\* verify is the gate for LANDING the source; your build +
  suite run is the gate for MEASURING it. Keep the two separate.

## Step 0 in every worktree brief (MANDATORY): restore test fixtures

`git worktree add` populates ZERO of the 14 `third_party/testing/*`
submodules, so a fresh agent worktree cannot run most suites — scores
read 0/0 and hub/npm tests fail with fixture ENOENT that agents misread
as engine regressions (hazard #15 in `workflow-gotchas-debugging`).
Every worktree-agent brief must include, before any build or test step:

    tools/ensure-test-env.sh    # idempotent: inits all testing
                                # submodules + verifies per-suite
                                # sentinels; exit 1 = scores will lie

If the worktree is offline and init fails, the fallback is copying the
named fixture dirs from the main checkout — but the agent must say so
in its report; never present a result from a checkout where the script
exits 1.

## Iteration-loop briefs (MANDATORY): ship the fast loop, not the full pipeline

Any brief whose task is an edit-verify-test **loop** (suite burn-down,
proof repair, feature with fixture iteration) MUST include the fast-loop
recipe from [fast-verify-extract](../fast-verify-extract/SKILL.md) and
this rule: **iterate with targeted verify + targeted extract +
`./ocaml-patches.sh` + linking ONLY the binary under test; run the full
`./build-ocaml.sh extract && compile` exactly once, on the final pass,
before floors + commit.** `compile` relinks all ~23 binaries (~700 s
measured 2026-07-10) because shared modules front every binary — paying
that per iteration turns a 2-3 min loop into a 15 min loop and a
2-hour task into an all-day one. Learned the slow way on the JSON-LD
compact dispatch (2026-07-10): the dispatcher read the skill when
writing it, then briefed an agent without it. The brief is where the
knowledge has to live — agents don't browse skills they weren't
pointed at.

## Feature-landing briefs (MANDATORY): the obsolescence sweep

Any brief that lands new capability or moves a score MUST instruct the
agent, before its single commit: run
`tools/obsolescence-sweep.sh <feature keywords>` and correct every
statement the landing falsifies (docs, hub posts, skills, .fst header
comments, `.github/test-suites/*.yaml` gap lists, ledger, dashboard
prose) in the same commit. Full procedure + lexicon:
[obsolescence-sweep](../obsolescence-sweep/SKILL.md). Born of
2026-07-10: three stale "we don't have X" claims shipped on the public
dashboard while X sat in the tree.

Every agent prompt MUST end with this block:

```
## Before you push (MANDATORY post-condition check)

After your final commit but BEFORE running `git push`, run this check:

  cd $WORKTREE_PATH && git status -s
  # Expected: empty. Anything here means a commit was missed.

  cd /home/user/factoidal && git status -s
  # Expected: empty (or unchanged from your start). Anything here that
  # you don't recognise from the parent session means you leaked into
  # the main worktree.

If the second check shows files YOU edited, you have leaked. Recovery:
  1. Stash them in MAIN (not your worktree):
     cd /home/user/factoidal && git stash push -m "agent-<your-id>-leakage" <files>
  2. In your worktree, copy the stashed content via:
     git -C /home/user/factoidal stash show -p stash@{0} | git apply
  3. Re-commit in your worktree.
  4. Then push.

Report both `git status` outputs in your final response so the parent
can verify.
```

## Other patterns

### Build-list edits respect the build lock

`formal/fstar/build-ocaml.sh` module lists are BUILD INPUTS. An agent
that adds its new module to the lists while `.build-running` exists
poisons the running cycle: compile reads the updated list but the
already-started extract never generated the new `.ml` ("Unbound
module" failures, hit live 2026-07-04, cycle 7). Briefs must say:
treat editing build-ocaml.sh / build-ocaml-serializer.sh exactly like
running fstar.exe - only while `.build-running` is ABSENT. Writing
the new `.fst` itself is always safe.

### Comment-trap warning in every .fst / .ml brief

Any brief that asks the agent to WRITE F\* or OCaml must include this
block verbatim — a subagent hit it in production on 2026-07-04
(`jsonld_runner.ml`: the sequence "F" + star + close-paren inside a
block comment ended the comment early; syntax error pointed 70 lines
away):

```
## Comment syntax (MANDATORY)
- F* files: use // line comments ONLY for all new comments.
- OCaml files: block comments nest. Never write *), (*, or the
  F-star name as letter-F-then-star inside a comment - spell it
  F-star. Same for quoting patterns like construct(*): reword.
```

### Forbid hand-written .ml in `formal/fstar/ocaml-output/`

Any agent task that involves "make this OCaml side faster / fix this
behavior" should explicitly forbid editing extracted `.ml` files
directly:

```
## Iron rule #11 (MANDATORY)

Inside the verified library boundary, OCaml is `assume val`
realisations only. Do NOT hand-edit any extracted file under
$WORKTREE_PATH/formal/fstar/ocaml-output/*.ml — fix the .fst source
or add a patch script under
$WORKTREE_PATH/formal/fstar/experimental_ocaml_glue/ or
$WORKTREE_PATH/formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/

Consumer-side .ml (w3c_runner.ml, owl_runner.ml, factoidal_*.ml,
rdfc10_runner.ml, cottas_ondisk_smoketest.ml) are hand-written
runners, NOT extracted. They are exempt from rule #13 but still
subject to rule #15 ("no semantic logic in test runners"). If you
find yourself adding logic to a runner, ask whether that logic
belongs in the F* spec instead.
```

### One agent = one commit-sized goal

Per anti-pattern #23 in CLAUDE.md. Don't dispatch "fix all of OWL DL";
dispatch "land prp-key (Cluster B) + report numerical impact". An
agent that doesn't know when to stop ships sprawl.

### Ship code sketches, not narrow instructions

Per anti-pattern #24. The prompt should include:
- Concrete file paths with line numbers
- The function names and signatures involved
- A code sketch of the proposed change
- The specific test or score that should move

Not just "make Tableau better."

## When to forgo `isolation: "worktree"`

For read-only research tasks, use the `Explore` subagent instead — no
worktree, no leakage hazard, no merge to coordinate.

For tasks that must commit + push code, always use `isolation:
"worktree"`. The leakage hazard is real but Rule 1 + Rule 2 manage it.

## Skill cross-refs

- `workflow-gotchas-debugging` — what to do when the rules above
  weren't followed and leakage already happened.
- `github-and-prs` — how the agent should branch + push.
- `build-and-test` — how the agent should run `build-ocaml.sh` (and
  the new `flock` lock that prevents extract races).
- `markdown-style` — agent commit messages and PR bodies.
- `choosing-models` — which model/effort tier to dispatch the agent
  on; this skill is only about what the prompt must say, not who runs
  it.
- `session-economy` — when to fan out to a subagent at all and how to
  keep the parent session's context small; this skill is the prompt
  template, not the fan-out policy.

## Proof-agent briefs (the licensing fan-out pattern, 2026-08-04)

Six licensing/preservation lemmas landed in one day via scoped
worktree agents, one rule per agent; two more taught the failure
modes. The brief shape that worked:

- **Ship the full proof sketch, not the goal.** Every green agent got
  the exact lemma statements, the witness chain spelled out, the
  template section to mirror (file + construct names), and the known
  soft spots ranked. Agents deviate from a sketch when verification
  demands it and say so; they do not reliably invent the sketch.
- **Name the verbatim-lambda constraint explicitly** (proof-shape
  trap #1 in `fstar-module-style`) or the agent will "clean up" the
  step function into a top-level definition and burn cycles on the
  failing assert_norm.
- **Include a two-attempt stop rule for anything near a known-hard
  shape.** The prp-inv agent lacked one and spent 318k tokens / 125
  tool calls circling an undischargeable goal (proof-shape trap #3).
  After the rule was added to briefs, the eq-trans agent on the
  neighbouring shape finished normally.
- **Agents deliver SECTIONS; the orchestrator owns the file.** Agents
  work on a stale branch point by construction — tell them not to
  renumber or reconcile, and graft their section onto the live file
  yourself (renumber the header, re-verify the combined module,
  commit). Landing conflicts between two agents editing the same
  file dissolve when neither agent commits.
- **Verify-before-trust stays mandatory**: re-run the full module
  verification in the MAIN tree before committing an agent section,
  even when the agent reports PASS — its worktree deps and branch
  point differ from yours.
- **Agents may end their turn "waiting on a monitor" while their
  verify still runs.** That final message is not a report; check
  their worktree directly (file present? fstar.exe running?) before
  resuming them — a resume costs tokens and may be unnecessary.

## The extract-without-compile stall (cost three cycles, 2026-07-13)

Agents that run `./build-ocaml.sh extract` (or whose last background
build was extract-only) and then measure with `bin/<platform>/*`
measure a STALE binary — extract regenerates `.ml` but does not relink.
Three separate overnight agents hit this on one night. Brief inclusion
for any agent that builds then measures: "if your last build step was
`extract`, run `./build-ocaml.sh compile` before measuring; verify
`stat -c '%y' bin/linux-x86_64/factoidal` is NEWER than your last
source edit." The orchestrator-side tell: BUILD_STATUS=OK from an
extract log + a binary mtime older than the newest `.ml`.


## Rule: agents must NEVER end a turn to "wait for a background build" (five occurrences, 2026-08-14..17)

The single most repeated agent failure of the #443..#448 work week:
an agent starts a long build with `run_in_background`, arms a Monitor
or says "the notification will resume me", and ENDS ITS TURN. Nothing
resumes it. Subagents are not woken by their own monitors or task
notifications — those go to the ORCHESTRATOR. The agent is simply
stopped, and the orchestrator pays a detection round + a resume prompt
every time. Five agents did this in four days, several twice.

MANDATORY brief inclusion for any agent that builds:

> Never end your turn to wait for a build. Poll in the foreground and
> continue in the SAME turn:
>   while kill -0 <BUILD_PID> 2>/dev/null; do sleep 20; done
> If you did not keep the PID, match the LAUNCHER string
> (`pgrep -f "bash ./build-ocaml.sh"`), NEVER the bare script name —
> `pgrep -f "build-ocaml.sh"` matches your own polling shell and
> loops forever (workflow-gotchas hazard #17 + addendum).

The orchestrator-side tell that an agent has done this anyway: its
task-notification "result" is a sentence about waiting, not a report.
Resume it immediately with the poll instruction; do not wait for it.
