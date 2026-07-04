---
name: subagent-prompting
description: How to write subagent prompts for the Factoidal repo so the agent's work actually lands cleanly. Use whenever you dispatch a subagent with the Agent tool, especially with `isolation: "worktree"`. Two load-bearing rules. (1) Path discipline — agents must use only paths under their worktree, not absolute paths from your prompt context. (2) Post-condition checks — agent must verify its main-worktree footprint is zero before reporting back. Also carries MANDATORY brief inclusions for build-list edits (only while `.build-running` is absent), the F*/OCaml comment-nesting trap, and iron rule #11 (no hand-editing extracted `.ml`) — plus the one-agent-one-commit and ship-code-sketches rules. Pairs with workflow-gotchas-debugging (which catalogues recovery steps when these rules are violated).
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
