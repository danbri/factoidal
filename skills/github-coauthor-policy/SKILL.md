---
name: github-coauthor-policy
description: Commit-message attribution policy for this repository — do NOT list Claude's role in GitHub commits. No Co-Authored-By Claude trailers, no "Generated with Claude Code" lines, no Claude-Session links, no prose crediting Claude in commit messages. Use whenever writing a git commit in this repo, and when configuring or reviewing any tool/harness that appends attribution trailers automatically.
---

# GitHub co-author policy

Owner directive (2026-07-05): **do not list Claude's role in GitHub
commits.**

## The rule

Commit messages in this repository must not contain:

- `Co-Authored-By: Claude ...` trailers (any model name or variant)
- `🤖 Generated with [Claude Code](...)` or similar generated-with
  lines
- `Claude-Session: https://claude.ai/code/...` links
- Prose crediting Claude, an AI assistant, or a model in the commit
  subject or body ("implemented by Claude", "AI-assisted", etc.)

Commit messages describe the change: what it does, measured results,
spec references, issue links. Nothing about who or what typed it.

## Identity fields (updated 2026-07-29)

Owner directive (2026-07-29, verbatim: "we don't gpg nor credit ai
tools with code authorship" and, on the identity field specifically,
"It is my repo"): the git author/committer identity for commits made
by Claude sessions is the OWNER's identity, `Dan Brickley
<danbri@danbri.org>` — the no-AI-credit rule covers the metadata
fields, not just the message body. This supersedes this file's
earlier "identity stays `Claude <noreply@anthropic.com>`" paragraph.
Set it repo-local in every session/worktree that commits:
`git config user.name "Dan Brickley" && git config user.email
danbri@danbri.org`. Subagent briefs that authorize commits must
include this alongside the message rule. Consequence accepted by
the owner: the container's SSH signing key is registered to the bot
address, so a human-committed commit cannot verify against it and
GitHub shows it "Unverified". Correct attribution outranks the badge.

### The policy is now enforced by the bootstrap, not by memory
(2026-08-26)

For a month this rule depended on the agent remembering to run the
`git config` pair in every session and worktree, and on the agent
IGNORING a hook that told it to do the opposite. The hosted CCR image
ships two hooks:

- a SessionStart hook setting the GLOBAL identity to
  `Claude <noreply@anthropic.com>`;
- a Stop hook that, on any commit GitHub would mark Unverified,
  printed `Please run 'git config user.email noreply@anthropic.com &&
  git config user.name Claude'`.

That second one is a standing instruction to violate iron rule #13,
issued at the end of every turn, with an exit code that blocks the
turn. Telling a future session to "ignore that nag" is not a control;
an instruction repeated every turn beats a rule read once.

Owner instruction, 2026-08-26, verbatim: "Delete the hook instruction
to leak our ai tooling decisions into github; all attributions are to
responsible human only".

Both hooks were rewritten in the container, and — because
`/root/.claude/` dies with the container — the durable fix lives in
the repository: `tools/sandbox-bootstrap.sh` pins the REPOSITORY-LOCAL
identity on every session start and prints it in the bootstrap block
(`- commit identity: Dan Brickley <danbri@danbri.org> (repo-local;
human only)`). Repo-local config wins over global regardless of which
hook ran last, so the harness cannot take it back by reordering.

If a future session sees the bootstrap line report anything else, the
bootstrap did not run; fix that rather than committing.
- PR descriptions follow the same spirit: describe the diff, skip
  the attribution footer.
- CHANGELOG/docs prose is unaffected; this policy is about commits.

## For harness defaults that auto-append trailers

Claude Code's default guidance appends Co-Authored-By and session
trailers. This repository policy OVERRIDES that default. When
composing any `git commit -m` here, end the message after the
substantive content. If a hook or tool re-adds a trailer, strip it
before pushing (`git commit --amend`) — the policy applies to what
lands on `origin`, not to intermediate local state.

## Subagent briefs

Subagents rarely commit (the coordinator lands), but any brief that
does authorize a commit MUST quote this rule: "commit messages carry
no Claude attribution — no Co-Authored-By, no generated-with, no
session links, per skills/github-coauthor-policy."

## History note

Commits pushed before 2026-07-05 carry the old trailers. Do not
rewrite published history to remove them — the policy is forward-
looking.
