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

## What this does NOT change

- The git author/committer identity currently used for automated
  commits (`Claude <noreply@anthropic.com>`) stays as-is — it is
  repository metadata, not commit-message content, and changing it to
  a human identity would misattribute authorship. If the owner wants
  a different identity, that is a separate decision.
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
