---
name: github-and-prs
description: Use the GitHub CLI (gh) for the Factoidal repository's PR / issue / branch workflow. Use when the user asks to create / view / merge a PR, list branches, audit stale branches, comment on an issue, or anything involving gh commands. The Factoidal repo's git remote uses a local proxy that confuses gh's repo inference, so all commands need an explicit --repo flag.
---

# GitHub CLI for the Factoidal repo

The git remote in this project points at a local proxy
(`http://local_proxy@127.0.0.1:.../git/danbri/factoidal`) so that pushes
work in restricted-network environments. As a side effect, `gh` cannot
infer the repo from the remote and fails with:

```
none of the git remotes configured for this repository point to a known GitHub host
```

**Fix: every `gh` command takes `--repo danbri/factoidal` explicitly.**
This is the single most common failure mode and accounts for ~all
gh-related friction in this project.

## Auth setup (one-time per sandbox)

If `gh auth status` reports "not logged into any GitHub hosts":

### Device flow (interactive, no token needed)

```bash
curl -sX POST https://github.com/login/device/code \
  -H "Accept: application/json" \
  -d "client_id=178c6fc778ccc68e1d6a&scope=repo+read:org+workflow"
```

Output is JSON with `user_code`, `verification_uri`,
`device_code`. Open `verification_uri` in a browser, enter
`user_code`, authorize. Then poll for the token:

```bash
DEVICE_CODE=...   # from the previous response
curl -sX POST https://github.com/login/oauth/access_token \
  -H "Accept: application/json" \
  -d "client_id=178c6fc778ccc68e1d6a&device_code=$DEVICE_CODE&grant_type=urn:ietf:params:oauth:grant-type:device_code" \
  | python3 -c 'import sys,json; print(json.load(sys.stdin)["access_token"])'
```

Save the token via:

```bash
echo "<token>" | gh auth login --with-token
gh auth status
```

The client_id `178c6fc778ccc68e1d6a` is `gh`'s public client — the
flow is identical to what `gh auth login -w` does internally, just
scriptable.

### Personal access token (faster)

If the user already has a PAT, paste it via:

```bash
echo "$GH_TOKEN" | gh auth login --with-token
```

## Branch + PR conventions

### Branch naming

- `claude/<topic>` for any agent or human work. Topics use kebab-case.
- Examples: `claude/track1-rdfc10-escape-delegate`,
  `claude/build-z3version-flag`, `claude/fstar-only-query-planning-recovery`.
- Avoid project codenames in branch names (per the recovery plan +
  glossary policy). Use the descriptive name for the work.

### PR base

- Default base branch is **`claude/main`**, not `main`.
- Pass `--base claude/main` explicitly to gh commands.

### Standard PR creation

```bash
gh pr create --repo danbri/factoidal \
  --base claude/main \
  --head claude/<branch> \
  --title "..." \
  --body "$(cat <<'EOF'
## Summary
- ...

## Test plan
- [ ] ...
EOF
)"
```

### Standard inspection

```bash
gh pr list --repo danbri/factoidal --state open
gh pr list --repo danbri/factoidal --state merged --limit 50
gh pr view 164 --repo danbri/factoidal
gh pr view 164 --repo danbri/factoidal --json mergeable,mergeStateStatus
gh pr checks 164 --repo danbri/factoidal
```

### Merging

The user merges. **Don't** run `gh pr merge` yourself unless the user
explicitly says so. PRs in this repo are reviewed and merged
manually.

### Force-push policy

Force-push to a PR's head branch is acceptable when:

1. The user has approved it (explicit "Y" or "yes").
2. The branch is the user's own (or a Claude-generated branch).
3. The remote tip has only a CI-shadow auto-commit on top of your
   real work (clobbering the shadow is lossless).

**Never** force-push:

- To `claude/main` or `main`.
- After someone else has commented on the PR (their inline review
  comments will detach from line numbers).

Use `--force-with-lease` first; fall back to `--force` only when a
known-safe CI shadow is the cause of the lease rejection.

## Branch cleanup workflow

The repo accumulates `claude/<topic>` branches faster than they get
deleted. The recipe for safe cleanup:

```bash
# 1. List all merged PRs and their head branches
gh pr list --repo danbri/factoidal --state merged --limit 200 \
  --json number,headRefName,title,mergedAt \
  > /tmp/merged-prs.json

# 2. List all remote branches
git ls-remote --heads origin | awk '{print $2}' | sed 's|refs/heads/||' \
  > /tmp/remote-branches.txt

# 3. Cross-reference: branches whose head was merged are safe to delete.
python3 -c '
import json, sys
prs = json.load(open("/tmp/merged-prs.json"))
merged = {p["headRefName"]: p for p in prs}
for line in open("/tmp/remote-branches.txt"):
    b = line.strip()
    if not b.startswith("claude/"): continue
    if b in ("claude/main",): continue
    if b in merged:
        print(f"DELETE {b} (PR #{merged[b]['"'"'number'"'"']} merged {merged[b]['"'"'mergedAt'"'"'][:10]})")
    else:
        print(f"KEEP   {b} (no merged PR; check manually)")
' | sort
```

Surface the DELETE list to the user, get explicit approval, then:

```bash
xargs -n1 git push origin --delete < /tmp/branches-to-delete.txt
```

**Never delete a branch without user approval**, even if it looks
obviously stale. Some branches hold in-progress work that hasn't
been pushed elsewhere.

## CI

This repo uses GitHub Actions. The relevant workflows:

| Workflow | Path | Trigger |
|---|---|---|
| `check-extraction` | `.github/workflows/check-extraction.yml` | PR + push |
| `check-fstar-purity` (Omega3) | `.github/workflows/check-fstar-purity.yml` | PR diff |
| `w3c-tests` | `.github/workflows/w3c-tests.yml` | push to `claude/main` |
| `check-derived-files` | `.github/workflows/check-derived-files.yml` | PR |
| `deploy-pages` | `.github/workflows/deploy-pages.yml` | push to `claude/main` |
| `ukparliament-bench` | `.github/workflows/ukparliament-bench.yml` | manual |
| `debug-bytecode-build` | `.github/workflows/debug-bytecode-build.yml` | manual |

The `w3c-tests` workflow auto-pushes a "ci(linux-x86_64): shadow
build artifacts [skip ci]" commit to `claude/main` whenever the
binaries change. PRs that have stale binaries diverge from
`claude/main` here — usually merge-conflict on
`bin/ci-linux-x86_64/build-info.json`. The standard fix is the
`merge=ours` git driver (see CLAUDE.md).

```bash
gh run list --repo danbri/factoidal --limit 10
gh run view <run-id> --repo danbri/factoidal
gh run watch <run-id> --repo danbri/factoidal
```

## What this skill does NOT do

- Does not interact with private/forked repos. Scope is
  `danbri/factoidal` only.
- Does not bypass review — never `gh pr merge` without user OK.
- Does not delete branches without user approval, even when "obviously"
  merged.

## Cross-references

- `fstar-env` skill — toolchain setup if `fstar.exe` is missing.
- `build-and-test` skill — local verification before opening a PR.
- `docs/claude-rules/anti-patterns.md` — full anti-pattern table.
