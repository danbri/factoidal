---
name: session-restore
description: Restore a fresh or recycled VM/container/session to full working state in minutes, not hours — the cache inventory (toolchain-cache branch, .checked verification cache, pycottas venv, skill symlinks), what the bootstrap hook restores automatically vs what needs a command, and the never-again rules from the 2026-07-03 session that burned ~90 minutes compiling F* from source twice. Use on any fresh clone, restored VM, new sandbox, when fstar.exe or test data is missing, when a session is about to do something expensive that a previous session already did, or when adding a new cache-worthy artifact.
---

# Session / VM restoration: never rebuild what a previous session built

An ephemeral container is recycled; the repo is the only durable
store. Everything expensive a session produces must therefore either
be committed (binaries, per Iron Rule #9), pushed to a cache branch,
or accepted as lost. This skill is the inventory of what we cache,
how restoration works, and the mistakes that motivated it.

## What restores automatically (the bootstrap hook)

`.claude/hooks/session-start.sh` → `tools/sandbox-bootstrap.sh` runs
in remote sandboxes on every session start, all steps idempotent:

| Restored | From | Cold cost | Warm cost |
|---|---|---|---|
| Test submodules (w3c, rdf-canon) | git | ~1 min | no-op |
| Committed binaries check + `ocaml-output/` symlinks | `bin/<platform>/` | instant | instant |
| pycottas venv (`_tmp.junk/pycottas-venv`) | PyPI | ~1 min | no-op |
| **Skill discovery symlinks** `.claude/skills/<n>` | regenerated fresh from `skills/*/` | instant | instant |
| F\* toolchain (backgrounded) | `toolchain-cache` branch | ~2-4 min | no-op |
| fstar-mcp binary + daemon | cargo / running pid | ~2-3 min | instant |

Container state is cached after the hook completes, so a warm
container pays none of this.

## The cache branches (orphan, never merged)

- **`toolchain-cache`** — `bin/fstar.exe` + `lib/fstar` for the
  pinned F\* version (split <100MB chunks + SHA256SUMS). Consumer:
  `tools/install-toolchain-cache.sh`. Rebuild when
  `fstar_version` in `bin/ci-linux-x86_64/build-info.json` changes;
  instructions in the branch README.
- **`checked-cache`** (planned) — the repo's `formal/fstar/*.checked`
  verification cache. Content-digest keyed by F\*, so even a stale
  snapshot gives partial hits; a full cold re-verify of the tree
  costs ~2 hours, which is what this saves.

**Gate rule (non-negotiable): cache artifacts are pushed only from a
state that passed the full test battery** — F\* verification, the W3C
suites, and the perf gates — exactly like the committed binaries
(Iron Rule #9). A `.checked` set or toolchain snapshot from an
unproven tree would let every future session bootstrap from a
regression. Same order of operations as binaries: build → gates →
commit/push, never build → push → hope.

Pattern for new cache artifacts: orphan branch, split files under
100MB, SHA256SUMS, single amended commit (history of a cache is
worthless bulk), consumer script on the main line, restore step wired
into the bootstrap hook, entry in this table — and the gate rule
above.

## Skill discovery is regenerated, never trusted stale

`skills/` is the single source of truth for what skills exist. The
hook regenerates `.claude/skills/<name>` symlinks from a directory
scan **every session** — new skills get linked, deleted ones
unlinked, and the orientation output warns if a skill on disk is
missing from CLAUDE.md's human-facing index (fix CLAUDE.md when you
see that warning; do not let the two lists drift). When a Claude
session is in play, these symlinks are what make skills load
natively — they are not optional decoration.

## Never-again rules (2026-07-03, ~90 wasted minutes)

1. **Never compile F\* from source when a cache exists.** Check
   `toolchain-cache` first; `tools/install-toolchain-cache.sh` is the
   entry point. Source builds are for producing a NEW cache entry.
2. **Never let opam choose the F\* version.** Pin to CI's
   (`build-info.json`); a mismatched version verifies fine and then
   churns every extracted `.ml` — we paid the full compile twice.
3. **Never conclude "unreachable" from one 403.** Probe: git protocol
   reaches ANY GitHub repo (incl. clones into /tmp);
   `api.github.com` + release assets are blocked; PyPI/npm/crates are
   direct. Check `$HTTPS_PROXY/__agentproxy/status`. Release-only
   artifacts get mirrored into a cache branch — that is this repo's
   standard answer, endorsed as policy.
4. **Big one-off costs run once, then get cached for everyone.** If
   a session pays >10 minutes for reusable state, pushing it to a
   cache branch is part of finishing the task.
5. **Restoration must never block the session.** Hook steps are
   backgrounded and fail-open; a session can always run the committed
   binaries with zero toolchain.

## Manual restoration (non-hook harnesses, local dev)

```bash
git submodule update --init third_party/testing/w3c third_party/testing/rdf-canon
tools/install-toolchain-cache.sh        # F* + z3 + switch, 2-4 min
eval $(opam env --switch=fstar)         # every shell, before F* work
```

## What this skill does NOT cover

- Toolchain internals and repair — `fstar-env`.
- Making the verify/extract loop itself fast — `fast-verify-extract`.
- What to do once restored — `session-economy`.
