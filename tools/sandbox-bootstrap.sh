#!/usr/bin/env bash
# tools/sandbox-bootstrap.sh
#
# Vendor-neutral session-start bootstrap. Runs at the start of an
# agent session in a sandboxed dev environment to:
#   (a) initialise the two load-bearing test-data submodules
#       (third_party/testing/{w3c,rdf-canon}) — without them the
#       runners report zero tests and w3c-tests.sh clobbers the
#       committed dashboard with a 0/0 run;
#   (b) smoke-check the committed binaries for this platform
#       (Iron Rule #9: a fresh clone runs tests with no toolchain);
#   (c) ensure the fstar-mcp binary is installed and its daemon
#       started so .mcp.json's http://127.0.0.1:3700 answers;
#   (d) print a compact orientation block for the agent.
# Every step is idempotent — fast no-op if already done.
#
# Deliberately NOT done here: installing the opam/F*/z3 toolchain.
# That is a 30-60 minute build, only needed when editing .fst files;
# it stays an explicit step via skills/fstar-env/SKILL.md.
#
# Wired to:
#   - Claude Code: .claude/hooks/session-start.sh (one-line wrapper)
#   - Other agent harnesses: invoke this script from their session-
#     start hook directly. No Claude-specific assumptions in the body.
#
# Activates in a remote/sandbox environment only (the current trigger
# is CLAUDE_CODE_REMOTE=true; extend the gate when adding other
# harnesses). Local dev environments are left alone — contributors who
# want fstar-mcp on a Mac/laptop should run the cargo install line
# manually (also documented in README.md and CLAUDE.md) and start the
# daemon with tools/fstar-mcp-server.sh start.
#
# Failure mode: never blocks the session. If the install or daemon-
# start fails, the session still starts; the F* MCP server simply
# won't load on this session and the agent falls back to running
# fstar.exe in batch mode. Failures print to stderr so the next
# session can pick them up.

set -euo pipefail

# Web/sandbox-only — keep local dev fast.
if [[ "${CLAUDE_CODE_REMOTE:-}" != "true" ]]; then
  exit 0
fi

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# 0a. Test-data submodules (idempotent: fast no-op when populated).
#     Only the two the runners need; the other five (shex/csvw/vc/
#     did/rml) are unwired and stay lazy.
if [[ ! -e "$REPO_ROOT/third_party/testing/w3c/README.md" ]]; then
  echo "session-start: initialising W3C test submodules (first run on this container)..." >&2
  git -C "$REPO_ROOT" submodule update --init \
    third_party/testing/w3c third_party/testing/rdf-canon >&2 \
    || echo "session-start: submodule init FAILED — test runners will report zero tests; do not trust a 0/0 run" >&2
fi

# 0b. Committed-binary smoke check (never blocks; report only).
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)  PLAT=linux-x86_64 ;;
  Darwin-arm64)  PLAT=darwin-arm64 ;;
  *)             PLAT="" ;;
esac
BIN_STATUS="unknown platform: binaries must be built via build-ocaml.sh"
if [[ -n "$PLAT" ]]; then
  if "$REPO_ROOT/bin/$PLAT/factoidal" --help >/dev/null 2>&1; then
    BIN_STATUS="bin/$PLAT committed binaries OK (tests runnable with no toolchain)"
  else
    BIN_STATUS="bin/$PLAT binaries missing or not runnable — see skills/build-and-test"
  fi
  # Iron Rule #9's second half: ocaml-output/ symlinks point at the
  # platform bin/ dir. build-ocaml.sh makes these after a local build,
  # but a fresh clone lacks the untracked ones and tests/local/*
  # scripts hardcode the ocaml-output/ paths. Restore idempotently.
  for b in w3c_runner factoidal factoidal-http owl_runner rdfc10_runner; do
    if [[ ! -e "$REPO_ROOT/formal/fstar/ocaml-output/$b" && -x "$REPO_ROOT/bin/$PLAT/$b" ]]; then
      ln -sf "../../../bin/$PLAT/$b" "$REPO_ROOT/formal/fstar/ocaml-output/$b"
    fi
  done
fi

# 0c. pycottas venv — tests/local/{cottas_corpus,backend_parity,
#     parquet_footer}_regressions.sh need it to build .cottas
#     artifacts from the in-repo sample. Idempotent; non-fatal.
VENV="$REPO_ROOT/_tmp.junk/pycottas-venv"
if [[ ! -x "$VENV/bin/python" ]] || ! "$VENV/bin/python" -c "import pycottas" >/dev/null 2>&1; then
  echo "session-start: provisioning pycottas venv for tests/local COTTAS scripts..." >&2
  ( python3 -m venv "$VENV" && "$VENV/bin/pip" install --quiet pycottas ) >&2 \
    || echo "session-start: pycottas venv failed — tests/local COTTAS regressions will skip" >&2
fi

# 0c2. Skill discovery symlinks — .claude/skills/<name> -> ../../skills/<name>.
#      Regenerated fresh from the skills/ directory EVERY session so
#      discovery never trusts a stale committed list: new skills get
#      linked, deleted skills get unlinked. skills/ is the source of
#      truth; CLAUDE.md's ## Skills section is human documentation.
mkdir -p "$REPO_ROOT/.claude/skills"
for link in "$REPO_ROOT/.claude/skills"/*; do
  [ -L "$link" ] && [ ! -e "$link" ] && rm -f "$link"   # dangling
done
SKILL_DRIFT=""
for d in "$REPO_ROOT"/skills/*/; do
  n=$(basename "$d")
  [ -f "$d/SKILL.md" ] || continue
  [ -e "$REPO_ROOT/.claude/skills/$n" ] || ln -sfn "../../skills/$n" "$REPO_ROOT/.claude/skills/$n"
  grep -q "skills/$n/SKILL.md" "$REPO_ROOT/CLAUDE.md" || SKILL_DRIFT="$SKILL_DRIFT $n"
done
[ -n "$SKILL_DRIFT" ] && echo "session-start: WARNING skills missing from CLAUDE.md index:$SKILL_DRIFT" >&2

# 0d. F* toolchain from the repo's toolchain-cache branch (~2-4 min
#     cold, no-op warm). Backgrounded so session start never blocks;
#     verify-capable when it completes, compile-capable when its
#     background opam deps finish (see .claude-runs/toolchain-deps.log).
if ! command -v fstar.exe >/dev/null 2>&1 && [[ ! -x "$HOME/.opam/fstar/bin/fstar.exe" ]]; then
  echo "session-start: installing F* toolchain from cache branch in background -> .claude-runs/toolchain-cache-install.log" >&2
  mkdir -p "$REPO_ROOT/.claude-runs"
  nohup "$REPO_ROOT/tools/install-toolchain-cache.sh" \
    > "$REPO_ROOT/.claude-runs/toolchain-cache-install.log" 2>&1 &
fi

# 1. Install fstar-mcp if missing. --locked is essential: fstar-mcp's
#    git dep `pmcp` (paiml/rust-mcp-sdk) moved to an incompatible API
#    at HEAD, so without the committed Cargo.lock (pmcp 1.9.4) the
#    build fails (StreamableHttpServerConfig missing allowed_origins /
#    max_request_bytes).
MCP_STATUS="F* MCP daemon on :3700"
if [[ ! -x "$HOME/.cargo/bin/fstar-mcp" ]]; then
  if ! command -v cargo >/dev/null 2>&1; then
    echo "session-start: cargo not found; cannot install fstar-mcp" >&2
    MCP_STATUS="F* MCP unavailable (no cargo)"
  else
    echo "session-start: installing FStarLang/fstar-mcp via cargo (~2-3 min on a cold sandbox)..." >&2
    if cargo install --git https://github.com/FStarLang/fstar-mcp.git --locked --quiet 2>&1 | tail -20 >&2; then
      echo "session-start: fstar-mcp installed at $HOME/.cargo/bin/fstar-mcp" >&2
    else
      echo "session-start: fstar-mcp install failed; the F* MCP server will be unavailable this session" >&2
      MCP_STATUS="F* MCP unavailable (install failed)"
    fi
  fi
fi

# 2. Start (or rejoin) the daemon so MCP clients can connect.
if [[ "$MCP_STATUS" == "F* MCP daemon on :3700" ]]; then
  "$(dirname "$0")/fstar-mcp-server.sh" start || \
    { echo "session-start: fstar-mcp daemon failed to start; F* MCP unavailable" >&2; \
      MCP_STATUS="F* MCP unavailable (daemon failed)"; }
fi

# 2.5 Git freshness. A stale/behind checkout silently republishes old
#     numbers and wastes a session diagnosing a state origin already
#     fixed (2026-07-07 incident: a resumed container sat 78 commits
#     behind origin, unnoticed until a push was rejected). Fetch; if
#     behind, fast-forward when the tree is clean (auto-pull), and warn
#     loudly — never auto-overwrite — when it is dirty. Never blocks.
GIT_FRESHNESS="up to date with origin"
if BR=$(git -C "$REPO_ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null) && [ -n "$BR" ] && [ "$BR" != "HEAD" ]; then
  if timeout 30 git -C "$REPO_ROOT" fetch -q origin "$BR" 2>/dev/null; then
    BEHIND=$(git -C "$REPO_ROOT" rev-list --count "HEAD..origin/$BR" 2>/dev/null || echo 0)
    if [ "${BEHIND:-0}" -gt 0 ]; then
      if [ -z "$(git -C "$REPO_ROOT" status --porcelain 2>/dev/null)" ]; then
        if git -C "$REPO_ROOT" merge --ff-only "origin/$BR" -q 2>/dev/null; then
          GIT_FRESHNESS="was ${BEHIND} commit(s) behind origin/${BR} — auto-fast-forwarded to $(git -C "$REPO_ROOT" rev-parse --short HEAD)"
        else
          GIT_FRESHNESS="DIVERGED from origin/${BR} (behind ${BEHIND}, ff failed) — reconcile before trusting local state"
        fi
      else
        GIT_FRESHNESS="BEHIND origin/${BR} by ${BEHIND} but working tree is DIRTY — NOT auto-pulled; commit/stash, then 'git merge --ff-only origin/${BR}' before trusting local state or publishing"
      fi
    fi
  else
    GIT_FRESHNESS="could NOT fetch origin (offline/timeout) — freshness unconfirmed; verify before publishing dashboard/docs"
  fi
fi

# 3. Compact orientation block (stdout → added to session context).
#    Keep this short: it exists so the agent does NOT re-derive
#    environment state with a dozen exploratory commands.
FSTAR_STATUS="absent (committed binaries suffice for tests; for .fst work run skills/fstar-env)"
command -v fstar.exe >/dev/null 2>&1 && FSTAR_STATUS="fstar.exe on PATH"
cat <<ORIENT
factoidal session bootstrap:
- ${BIN_STATUS}
- test submodules: $([ -e "$REPO_ROOT/third_party/testing/w3c/README.md" ] && echo present || echo "MISSING (0/0 runs will lie)")
- F* toolchain: ${FSTAR_STATUS}
- ${MCP_STATUS}
- git: ${GIT_FRESHNESS}
- goal + working discipline: CLAUDE.md (skills index at the bottom)
- run tests: ./w3c-tests.sh | current scores: docs/test-results/latest.json
ORIENT

exit 0
