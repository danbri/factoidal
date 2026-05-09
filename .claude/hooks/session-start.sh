#!/usr/bin/env bash
# .claude/hooks/session-start.sh
#
# Runs at the start of every Claude Code session. On the Anthropic
# remote sandbox (CLAUDE_CODE_REMOTE=true) ensures the fstar-mcp
# binary referenced by .mcp.json is installed under ~/.cargo/bin.
# Idempotent: skips work entirely if the binary is already present.
#
# Local dev environments are left alone — contributors who want
# fstar-mcp on a Mac/laptop should run the cargo install line below
# manually (it lives in CLAUDE.md too).
#
# Failure mode: never blocks the session. If the install fails, the
# session still starts; the fstar MCP server simply won't load on
# this session and Claude falls back to running fstar.exe in batch
# mode. The hook prints the failure to stderr so the next session can
# pick it up.

set -euo pipefail

# Web/sandbox-only — keep local dev fast.
if [[ "${CLAUDE_CODE_REMOTE:-}" != "true" ]]; then
  exit 0
fi

# Idempotent: already installed → done.
if [[ -x "$HOME/.cargo/bin/fstar-mcp" ]]; then
  exit 0
fi

if ! command -v cargo >/dev/null 2>&1; then
  echo "session-start: cargo not found; cannot install fstar-mcp" >&2
  exit 0
fi

echo "session-start: installing FStarLang/fstar-mcp via cargo (~2-3 min on a cold sandbox)..." >&2
if cargo install --git https://github.com/FStarLang/fstar-mcp.git --quiet 2>&1 | tail -20 >&2; then
  echo "session-start: fstar-mcp installed at $HOME/.cargo/bin/fstar-mcp" >&2
else
  echo "session-start: fstar-mcp install failed; the F* MCP server will be unavailable this session" >&2
fi

exit 0
