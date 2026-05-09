#!/usr/bin/env bash
# tools/sandbox-bootstrap.sh
#
# Vendor-neutral session-start bootstrap. Runs at the start of an
# agent session in a sandboxed dev environment to (a) ensure the
# fstar-mcp binary is installed and (b) start the fstar-mcp daemon
# so .mcp.json's http://127.0.0.1:3700 has something to talk to.
# Both steps are idempotent — fast no-op if already done.
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

# 1. Install fstar-mcp if missing. --locked is essential: fstar-mcp's
#    git dep `pmcp` (paiml/rust-mcp-sdk) moved to an incompatible API
#    at HEAD, so without the committed Cargo.lock (pmcp 1.9.4) the
#    build fails (StreamableHttpServerConfig missing allowed_origins /
#    max_request_bytes).
if [[ ! -x "$HOME/.cargo/bin/fstar-mcp" ]]; then
  if ! command -v cargo >/dev/null 2>&1; then
    echo "session-start: cargo not found; cannot install fstar-mcp" >&2
    exit 0
  fi
  echo "session-start: installing FStarLang/fstar-mcp via cargo (~2-3 min on a cold sandbox)..." >&2
  if cargo install --git https://github.com/FStarLang/fstar-mcp.git --locked --quiet 2>&1 | tail -20 >&2; then
    echo "session-start: fstar-mcp installed at $HOME/.cargo/bin/fstar-mcp" >&2
  else
    echo "session-start: fstar-mcp install failed; the F* MCP server will be unavailable this session" >&2
    exit 0
  fi
fi

# 2. Start (or rejoin) the daemon so MCP clients can connect.
"$(dirname "$0")/fstar-mcp-server.sh" start || \
  echo "session-start: fstar-mcp daemon failed to start; F* MCP unavailable" >&2

exit 0
