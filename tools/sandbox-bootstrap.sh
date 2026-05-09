#!/usr/bin/env bash
# tools/sandbox-bootstrap.sh
#
# Vendor-neutral session-start bootstrap. Runs once at the start of an
# agent session in a sandboxed dev environment to ensure tools the
# repo's .mcp.json references are installed. Today that means the
# fstar-mcp binary (FStarLang/fstar-mcp) under ~/.cargo/bin.
# Idempotent: skips work entirely if the binary is already present.
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
# manually (also documented in README.md and CLAUDE.md).
#
# Failure mode: never blocks the session. If the install fails, the
# session still starts; the F* MCP server simply won't load on this
# session and the agent falls back to running fstar.exe in batch mode.
# The script prints the failure to stderr so the next session can pick
# it up.

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
# --locked is essential. fstar-mcp's git dep `pmcp` (paiml/rust-mcp-sdk)
# moved to an incompatible API at HEAD; without --locked, cargo resolves
# to that and the build fails (StreamableHttpServerConfig missing
# allowed_origins / max_request_bytes). The committed Cargo.lock pins
# pmcp 1.9.4, which is what fstar-mcp's source actually compiles against.
if cargo install --git https://github.com/FStarLang/fstar-mcp.git --locked --quiet 2>&1 | tail -20 >&2; then
  echo "session-start: fstar-mcp installed at $HOME/.cargo/bin/fstar-mcp" >&2
else
  echo "session-start: fstar-mcp install failed; the F* MCP server will be unavailable this session" >&2
fi

exit 0
