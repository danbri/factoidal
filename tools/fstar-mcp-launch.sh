#!/usr/bin/env bash
# tools/fstar-mcp-launch.sh
#
# Wrapper invoked by .mcp.json (project-scoped MCP server config) so
# that the fstar-mcp binary runs with the F* opam switch active and a
# discoverable fstar.exe on PATH.
#
# fstar-mcp wraps F*'s --ide stdio protocol. It exposes tools like
# create_session, type_at_position, current_proof_context, etc., that
# avoid Claude having to rerun `fstar.exe`/`make verify` in batch mode
# for every diagnostic.
#
# Layout:
#   - This wrapper is committed at tools/fstar-mcp-launch.sh.
#   - The fstar-mcp binary is installed by .claude/hooks/session-start.sh
#     into ~/.cargo/bin/ on first session of a fresh sandbox (idempotent).
#   - .mcp.json at the repo root references this wrapper.
#
# We activate the fstar opam switch unconditionally — without it,
# fstar.exe is not on PATH and create_session calls fail. The opam
# switch name "fstar" is the project convention (see CLAUDE.md rule
# #12 and the fstar-env skill).

set -euo pipefail

# Activate the fstar opam switch if available. Fall back silently if
# opam is not installed (lets a non-F* dev still load Claude Code in
# this repo without crashing the MCP boot). Unsourceable env -> let
# fstar-mcp's own create_session error handling surface the problem.
if command -v opam >/dev/null 2>&1; then
  eval "$(opam env --switch=fstar 2>/dev/null || true)"
fi

# Locate the fstar-mcp binary. Prefer ~/.cargo/bin (cargo install
# default), then $PATH, then a vendored project-local build.
BIN=""
for cand in "$HOME/.cargo/bin/fstar-mcp" "$(command -v fstar-mcp 2>/dev/null || true)"; do
  if [[ -n "$cand" && -x "$cand" ]]; then BIN="$cand"; break; fi
done

if [[ -z "$BIN" ]]; then
  echo "fstar-mcp: binary not found; expected ~/.cargo/bin/fstar-mcp" >&2
  echo "  install with: cargo install --git https://github.com/FStarLang/fstar-mcp.git" >&2
  echo "  or open a fresh Claude Code session — .claude/hooks/session-start.sh installs it" >&2
  exit 127
fi

exec "$BIN" "$@"
