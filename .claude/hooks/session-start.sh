#!/usr/bin/env bash
# Thin wrapper — Claude Code's SessionStart hook trigger lives here,
# but the actual bootstrap logic is vendor-neutral and lives at
# tools/sandbox-bootstrap.sh so other agent harnesses can reuse it.
exec "$CLAUDE_PROJECT_DIR/tools/sandbox-bootstrap.sh" "$@"
