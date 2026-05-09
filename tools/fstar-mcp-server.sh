#!/usr/bin/env bash
# tools/fstar-mcp-server.sh start|stop|status
#
# Manages the fstar-mcp daemon. fstar-mcp 0.1.0 ships only a Streamable
# HTTP transport (no stdio mode), so Claude Code's .mcp.json points at
# http://127.0.0.1:$FSTAR_MCP_PORT and the server has to be running
# before MCP clients can talk to it.
#
# tools/sandbox-bootstrap.sh invokes this with `start` on session
# start. The daemon stays up until killed; subsequent sessions in the
# same sandbox reuse the existing process (idempotent start).
#
# PID and log files live under .claude-runs/ (already gitignored).

set -euo pipefail

# Must match the URL in .mcp.json. If you change one, change both.
PORT="${FSTAR_MCP_PORT:-3700}"
ROOT="${CLAUDE_PROJECT_DIR:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
RUN_DIR="$ROOT/.claude-runs"
PID_FILE="$RUN_DIR/fstar-mcp.pid"
LOG_FILE="$RUN_DIR/fstar-mcp.log"

_alive() {
  [[ -f "$PID_FILE" ]] && kill -0 "$(cat "$PID_FILE")" 2>/dev/null
}

case "${1:-start}" in
  start)
    if _alive; then
      echo "fstar-mcp: already running (pid $(cat "$PID_FILE")) on http://127.0.0.1:$PORT" >&2
      exit 0
    fi

    BIN=""
    for cand in "$HOME/.cargo/bin/fstar-mcp" "$(command -v fstar-mcp 2>/dev/null || true)"; do
      if [[ -n "$cand" && -x "$cand" ]]; then BIN="$cand"; break; fi
    done
    if [[ -z "$BIN" ]]; then
      echo "fstar-mcp: binary not found; expected ~/.cargo/bin/fstar-mcp" >&2
      echo "  install: cargo install --locked --git https://github.com/FStarLang/fstar-mcp.git" >&2
      echo "  or run tools/sandbox-bootstrap.sh, which installs it on a fresh sandbox" >&2
      exit 127
    fi

    # Activate the F* opam switch so fstar.exe is on PATH for
    # create_session calls. Silently no-op if opam isn't present.
    if command -v opam >/dev/null 2>&1; then
      eval "$(opam env --switch=fstar 2>/dev/null || true)"
    fi

    mkdir -p "$RUN_DIR"
    FSTAR_MCP_PORT="$PORT" nohup "$BIN" >"$LOG_FILE" 2>&1 &
    echo $! >"$PID_FILE"

    # Brief sanity wait — give the server a moment to bind. If it
    # died, surface the log tail and clean up the stale pidfile.
    sleep 1
    if ! _alive; then
      echo "fstar-mcp: failed to start; tail of log:" >&2
      tail -10 "$LOG_FILE" >&2 || true
      rm -f "$PID_FILE"
      exit 1
    fi
    echo "fstar-mcp: started on http://127.0.0.1:$PORT (pid $(cat "$PID_FILE"))" >&2
    ;;
  stop)
    if _alive; then
      kill "$(cat "$PID_FILE")"
      rm -f "$PID_FILE"
      echo "fstar-mcp: stopped" >&2
    else
      echo "fstar-mcp: not running" >&2
      rm -f "$PID_FILE"
    fi
    ;;
  status)
    if _alive; then
      echo "running (pid $(cat "$PID_FILE")) on http://127.0.0.1:$PORT"
    else
      echo "not running"
      exit 1
    fi
    ;;
  *)
    echo "usage: $0 {start|stop|status}" >&2
    exit 2
    ;;
esac
