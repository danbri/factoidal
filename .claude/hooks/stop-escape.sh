#!/usr/bin/env bash
# Project-level Stop-hook escape hatch.
#
# Purpose: break out of a Stop-hook-induced response loop (e.g. a goal-tracker
# hook that exits 2 to keep relaunching the agent) when the user has no
# working way to issue a slash command — notably on mobile, where /goal clear
# is sent as plain text args instead of invoking the command.
#
# Mechanism: if the sentinel file .claude/STOP exists in the project root,
# this hook force-terminates the Claude Code process tree. That bypasses any
# other Stop hooks (project-level or user-level) that would otherwise exit 2
# and keep the loop alive.
#
# How to trigger from mobile when stuck:
#   - From the GitHub mobile UI, create .claude/STOP on the branch the
#     runaway session is working on, then ask the agent to `git pull`; OR
#   - Send the runaway agent a chat message: "Run: touch .claude/STOP".
#     The next Stop hook invocation will kill the session.

set -u

# Drain stdin; hook receives JSON we don't need to parse.
cat >/dev/null 2>&1 || true

SENTINEL="${CLAUDE_PROJECT_DIR:-$PWD}/.claude/STOP"
[[ -e "$SENTINEL" ]] || exit 0

echo "[.claude/STOP detected] terminating Claude Code session to break Stop-hook loop." >&2

# Remove the sentinel so the next session starts clean.
rm -f "$SENTINEL" 2>/dev/null || true

# Walk up the process tree to find the top-most claude-code process and
# terminate it. Killing $PPID alone is not always enough — the parent may
# itself be a child of the harness manager.
pid=$PPID
top=$pid
for _ in 1 2 3 4 5 6 7 8; do
  ppid=$(ps -o ppid= -p "$pid" 2>/dev/null | tr -d ' ')
  [[ -z "${ppid:-}" || "$ppid" -le 1 ]] && break
  cmd=$(ps -o comm= -p "$ppid" 2>/dev/null | tr -d ' ')
  case "$cmd" in
    *claude*|node|*node*) top=$ppid ;;
  esac
  pid=$ppid
done

kill -TERM "$top" 2>/dev/null || true
( sleep 2 && kill -KILL "$top" 2>/dev/null ) &

exit 0
