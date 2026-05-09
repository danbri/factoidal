---
name: mcp-setup-readme
description: Reference for how MCP servers are wired in the Factoidal repo (today: `fstar-mcp` from FStarLang/fstar-mcp, served over HTTP on http://127.0.0.1:3700). Use when configuring, debugging, restarting, or adding to the project's MCP setup. Covers `.mcp.json`, the session-start bootstrap (`tools/sandbox-bootstrap.sh`), the daemon manager (`tools/fstar-mcp-server.sh`), port assignment via `FSTAR_MCP_PORT`, and why we run HTTP transport instead of stdio. Pairs with the `fstar-mcp` skill (which covers USING the F* MCP for proof / typecheck queries during development).
metadata:
  mcp_servers: fstar-mcp
  transport: streamable-http
  default_port: "3700"
---

# MCP setup — Factoidal repo

This skill is the **wiring** reference. The companion `fstar-mcp`
skill is the **using** reference (lookup_symbol, create_session,
get_proof_context, …). Read this one when something about the MCP
plumbing is broken or being changed.

## What's wired today

| Server | Source | Transport | URL / endpoint | Config |
|---|---|---|---|---|
| `fstar` | [FStarLang/fstar-mcp](https://github.com/FStarLang/fstar-mcp) v0.1.0 | Streamable HTTP | `http://127.0.0.1:3700` | `.mcp.json` |

`.mcp.json` (project-scoped, committed) is read by every MCP-aware
client — Claude Code, Cursor, Continue, Zed, Cline, etc. The same
file works for all of them. Project-scoped MCPs require a one-time
per-client trust prompt on first session.

## File map

```
.mcp.json                              project-scoped MCP server config
tools/sandbox-bootstrap.sh             vendor-neutral session-start bootstrap
tools/fstar-mcp-server.sh              {start|stop|status} daemon manager
.claude/hooks/session-start.sh         Claude Code wrapper -> sandbox-bootstrap.sh
.claude/settings.json                  registers SessionStart hook
.claude-runs/fstar-mcp.{pid,log}       runtime state (gitignored)
~/.cargo/bin/fstar-mcp                 binary, installed by the bootstrap
```

The daemon's binary is **not** committed. The bootstrap installs it
on first session start in a remote/sandbox environment via
`cargo install --locked --git ...`. Local contributors install once
manually (see `skills/fstar-mcp/SKILL.md`).

## Lifecycle

| Command | Effect |
|---|---|
| `tools/fstar-mcp-server.sh start` | Start the daemon if not already running. Idempotent. Activates the F* opam switch first so `fstar.exe` is on PATH inside the daemon. Writes pid + log under `.claude-runs/`. |
| `tools/fstar-mcp-server.sh stop` | Kill the daemon, clean up pidfile. |
| `tools/fstar-mcp-server.sh status` | Print running / not running. |
| `tools/sandbox-bootstrap.sh` | Install (if missing) + start. Wired to Claude Code's `SessionStart` event via `.claude/hooks/session-start.sh`. |

## Why HTTP, not stdio

`.mcp.json` would normally use `command:` entries (stdio transport
— the MCP server is spawned as a child process per session and
talks JSON-RPC over its own stdin/stdout). That's the simpler model
and it's what most MCP servers ship with.

**fstar-mcp 0.1.0 is HTTP-only.** Its `pmcp` dependency
(paiml/rust-mcp-sdk) only exposes a `StreamableHttpServer`. There is
no `--stdio` flag. So we run the binary as a long-lived background
daemon and point `.mcp.json` at its URL:

```json
{
  "mcpServers": {
    "fstar": {
      "type": "http",
      "url": "http://127.0.0.1:3700"
    }
  }
}
```

When upstream adds stdio (or someone forks one in), the wiring
collapses back to a single `command:` line and the bootstrap can
drop the daemon-start step. Tracked informally — no issue yet.

## Port

`FSTAR_MCP_PORT` (default `3700`). Three places must agree:

1. `.mcp.json` URL
2. `tools/fstar-mcp-server.sh` `PORT` default
3. The env var the daemon receives at start time

If you change the port, change all three. The daemon manager script
already reads `FSTAR_MCP_PORT` and forwards it to the daemon's env;
only `.mcp.json` is hard-coded.

## Pinning gotcha (anti-pattern #5)

The Makefile passes `--z3version 4.13.3`. The MCP daemon inherits
the `fstar` opam switch's PATH (so `fstar.exe` is the same one
`make verify` uses, and z3 is `/usr/local/bin/z3` 4.13.3 — verified
by reading `/proc/$pid/environ` on the running daemon).

**But** when calling `create_session` you must pass
`options: ["--z3version", "4.13.3"]` explicitly. Without it,
`fstar.exe` accepts any z3 on PATH and you can drift into
green-in-MCP / red-in-`make verify` territory. The `fstar-mcp`
skill repeats this; it's worth repeating here because it bites
during debugging.

## Debugging checklist

When the MCP isn't responding:

1. `tools/fstar-mcp-server.sh status` — daemon running at all?
2. `curl -s -o /dev/null -w "%{http_code}\n" http://127.0.0.1:3700/`
   — should return `406` (server is up; needs MCP headers).
3. `tail .claude-runs/fstar-mcp.log` — last lines of the daemon's
   own log.
4. `pgrep -f fstar-mcp` — confirm the pidfile matches reality.
5. `lsof -i :3700` (or `cat /proc/net/tcp | awk '$4=="0A"'`) —
   port collision.
6. In Claude Code: client may have lost the connection without the
   server actually being down. Restart the client. Each MCP tool is
   its own permission unit, so first use re-prompts.

A real MCP `initialize` round-trip:

```bash
curl -s -X POST http://127.0.0.1:3700/ \
  -H "Content-Type: application/json" \
  -H "Accept: application/json, text/event-stream" \
  -H "mcp-protocol-version: 2024-11-05" \
  -d '{"jsonrpc":"2.0","id":1,"method":"initialize",
       "params":{"protocolVersion":"2024-11-05",
                 "capabilities":{},
                 "clientInfo":{"name":"smoke","version":"0"}}}'
```

A healthy server returns
`{"result":{"protocolVersion":"2024-11-05","capabilities":{...},"serverInfo":{"name":"fstar-mcp","version":"0.1.0"}}}`.

## Adding another MCP server

To add a second server (e.g. a git/GH MCP, a vector store):

1. Append to `mcpServers` in `.mcp.json`. Use `command:` if it
   supports stdio (preferred — no daemon lifecycle).
2. If HTTP-only, pick a port not in `[3000, 3700]` and add a
   manager script (model after `tools/fstar-mcp-server.sh`).
3. Update `tools/sandbox-bootstrap.sh` to start it after install.
4. Document in this skill's "What's wired today" table.

## Permissions

Project-scoped MCPs require trust on first use. To pre-approve the
read-only `fstar-mcp` tools so they don't re-prompt every session,
add to `.claude/settings.json` (committed, repo-wide) or
`.claude/settings.local.json` (gitignored, personal):

```json
{
  "permissions": {
    "allow": [
      "mcp__fstar__create_session",
      "mcp__fstar__close_session",
      "mcp__fstar__list_sessions",
      "mcp__fstar__lookup_symbol",
      "mcp__fstar__get_proof_context"
    ]
  }
}
```

`update_buffer`, `typecheck_buffer`, and `restart_solver` mutate
F\*'s VFS or the z3 process — leave those prompting unless you
have a specific reason to auto-approve.

## Pairs with

- `fstar-mcp` — using the F* MCP for proof / typecheck queries.
- `fstar-env` — the underlying opam switch + z3 that the daemon
  inherits at start.
- `workflow-gotchas-debugging` — broader dev-loop hazards.
