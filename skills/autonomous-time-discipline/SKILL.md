---
name: autonomous-time-discipline
description: Discipline for long-running autonomous work — always make use of wall-clock time. Use when running multi-hour sessions, kicking long builds in the background, waiting on system notifications, or when you suspect a background job has stalled. Codifies the silent-stall failure mode (background job dies, no notification arrives, you sit waiting) and the timers/loops/monitors/callbacks toolkit that prevents it.
---

# Autonomous time discipline

This skill codifies one rule: **never sit idle waiting for a notification
that may not arrive.** Background jobs can die silently — killed by
`timeout`, OOM, the harness reaping the parent shell, an MCP reconnect
storm dropping the event. If you treat "no news" as "still running,"
you can lose hours.

## The failure mode

I had a background extract+compile job. The bash exited (probably
hit `timeout`). The completion event never landed in my conversation —
either dropped during an MCP reconnect or the process was reaped before
emitting it. I waited ~3 hours assuming "still running" before the user
asked for status and I checked `date`.

Lost ~3 hours on a 4-hour session. **Silence is not success.**

## The toolkit

You have all the primitives. Use them in combination:

### 1. Wall-clock awareness — always

Run `date -u` whenever you check on background work. Compare against
the start time of the job. If wall-clock has elapsed past the
expected duration, the job is dead even if no notification arrived.

```bash
echo "started $(date -u)" >> /tmp/job.log
... long command ... &
echo "checked $(date -u), expected ~5min"
```

Most claude-side Bash output already carries timestamps via the OS;
read them. `stat -c '%y'` on a log file tells you when it was last
written — if more than your timeout ago, the writer is gone.

### 2. `Bash run_in_background` — for one-shot waits

Use when you need ONE notification: "tell me when X is done." The
inner command must EXIT when the condition is met, not loop forever.

```bash
# Right — exits when the build is done
timeout 1800 ./build.sh extract && timeout 1800 ./build.sh compile
echo "done at $(date -u)"

# Wrong — never exits, no completion event
tail -f build.log | grep "Built:"
```

Crucially: **the parent claude harness sends ONE event per
background bash, when it exits.** If the bash hangs, no event. If
the bash gets killed by `timeout`, you DO get an event with the kill
exit code (usually 124 or 143) — but if the system drops it during
a reconnect, you still get nothing. So pair it with #3.

### 3. `Monitor` — for streaming progress + terminal-state coverage

Use Monitor when you want to see incremental progress AND catch
terminal states (success, failure, crash, hang). The filter should
emit on every state you'd act on, not just the happy path:

```bash
tail -F /tmp/build.log /tmp/test.log 2>/dev/null \
  | grep --line-buffered -E 'Extracted module|FAIL|FATAL|Error|^Built|Pipeline complete|exited rc='
```

The Monitor skill doc has the full pattern. Coverage rule from
there: **if this process crashed right now, would my filter emit
anything?** If not, widen it.

### 4. Wall-clock heartbeats inside long jobs

Stamp `date -u` at every phase boundary so log mtimes reflect real
progress, not the cached log of a dead job:

```bash
echo "phase 1 start $(date -u)"
./step1.sh
echo "phase 1 done $(date -u)"
echo "phase 2 start $(date -u)"
./step2.sh
echo "phase 2 done $(date -u)"
```

Then `tail -1 /tmp/log` tells you the last phase boundary; compare
to `date -u` to see if the job is making progress.

### 5. Stale-lock cleanup before restart

When a build dies under `timeout`, its EXIT trap may not fire,
leaving stale `.build-running` / `.build.lock` markers. The next
build will refuse to start ("another build is already running"). On
restart, ALWAYS check + clean:

```bash
ls -la /home/user/factoidal/formal/fstar/.build-running \
       /home/user/factoidal/formal/fstar/.build.lock 2>&1
# if any are stale (mtime > 1h with no live process), rm them.
pgrep -af 'build-ocaml' | grep -v 'pgrep\|grep' | head
# if zero, the locks are stale and safe to remove.
rm -f /home/user/factoidal/formal/fstar/.build-running \
      /home/user/factoidal/formal/fstar/.build.lock
```

### 6. The `pgrep` self-match trap

`pgrep -f 'build-ocaml.sh extract'` matches its OWN argv when run
inside a wrapper bash whose argv contains the literal string. Two
fixes:

```bash
# Wrong — matches self
until ! pgrep -f 'build-ocaml.sh extract' > /dev/null; do sleep 5; done

# Right — exclude self by PID, or use pidof, or check the lock file.
until ! pgrep -fa 'build-ocaml.sh extract' \
        | grep -v "^$$\b" \
        | grep -v 'pgrep\|grep' \
        | grep -q .; do sleep 5; done

# Even better — check the build's own marker file
until [ ! -f /home/user/factoidal/formal/fstar/.build-running ]; do sleep 5; done
```

### 7. SessionStart and PostToolUse hooks

For things that should happen every session (env activation, lock
sweep, worklog dump), use `.claude/settings.json` hooks rather than
remembering to do them manually. The repo already has a SessionStart
hook (`tools/sandbox-bootstrap.sh`) and a PostToolUse hook that
reminds about rule #18 worklog updates. Extend those rather than
inventing new conventions.

## The combined pattern

For any long autonomous batch:

1. Stamp `date -u` and the job ID in `.claude-worklog.md` when you
   kick the job. Note the expected duration and the cap.
2. Fire the job with `Bash run_in_background`. Use a generous
   `timeout` cap (e.g. 30 min for a heavy build, 10 min per
   rule #17 for ad-hoc parse runs).
3. Add a `Monitor` with a filter that covers BOTH per-step progress
   AND terminal-state markers (success, failure, the timeout exit
   codes 124/143).
4. Continue with parallel work. Don't poll.
5. At every `date -u` checkpoint, if it's been more than 2× the
   expected duration with no Monitor events, treat the job as dead:
   check ps, check log mtime, restart if needed.
6. On restart: clean stale locks, bump cap, re-stamp the log.

## Quick reference

| Situation | Tool | Failure mode it prevents |
|---|---|---|
| One-shot wait for build to finish | `Bash run_in_background` | Sitting on a long blocking call |
| Streaming per-step progress | `Monitor` with grep filter | Treating silence as progress |
| Periodic rule reminders | `PostToolUse` hook | Forgetting rule #18 worklog dumps |
| Always-active env setup | `SessionStart` hook | Forgetting `eval $(opam env)` |
| Wall-clock check | `date -u` + log mtime | Misjudging elapsed time |
| Lock cleanup on restart | explicit `rm` after `pgrep` | "Build already running" loop |

## The one rule

If a build job has been running for more than its cap with no
notification, it is dead. Restart with stale-lock cleanup and a
Monitor.

## See also

- [`workflow-gotchas-debugging`](../workflow-gotchas-debugging/SKILL.md)
  for the ten dev-loop hazards we've actually hit and their recovery
  steps.
- CLAUDE.md anti-patterns #17–#22 (timeout caps, no `tail -N`
  truncation, worklog discipline, parallel-work pickup).

## Overnight operation patterns (2026-07-04, ~12h autonomous run)

- **Heartbeat timer**: when scheduled triggers are unavailable (MCP
  approval friction), a background `sleep 3300; echo HEARTBEAT` is a
  self-wakeup — its completion notification re-invokes the session.
  Re-arm it every time it fires. 55 min balances responsiveness
  against noise.
- **Stale-timer discipline**: every poll/timer you background will
  fire eventually, often after the thing it watched already finished.
  On wake, identify the LIVE task first (the long-running build or
  agent), treat other notifications as no-ops, and do not re-print
  status for stale ones. A timer whose command ends in a conditional
  (`ls file && echo X`) exits non-zero when the condition is false
  and arrives labelled "failed" — read the output, not the label.
- **Container-restart drill**: the workspace, opam switch, .checked
  cache, and pushed branches survive; RUNNING processes and their
  locks do not. On the restart notice: `git status` (tree intact?),
  check toolchain (`fstar.exe`, `wasm_of_ocaml` present?), remove
  stale `.build-running`, relaunch the interrupted chain from its
  last completed phase (logs in `.claude-runs/` say where it died).
  Killed subagents: check their last message for confessed
  in-flight damage (one clobbered a committed file and said so),
  verify with git, then re-dispatch with a tightened brief.
- **Cache-window pacing**: prefer one long timer over many short
  polls; when a build phase reliably takes ~10 min, one 9-10 min
  timer beats three 3-min ones (less context burn, same latency).

