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

### 6b. The detached-build-script recipe (and the absolute-log trap)

The reliable way to run a 15-25 min extract+compile without foregrounding
it: write a small script, launch it `setsid`-detached, and wait on its
completion MARKER — not on process liveness. The recipe, and the two bugs
that silently break it:

```bash
#!/bin/bash
cd /home/user/factoidal
# (1) opam env does NOT survive a container restart — set PATH EXPLICITLY.
export PATH="/root/.opam/fstar/bin:$PATH"; eval $(opam env --switch=fstar) 2>/dev/null
export PATH="/root/.opam/fstar/bin:/opt/node22/bin:$PATH"
rm -f formal/fstar/.build.lock formal/fstar/.build-running   # always, first
# (2) LOG MUST BE ABSOLUTE. The script `cd`s into formal/fstar; a RELATIVE
#     log path then resolves under formal/fstar/, so every `echo RC >>`
#     after the cd writes to a DIFFERENT (or nonexistent) file. Symptom:
#     the log you read is nearly empty (only the pre-cd lines + a final
#     marker), no EXTRACT_RC/COMPILE_RC, and you wrongly conclude "the
#     build didn't run" when it ran fine and wrote its RCs elsewhere.
LOG=/home/user/factoidal/.claude-runs/mybuild.log; : > "$LOG"
cd formal/fstar
RC=0; timeout 1400 ./build-ocaml.sh extract >> "$LOG" 2>&1 || RC=$?
echo "EXTRACT_RC=$RC" >> "$LOG"; [ $RC -ne 0 ] && { echo FAIL >> "$LOG"; exit 1; }
RC=0; timeout 1400 ./build-ocaml.sh compile >> "$LOG" 2>&1 || RC=$?
echo "COMPILE_RC=$RC" >> "$LOG"
echo "DONE" >> "$LOG"
```

Launch + wait on the marker, not the process:
`setsid bash mybuild.sh >/dev/null 2>&1 </dev/null &` then poll for `DONE`.

**Liveness by lock + `/proc` cwd, NEVER by log timestamps.** A healthy
extract writes to per-step logs, so the TOP log looks quiet for minutes —
that is NORMAL, not a hang. Judge alive by: the `.build.lock` is held AND
`readlink /proc/<pid>/cwd` for the build pid is under `formal/fstar`. When
you must kill ONE build among several (e.g. a stray worktree build), select
by that `/proc/<pid>/cwd` match, never by `pkill -f build-ocaml` (which
also matches your own waiter's argv and sibling builds).

**Glue-patch changes need `extract`, not `compile`.** `build-ocaml.sh
compile` does NOT re-apply `experimental_ocaml_glue/*.sh` /
`ocaml-patches.sh`. After editing any `.fst` OR any glue patch, run
`extract` (which re-applies patches) then `compile`. A patch whose `sed`
anchor you deleted will WARN "anchor not found" — usually cosmetic (a dead
hook), but confirm via the suite gates, not the warning count.

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


## Never end a turn with in-flight work and no armed wakeup (2026-08-06, the half-day stall)

The night of 2026-08-05 ended with three things in flight: a full
rebuild+suite gate batch (background bash), and two proof/test agents
finishing in worktrees. The turn ended relying on task-notifications
to continue the work. The session then idled; the harness suspended
it; the background bash job was KILLED mid-run (its log truncates at
22:46 with no final RC echo), and no notification ever re-woke the
session. Work resumed only when the owner arrived the next morning —
roughly twelve hours in which the remaining ~40 minutes of work
(harvest two finished agents, re-run one gate, commit) sat untouched.
The owner's read was correct: "you put down your tools."

Rules, each paid for that night:

1. **A pending task-notification is NOT a wakeup guarantee.** It
   fires only into a live session. If the session suspends first, the
   notification and the background job both die. Stop-hooks and goal
   hooks are the same: they gate STOPPING, they cannot resurrect a
   suspended session.
2. **Before ending ANY turn with unfinished in-flight work, arm
   `send_later`** (claude-code-remote MCP; survives container
   restarts, granularity one minute). 30-60 minutes out, message
   written to your future self with: what was running, where its
   logs/worktrees are, what "done" looks like, and the instruction to
   re-arm if anything is still open. Re-arm on every wake until the
   queue is empty. Cost: one tool call. The alternative cost,
   measured: half a working day.
3. **Long background bash jobs are mortal in a way agents are not.**
   Prefer: (a) finish long builds inside an active turn with Monitor
   when feasible; (b) otherwise accept the job may die and make death
   DETECTABLE — end every script with an unconditional RC echo
   (hazard #21 rule 4: a log without its final RC line means "killed
   mid-run", never "tail cut off") and make it RESUMABLE (staged
   steps, committed checkpoints).
4. **The last act of an autonomous evening is a handoff note to
   yourself**, not a status message to the owner. The status message
   is for the owner; the send_later payload is the machine-readable
   version with paths and next actions.

### The cron heartbeat (owner-requested, 2026-08-06)

One-shot `send_later` wakeups cover known waits; they do not cover
the wakeup you forgot to arm. The floor under everything is a
recurring cron trigger (`create_trigger`, self-bind, minimum interval
hourly) whose prompt is a standing checklist: check processes, check
worktrees, harvest finished agents, commit certified results,
dispatch next unblocked work, push — and explicitly "do NOT invent
work" when idle. Sessions fired by the trigger may lack the
scheduling MCP tools; that is fine — the recurrence itself is the
safety net, no re-arming needed from fired turns. Pause or delete
the trigger when the program it serves completes (`list_triggers` /
`update_trigger enabled:false`) — a heartbeat that outlives its work
becomes noise the owner pays for.

### Wakeups check liveness; dispatch judgment is a separate duty (2026-08-06 evening)

The cron heartbeat prevented every recurrence of the overnight stall —
but for five consecutive firings the session woke, found the running
jobs healthy, classified all remaining proof work as "blocked behind
the gate build", and went back to sleep with ONE task running. The
classification was wrong: a build in the MAIN checkout never blocks
proof dispatches in WORKTREES (separate repository copies; the only
shared resource is CPU, and `nice` handles that). The owner caught it
with "why only one running task".

Rule: on every wakeup, "is anything dispatchable?" must be answered
against the REAL blockers only — a red main tree, or a missing
prerequisite theorem/file. "A build is running" and "a gate has not
certified yet" are not blockers for worktree-isolated proof work.
When the pipeline is at one task and the queue is non-empty, the
burden of proof is on NOT dispatching.
