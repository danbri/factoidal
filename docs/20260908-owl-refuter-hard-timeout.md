# OWL refuter hard native timeout — 2026-09-08

This work is a bounded harness repair for the OWL DL completion tracked in
https://github.com/danbri/factoidal/issues/617 and the executable-to-calculus
proof gap tracked in https://github.com/danbri/factoidal/issues/586. It does
not change the tableau search semantics or establish SROIQ completeness.

## Problem

`Harness/OwlProbe.lean` previously put the pure refuter in an `IO.Task` and
stopped waiting at `--refute-ms`. Lean cannot interrupt that pure work. A
one-second caller deadline on the slow `WebOnt-description-logic-502` case
returned to the judge, but the native runtime then waited for the abandoned
worker at process shutdown. The observed whole-process time was 110.94
seconds. The configured 20-second value therefore was not an actual native
process bound.

## Design

Each bounded refuter call now starts a hidden worker mode of the same
`l4owl-probe` executable in a new process group. The parent polls the OS child
against `IO.monoMsNow`. If the child has not exited by the deadline, the parent
terminates the process group and calls `wait`, so the child is reaped before
the judge continues. Lean's POSIX runtime stores the `setsid` flag on the
child and implements `Child.kill` as `killpg(pid, SIGKILL)` when that flag is
set; see the official
[process runtime source](https://github.com/leanprover/lean4/blob/master/src/runtime/process.cpp).
The hidden worker does not spawn another external process, but process-group
termination keeps that property robust if its implementation later does. A
timeout remains an indeterminate result and cannot create a pass.

Graphs cross the process boundary as RDF 1.2 N-Triples in secure temporary
files. Before serialization, every complete blank-node identifier is encoded
with `bnodeScopePrefix [identifier]`. This injective syntax-safe alpha-renaming
preserves co-reference and distinct identifiers and reaches blank nodes inside
RDF 1.2 triple terms. The worker parses one serialized triple per physical
line with the existing N-Triples parser, then reverses its tail accumulator.
This preserves the graph list's order and duplicate triples. A compiled guard
covers duplicate/order preservation, typed, language-tagged and directional
literal fields, a nested triple term, and an abstract blank-node identifier
that is not legal concrete N-Triples syntax.

The deadline includes executable startup, child-side wire parsing, and the
refutation. Parent-side serialization and the temporary-file write happen
before the deadline. A serializer, parser, or worker-exit error is reported as `REFUTER-WIRE`
or `REFUTER-WORKER` and withholds the verdict. A spawn or wait exception
propagates as an IO failure. None is mapped to inconsistency or entailment.

This is native harness process isolation. It is not used by the public Wasm
API, whose host must enforce its own wall-clock policy.

## Checks

`lake build l4owl-probe` passed 104 jobs. The generated C contains the direct
`Refute.refute` call in `refuteWorkerMain`; the parent `refuteBounded` path
serializes and calls `runRefuteChild`. The per-record wire fold compiles to a C
loop (`goto _start`) rather than input-sized native recursion.

A fresh post-resume focused run used a one-case catalog containing
`WebOnt-description-logic-502`:

```text
REFUTER-WALLCLOCK WebOnt-description-logic-502: killed and reaped after 1000 ms
HARNESS-DIAG-OWL factoidal-502-focused.rdf: ... refuter_timeouts=1 ... wall_ms=1034
real 1.24
user 1.03
sys 0.01
```

The parent explicitly called `wait` after `kill`; the focused process used
1.03 seconds of CPU and exited in 1.24 seconds. Process listing was not a
usable second check on this host because `pgrep` reported that the system
monitor service was unavailable. A 128-unit `type-inconsistency.rdf --dl`
smoke run kept the existing 118 pass,
9 fail, 1 skip result, reported four one-second timeouts, and the whole process
exited in 8.00 seconds rather than joining abandoned workers.

The wire scaling probe generated ordered graphs with distinct unsafe raw blank
node identifiers. It measured:

| Triples | Wire bytes | Encode | Decode |
| ---: | ---: | ---: | ---: |
| 1,000 | 123,349 | 13 ms | 80 ms |
| 2,000 | 253,349 | 27 ms | 165 ms |
| 4,000 | 513,349 | 51 ms | 324 ms |

These measurements cover the process wire, not the refuter's per-visit cost.
The hard timeout contains that cost; it does not make the search faster.
The temporary measurement source and raw output are
`/private/tmp/OwlWirePerf.lean` and
`/private/tmp/owl-wire-perf-20260908.log`; the focused timeout output and
external timer output are `/private/tmp/owl-hard-timeout-502.log` and
`/private/tmp/owl-hard-timeout-502.time`.
