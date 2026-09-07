---
name: danbri-function-precrime-checkers
description: Catch a function's resource-scaling defects — stack depth, live memory, or time that grows with input size — by MEASUREMENT during the ordinary test run, before the defect causes a crash on a large input in production. Use when adding or changing any parser, decoder, serializer, closure, or fold over input-proportional data; when writing a new stress or corpus test; when a crash "only happens on big inputs"; and when deciding whether a green suite actually proved the code scales. The name is the owner's (2026-09-07); the idea is not well known under any standard name, so it keeps his.
---

# Function pre-crime checkers

A function that recurses, allocates, or loops in proportion to its input has a
crash latent in it that the test suite does not see, because the test files
are small. The disaster arrives later, on a real input, in a place with a
smaller budget than the test machine (a browser tab's ~1 MB stack, a phone's
memory, a request timeout). This session paid for that four times in two days:
a manifest decode that overflowed a tab at 36,000 entries, an XML pre-pass
that overflowed at ~7,000 characters, an F\* SHACL command that segfaulted at
2,610 shapes, and a wasm packer that leaked 15.6 bignums per quad. Every one
ran the whole existing suite green first.

The defect has a signature you can measure BEFORE it crashes: **a resource
whose peak tracks the input size.** Pre-crime checking is watching for that
correlation during the ordinary run, so the defect is a failing test at size
1,000 rather than a support ticket at size 1,000,000. It is the resource
analogue of the repository's score discipline: a green test that never
measured scaling is the resource version of an unlabelled numerator.

## The three resources and how each betrays itself

| resource | crash it causes | the signature | the fix pattern |
|---|---|---|---|
| stack depth | stack overflow / segfault | one frame per input item: a recursive call not in tail position | accumulator or worklist loop; keep the recursive spec, prove a `@[csimp]` twin |
| live memory | out-of-memory / allocator abort | bytes retained per input item after the item is processed | free per item; on wasm32 watch for `Nat`/`Int` literals ≥ 2^31 boxed per call (`skills/lean4-wasm-export` trap) |
| time | timeout / apparent hang | superlinear wall time: a nested scan, a quadratic dedup, a re-decode per query | index, sort-then-scan, or hoist the repeated work; measure, do not guess |

The stack and the quadratic-time defects look identical from a distance ("it
hangs on big inputs") and are cured differently. On 2026-09-07 the 36,000-entry
manifest was BOTH: a non-tail decode that overflowed a tab, and, separately, a
quadratic `uniqueArtifactKeys` that owned the 300-second wall time. Making the
decode tail-recursive fixed the overflow and moved the tab from crash to hang;
only the quadratic fix removed the hang. **Do not assume one cause.** Measure
which resource is scaling before you fix anything.

## Three checkers, cheapest first

### 1. The static scan (Lean: `tools/lean-tail-recursion-audit.py`)

Reads the compiled IR (`formal/lean4/.lake/build/ir/**/*.c`): Lean turns a
direct tail self-call into `goto _start`, so any self-call surviving as a real
C call is one stack frame per step. It lists every such function and every
mutual-recursion cycle, maps each back to its Lean declaration, and classifies
what bounds the depth: input length, input tree depth, a counter, or a fixed
structure. `--gate` fails the build on a NEW input-length recursion against
`tools/lean-tail-recursion-allow.txt`; `--fstar` runs the coarser scan over
`formal/fstar/ocaml-output/*.ml` (OCaml compiles only direct tail calls to
jumps too, so the same defect exists there — issue 674, the SHACL segfault).

Limits, stated in the tool: it cannot see recursion through higher-order
combinators (`List.foldr` and friends), inlined or specialised bodies, or the
memory and time resources at all. It is the first line, not the whole line.
Its own war story: the first version delimited a C body by a `}` in column 0
and truncated every body at its first nested block, reporting 24 recursions
instead of 833 and missing both known cases — an audit that finds almost
nothing is evidence about the audit's reach before the code (anti-pattern 28).

### 2. The canary run: the whole suite under a small budget

Run the existing corpora once with a deliberately small stack, so anything
input-proportional fails early WITH A NAME instead of on a giant input later:

- native probes: `ulimit -s 512` before the run;
- wasm: build the diagnostic module with `-sSTACK_SIZE=262144
  -sSTACK_OVERFLOW_CHECK=2` (emscripten then names the overflowing function
  instead of dying silently); the shipping module never carries these;
- Node: a small `--stack-size` on a worker thread (the main thread segfaults
  on macOS rather than throwing).

This needs no new inputs — the W3C corpora are already large enough to trip a
512 KB stack where an 8 MB one hid the defect. It is a CI job, not a debugger
session, and it covers the whole tree every run.

### 3. The scaling assertion: n, 2n, 4n

For each parser, decoder, serializer and fold, run inputs of size n, 2n, 4n
and record peak stack (a depth counter under a build flag, or `/usr/bin/sample`
stack sampling — the method of `docs/designissues/2026-09-05-shard-pack-profile-and-memory.md`),
peak RSS (`/usr/bin/time -l`), and wall time. Assert stack is FLAT in n, memory
is at most linear, time is at most linear (or the stated complexity). This is
what turns "it worked on the test files" into "it scales", which is the
property the suite was silently not testing. `tests/stack/` is the seed; the
assertion is what makes it a gate.

## The rule

1. **A function over input-proportional data is not done until its scaling is
   measured, not assumed.** A green suite on small files proves correctness on
   small files.
2. **Measure which resource scales before fixing.** Stack, memory and time
   present the same symptom and have different cures; one input can carry more
   than one defect.
3. **Keep the readable definition; prove the fast one equal.** The accumulator
   or indexed version runs; the structural version stays for the proofs; a
   `@[csimp]` lemma or a stated equality theorem ties them, so no round-trip
   theorem is lost. Never a bigger stack, never `partial def`, never
   `native_decide` to paper over it.
4. **The scan is the gate for stack; the canary and the scaling assertion are
   the gate for what the scan cannot see.** A new input-length recursion that
   is genuinely bounded goes in the allow-list with the reason, the way a
   local test override carries its issue URL.

## Pointers

- `tools/lean-tail-recursion-audit.py` (the scanner and `--gate`),
  `tools/lean-tail-recursion-allow.txt` (the reasoned exceptions).
- `tests/stack/` (the deep-input stress suite and the canary run).
- `skills/lean4-performance/SKILL.md` (the fix patterns, measure-first rule),
  `skills/lean4-proof-patterns/SKILL.md` (the `@[csimp]` twin recipe),
  `skills/lean4-wasm-export/SKILL.md` (the big-literal memory trap),
  `skills/perf-benchmarking/SKILL.md` (the `sample` timing method),
  `skills/fstar-module-style/SKILL.md` (extraction is not stack-safe; the
  OCaml scan).
- War stories: issues 670 (manifest decode and the quadratic dedup), 673 (XML
  line-ending pre-pass), 674 (F\* SHACL segfault), 658 (the wasm bignum leak).
