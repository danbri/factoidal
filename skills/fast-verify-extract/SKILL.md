---
name: fast-verify-extract
description: Make the F* verify + OCaml extract + compile + test loop fast via .checked caching, targeted single-module rebuilds, and safe parallelism. Use when an edit-verify-extract cycle feels slow, when deciding whether to run a full ./build-ocaml.sh vs a targeted rebuild, when wiring caches into CI or the session container, or before dispatching parallel verification work. Every claim below is marked CONFIRMED (seen in --help output, script source, or measured here) or PROPOSED (not yet verified in this repo).
---

# Fast verify + extract + compile cycles

Every fix in this project pays the full loop: F\* verification (SMT),
OCaml extraction, native compile, W3C suites. The loop is the
project's measurement instrument — if it is slow we fly blind. This
skill documents which caches exist, what invalidates them, the
fastest correct loop for a single-module change, and the concurrency
rules that keep parallelism from corrupting the caches (the
2026-05-07 incident — see
[workflow-gotchas-debugging §2](../workflow-gotchas-debugging/SKILL.md)).

Toolchain measured against: F\* 2026.03.24 (commit 70671ff), z3
4.13.3, OCaml 4.14.1, opam switch `fstar`, 4-core Linux container,
2026-07-03. Timings below will scale but the mechanisms are
version-pinned facts.

## The fast loop for a single-module change

You edited `Foo.fst` and want a verified, extracted, compiled,
tested result without paying the full pipeline.

Precondition: the worktree has a warm `.checked` population — every
module `Foo.fst` depends on has a valid `*.fst.checked` next to its
source. One full `./build-ocaml.sh extract` per worktree establishes
this (each module in the loop is a command-line target, so each gets
its `.checked` written — CONFIRMED from the loop source, lines
348-351 of [build-ocaml.sh](../../formal/fstar/build-ocaml.sh)).

```bash
eval $(opam env --switch=fstar)     # iron rule #12 — every shell
cd formal/fstar

# 0. Don't race a build already in flight (the flock only guards
#    build-ocaml.sh, NOT ad-hoc fstar.exe — check the marker):
test ! -f .build-running || { echo "build in flight; wait"; exit 1; }

# 1. Verify just Foo (rlimit-capped per rule #17). With deps'
#    .checked valid, F* loads them without re-verification and
#    writes Foo.fst.checked on success:
timeout 600 fstar.exe --z3version 4.13.3 --cache_checked_modules Foo.fst

# 2. Extract just Foo. With Foo.fst.checked now valid this is
#    sub-second — F* loads the .checked and emits only Foo's .ml
#    (CONFIRMED: 0.64s for Parser.IRI, one .ml file emitted):
timeout 600 fstar.exe --z3version 4.13.3 --cache_checked_modules \
  --codegen OCaml --odir ocaml-output Foo.fst

# 3. Re-apply the patch pipeline. Extraction overwrote the patched
#    Foo.ml; the patches are idempotent over the whole directory
#    (build-ocaml.sh runs them unconditionally after every extract):
./ocaml-patches.sh ocaml-output

# 4. Recompile. The compile step's needs_rebuild check sees the
#    newer .ml and rebuilds; unchanged binaries are skipped only
#    when NO source is newer, so this rebuilds all binaries (see
#    proposal P3 below for why that is the current cost):
./build-ocaml.sh compile

# 5. Run only the affected suites. Map the diff to suites with the
#    dispatcher, or name the suites you know are relevant:
bash ../../tools/dispatch_test_suites.sh --diff HEAD~1 HEAD
cd ocaml-output && ./w3c_runner bind aggregates   # example
```

Caveats, all CONFIRMED by experiment or source:

- Step 1 writes `Foo.fst.checked` **only if every dependency has a
  valid `.checked`**. Otherwise F\* re-checks the deps in memory,
  still verifies Foo, but emits Warning 247 ("checked file was not
  written") and the next run pays the same cost again. If you see
  Warning 241/247, verify the named dependency first (it must be a
  command-line target to get its own `.checked`).
- If you edited a module that others depend on, their `.checked`
  files are now stale (digest mismatch cascades). Re-verify the
  dependents you care about, or fall back to
  `./build-ocaml.sh extract` which walks the whole ordered list.
- Steps 1-2 bypass build-ocaml.sh's "no silent failures" grep for
  `Extracted module` — eyeball the output yourself.
- For pure proof iteration (no extraction needed), the
  [fstar-mcp](../fstar-mcp/SKILL.md) server gives interactive
  typecheck queries without batch fstar.exe startup cost.
- New module? It must be added to the three lists in build-ocaml.sh
  (extract loop, `COMMON_MODULES`, `FSTAR_MODULES`) — see
  [workflow-gotchas-debugging §3](../workflow-gotchas-debugging/SKILL.md).

## Cache layers

| Layer | What | Where | Invalidated by | Win |
|---|---|---|---|---|
| `.checked` files | Serialized typechecked module (`--cache_checked_modules`) | `formal/fstar/*.fst.checked`, next to source; gitignored | Source **content digest** change (not mtime — CONFIRMED); any dependency's `.checked` going stale (cascades — CONFIRMED); F\* version change (PROPOSED, from F\* release practice; not tested here). NOT invalidated by `--z3rlimit_factor` change (CONFIRMED) | RDF.Bytes: 6.4s cold → 0.5s warm, 12x (CONFIRMED) |
| ulib `.checked` | Pre-checked F\* stdlib | `~/.opam/fstar/lib/fstar/ulib.checked/` | Reinstalling/upgrading the fstar opam package | Ships with the package; stdlib never re-verified (CONFIRMED via --dep output paths) |
| `.hints` files | Recorded z3 unsat cores for proof replay (`--record_hints` / `--use_hints`) | `Foo.fst.hints` next to source (or `--hint_dir`); JSON text | Query hash mismatch per top-level name; z3 version or `--z3seed` drift can break replay (PROPOSED) | **Measured negative on every module tested — REJECTED for the pipeline, 2026-07-04** (CONFIRMED, 4 modules incl. SPARQL11.Algebra, 2-3 repeats each; full table in P5). Slowdowns +20% to +80%; a hint MISS degrades gracefully (rc=0, warning line, plain-verify speed) |
| Incremental-extract manifest | Per-module **dependency-closure digest** recorded from the last successful extract; `--force-full` bypasses it | `ocaml-output/.extract-state/manifest.tsv` — **tracked in git**, despite `.gitignore` claiming otherwise (see below) | Any change to the module's own `.fst`/`.fsti` **or to anything in its transitive in-list dependency closure** (CONFIRMED — see P2). Before 2026-07-29 a dependency-only change did NOT invalidate it, which was unsound for proofs (issue #320) | Skips fstar.exe invocation entirely (not just codegen) for modules genuinely unaffected by the edit — replaces the old flat "everyone after this point in the list" cascade. CONFIRMED via scratch harness, see P2 |
| Committed `.ml` + binaries | Extraction output + `bin/<platform>/` | git (iron rule #9) | Re-extraction; `ocaml-patches.sh` rewrites `.ml` in place | Fresh clone runs tests with no toolchain |
| Compile skip | `needs_rebuild_from_sources` mtime check over all `.ml` + consumer sources | build-ocaml.sh lines 523-532 | Any single `.ml` newer than any binary → **full** recompile of everything (CONFIRMED) | Skips all ocamlopt invocations on a no-op |
| CI opam cache | `~/.opam` via actions/cache | [w3c-tests.yml](../../.github/workflows/w3c-tests.yml), [check-extraction.yml](../../.github/workflows/check-extraction.yml) | Manual key bump only (static keys `opam-fstar-<OS>-v3` / `-v4`) | Skips ~10 min toolchain install (CONFIRMED present) |
| CI `.checked` cache | `formal/fstar/*.fst.checked` via actions/cache | w3c-tests.yml only — **absent from check-extraction.yml** (CONFIRMED) | Key = `hashFiles('formal/fstar/*.fst','*.fsti')`; restore-keys prefix warms partial hits | Workflow comment: heavy pipeline ~25 min → ~5 min on no-.fst pushes |

Per-phase wall-clock timing is now recorded on every `build-ocaml.sh`
run: `.claude-runs/build-timings.csv` gets one appended line per phase
(`extract-loop`, `patches`, `compile`, `test`, `js`, `wasm`,
`wasm-factoidal`) — columns `timestamp,phase,seconds,changed_modules`,
where `changed_modules` is the count of modules actually re-extracted
in that run (0 for a `compile`/`js`/`wasm`-only invocation). Use this
to see which phase actually dominates a given cycle instead of
eyeballing terminal scrollback.

Flags confirmed to exist in `fstar.exe --help` (F\* 2026.03.24):
`--cache_checked_modules` (`-c`), `--cache_dir <dir>`, `--cache_off`,
`--already_cached <selector>`, `--record_hints`, `--use_hints`,
`--use_hint_hashes`, `--hint_dir`, `--hint_file`,
`--detail_hint_replay`, `--dep <make|graph|full|raw>`, `--extract
'<Target:Selector>'`, `--quake N/M`, `--retry N`,
`--proof_recovery`, `--query_cache` (interactive mode only,
experimental), `--z3refresh`, `--z3rlimit`, `--z3rlimit_factor`,
`--z3seed`, `--z3version`. There is **no** `--z3threads` or any
in-process query-parallelism flag (CONFIRMED by absence from
--help). Parallelism is process-level only.

Hint-flag spellings re-confirmed against F\* 2025.12.15 (this
container's toolchain, 2026-07-04): `--record_hints`, `--use_hints`,
`--use_hint_hashes`, `--hint_dir <dir>` ("Read/write hints to
dir/module_name.hints"), `--hint_file <path>` (overrides hint_dir),
`--detail_hint_replay`, plus `--reuse_hint_for <toplevel_name>` and
the deprecated `--hint_info`.

## Dependency-driven parallel verification

`fstar.exe --dep full <roots>` emits make-format rules (CONFIRMED,
observed output):

```
Parser.IRI.fst.checked: Parser.IRI.fst \
    Parser.FastString.fst.checked <ulib .checked...>
Parser_IRI.ml: Parser.IRI.fst.checked
ALL_FST_FILES= ...
```

so a Makefile with one pattern rule turns the whole verification DAG
into parallel-safe targets:

```make
FSTAR = fstar.exe --z3version 4.13.3 --cache_checked_modules
%.fst.checked: %.fst
	$(FSTAR) $<
include .depend        # regenerate via: $(FSTAR) --dep full <roots> > .depend
```

Measured on 4 modules, 4 cores: `make -j4` cold 7.2s vs serial 11.8s
(CONFIRMED). The win grows with the width of the dependency graph;
the repo's ~90-module list is much wider than 4.

This is the standard F\* project layout (the
[Low\*/KaRaMeL manual](https://fstarlang.github.io/lowstar/html/Setup.html)
documents the same `--dep full` + `--cache_dir obj` +
`--already_cached 'Prims FStar ...'` pattern) — with a bash + `xargs
-P` scheduler in place of a generated Makefile, since P2's manifest
skip logic didn't map cleanly onto make's mtime staleness model (see
P1 below). [build-ocaml.sh](../../formal/fstar/build-ocaml.sh)'s
extract step now runs this: `--dep full` once, Kahn-layered, each
layer's modules through `xargs -P $BUILD_JOBS`, barrier between
layers (P1, implemented 2026-07-04 — full design + scratch evidence
below). [formal/fstar/Makefile](../../formal/fstar/Makefile) `verify`
now uses exactly this shape — `--dep full` filtered to local rules,
real `.checked` targets, `--cache_checked_modules` — over
`$(wildcard *.fst)` instead of a hand-written list, so it covers the
whole corpus and shares the cache with the extract pipeline (P7,
implemented 2026-07-29 for issue #319).

## Concurrency safety rules

1. **One build-ocaml.sh per worktree.** The script takes a
   non-blocking flock on `.build.lock` and exits 75 if another
   instance holds it (CONFIRMED, lines 76-84). Parallel *worktrees*
   are fine — the lock is per-worktree.
2. **The flock does not cover ad-hoc `fstar.exe` runs.** Before any
   manual verify/extract in a worktree, check for `.build-running`
   (the marker build-ocaml.sh writes on entry, removed on exit —
   CONFIRMED lines 87-89).
3. **Never run concurrent ad-hoc fstar.exe invocations over
   overlapping modules in one tree.** This is the 2026-05-07
   corruption: interleaved writers on the same `.checked` outputs
   cascade into bogus cache misses and "Unbound module" compile
   failures ([workflow-gotchas-debugging §2](../workflow-gotchas-debugging/SKILL.md)).
4. **Parallelism must go through `make -j` with distinct targets,
   not backgrounded ad-hoc processes.** make guarantees one writer
   per `.checked` target and orders writers after their
   prerequisites; concurrent *readers* of a dep's `.checked` are
   safe (CONFIRMED in the make -j4 experiment). Ad-hoc `cmd1 & cmd2 &`
   fan-out gives neither guarantee.
5. **Concurrent ocamlopt invocations race on `.cmi`/`.cmx` in
   `ocaml-output/`** (CONFIRMED as the stated reason for the lock,
   build-ocaml.sh header comment). Same rule: parallel compile needs
   per-target discipline (dune or a generated Makefile), not
   backgrounded ocamlfind calls in one directory.

## Measurements behind this skill (2026-07-03, this container)

- RDF.Format.fst (96 lines): cold 0.74s, warm 0.49s.
- RDF.Bytes.fst (356 lines): cold verify+cache 6.4s; warm 0.54s;
  `touch` only (mtime change, same bytes) 0.50s — digest-based, not
  mtime; content perturbation → full re-verify 6.2-7.2s.
- Hints on RDF.Bytes: `--record_hints` wrote a 21 KB JSON
  `RDF.Bytes.fst.hints`; re-verify after a comment-only edit took
  6.3s/6.7s plain vs 12.2s/12.7s with `--use_hints` and 12.3s with
  `--use_hints --use_hint_hashes`. `--detail_hint_replay` reported
  no failed cores — replay succeeded and was still ~2x slower. For
  this codebase's cheap queries (default 5-unit rlimit), hint-replay
  overhead exceeds the SMT it saves, on this module.
- Dep invalidation: appending a comment to Parser.FastString.fst
  made Parser.IRI's run emit Warning 241 ("stale — digest mismatch")
  and Warning 247 (Parser.IRI.fst.checked not rewritten); F\* only
  writes `.checked` for command-line modules whose deps all have
  valid `.checked`.
- Flag change: warm re-run with `--z3rlimit_factor 4` added did not
  invalidate the `.checked` (0.57s).
- Extraction from a valid `.checked`: 0.64s, emits only the
  command-line module's `.ml`.
- make -j4 over a 4-module DAG: 7.2s vs 11.8s serial.

Additional hints measurements (2026-07-04, F\* 2025.12.15, z3
4.13.3, scratch-isolated copies of the sources, warm dependency
`.checked`, comment-only edit invalidating the target's `.checked`,
2-3 repeats per cell — full table and the rejection decision in P5):

- `--record_hints` costs nothing over a plain verify (39.4s vs 39.8s
  on SPARQL11.Algebra) and hints files are small JSON (1.9 KB for
  SPARQL.JSON.Escape up to 274 KB for SPARQL11.Algebra).
- **`--record_hints` silently writes NO hints file when any
  dependency lacks a valid `.checked`** — the same gating as the
  Warning 247 `.checked` write suppression. Verify the deps as
  command-line targets first or the record pass is a no-op with no
  error.
- Scratch-experiment hazard: running `fstar.exe --include
  <real-tree> --cache_dir <scratch>` on a scratch copy of a module
  wrote the `.checked` files **next to the real tree's sources**,
  not into the scratch cache dir — contaminating the main worktree
  with `.checked` keyed to the edited scratch copy. For isolated
  experiments, copy ALL `.fst`/`.fsti` into the scratch dir and pass
  no `--include` of the real tree.

## Proposals not yet implemented

Everything below is PROPOSED. None of it is wired in; do not assume
any of it when reading build logs. Each item names the diff, the
expected win, and how to measure it. Measure before/after on the
same machine, cold and warm, with `date +%s.%N` brackets or
`hyperfine` if available — per the
[perf-benchmarking](../perf-benchmarking/SKILL.md) discipline,
speed claims come from measurements, not assertions.

### P1 — layered parallel verify + extract in build-ocaml.sh — CONFIRMED, implemented 2026-07-04

Implemented directly in the extract loop (no separate Makefile —
bash + `xargs -P` turned out sufficient; see "why not a generated
Makefile" below). The design, in order:

1. **Compute the DAG once.** `fstar.exe --dep full "${PRESENT_MODULES[@]}"`
   produces make-format dependency rules for the whole module list in
   one invocation (measured 0.265s on the real 96-module list,
   2026-07-04 — cheap enough that it does not threaten the incremental
   manifest's near-1s no-op case). The rules are joined (backslash
   line continuations merged) and filtered down to edges *between
   modules in our own list* — ulib/Prims/FStar.\* prerequisites are
   dropped; F\* resolves those from the pre-checked stdlib regardless
   of how we schedule our own modules.
2. **Kahn-layer the DAG.** Layer 0 = modules with no in-list
   dependency; layer k+1 = modules whose in-list deps are all already
   placed in an earlier layer. Measured on the real 96-module list:
   **7 layers, widths 23 / 25 / 15 / 15 / 9 / 7 / 2** — a wide, shallow
   DAG (the module list is dominated by independent parsers/formats;
   deep chains like `SPARQL11.Store -> RDF.CottasStore -> ...` are the
   exception, not the rule).
3. **Run each layer through a bounded worker pool.** `BUILD_JOBS`
   (env override, default `nproc`, clamped to never exceed it) via
   `printf '%s\n' "${layer_mods[@]}" | xargs -P "$BUILD_JOBS" -I{}
   bash -c 'extract_worker "$@"' _ {}`. `extract_worker` is an
   exported bash function doing exactly what the old inline loop body
   did per module (manifest hash skip-check, then
   `fstar.exe --codegen OCaml --cache_checked_modules`), but as a
   forked process it cannot share the parent's associative arrays — it
   reads `MANIFEST_FILE` directly for its own previous hash and writes
   its outcome (`SKIP`/`OK`/`FAIL` + hash) to a per-module status file
   under `ocaml-output/.extract-state/status/` for the parent to
   collect once the layer's xargs pool drains.
4. **Barrier between layers.** The parent waits for the whole layer
   (backgrounded `xargs | tee` pipeline + a 30s-tick heartbeat modeled
   on `run_with_heartbeat`, adapted to watch a whole layer instead of
   one `fstar.exe` call) before starting the next layer's loop
   iteration. This is what makes concurrency safe: modules in one
   layer depend only on modules an *earlier, already-fully-processed*
   layer wrote `.checked` for, so two concurrent `fstar.exe`
   invocations never race on the same `.checked` target — the
   2026-05-07 corruption hazard this skill's concurrency-safety rules
   warn about.
5. **Fail-fast at layer granularity, not module granularity.**
   `xargs` does not abort early on a failing item — it keeps
   launching the rest of the layer's queue — so every failure in a
   layer is collected and reported together; the *next* layer never
   starts once any failure is recorded (a downstream layer may depend
   on the failed module's `.checked`, so proceeding would just cascade
   confusing secondary failures).
6. **The incremental-extract manifest (P2) is untouched in shape.**
   `extract_worker` does the same source-hash-vs-manifest comparison
   inline, before spawning any process, for every module — the
   DAG/layering only changes *how* the modules that actually need
   fstar.exe get scheduled, not the skip logic itself.

**Why not a generated Makefile** (the shape floated when this was a
PROPOSED item): a Makefile would give the same one-writer-per-target
guarantee, but the incremental-extract manifest's skip decision needs
custom logic (source hash vs. a TSV, not mtime) that doesn't map
cleanly onto make's own staleness model without fighting it; the
layered-xargs design reuses the exact skip code already validated for
P2 and keeps the DAG-to-schedule step small and auditable in one
script instead of splitting the pipeline across a generated file.

**Scratch validation** (2026-07-04, no `--include` of the real tree —
see the contamination hazard below; all sources copied into a
`mktemp -d`): an 8-module mini-tree — `Parser.FastString.fst` (leaf),
`RDF.Format.fst`, `Util.Log.fst`, `RDF.Graph.Executable.fst`,
`RDF.List.Helpers.fst` (4 more independent leaves) in layer 0, and
`Parser.IRI.fst` / `Parser.Combinators.fst` / `SPARQL.JSON.Escape.fst`
(each `open Parser.FastString`) in layer 1 — confirmed by grepping
each file's real `open` statements first, not assumed.

- **(a) Layering matches the real dependency graph**: the harness's
  own `fstar.exe --dep full` + parse + Kahn-layer step produced
  exactly layer 0 = the 5 leaves, layer 1 = the 3 `Parser.FastString`
  dependents — matching the `open` grep by hand.
- **(b) Real concurrency**: layer 0's 5 modules showed overlapping
  start/end wall-clock timestamps (e.g. `RDF.Format.fst` 938.557 to
  939.472, `Parser.FastString.fst` 938.561 to 939.246, `Util.Log.fst`
  938.561 to 938.910, all mid-flight simultaneously); the layer's long
  pole was `RDF.Graph.Executable.fst` (182KB) at ~11.3s, and layer 1
  correctly waited for it before starting.
- **(c) Fail-fast at layer granularity**: injecting a forced failure
  into `Parser.FastString.fst` (layer 0) still let all 5 layer-0
  modules run to completion (4 succeeded, 1 reported failed) and then
  stopped — layer 1's 3 modules were never attempted, exit code 1.
- **(d) Identical output to sequential**: a fresh full extract
  (`FORCE_FULL=1`) at `BUILD_JOBS=4` vs. the same at `BUILD_JOBS=1`
  produced byte-identical `.ml` files for all 8 modules (`diff -rq`
  clean) and the same 8 `.checked` files (spot-checked via
  `sha256sum`).
- Warm no-op rerun (nothing changed): 0.227s for all 8 modules vs.
  15.449s cold — consistent with the existing P2 manifest behavior,
  now running through the layered scheduler instead of a flat loop.

**Real-tree no-regression check** (2026-07-04, `./build-ocaml.sh
extract`, no `--force-full`, nothing in any `.fst` changed): exit 0,
`Dependency DAG: 96 modules in 7 layer(s)`, `Extraction outputs
already up to date; no F* modules re-extracted (96 skipped)` — same
message format as before P1. Wall-clock was 3m30s (`real 3m30.671s`)
against a pre-P1 baseline of ~1s, with `user 1.214s + sys 0.396s ≈
1.6s` of CPU.

**That was diagnosed as CPU contention from an unrelated sibling
process. The diagnosis was wrong** (corrected 2026-07-29). The cause
was the per-layer barrier: it did `sleep 30` *before* re-checking
whether the layer's `xargs` child had exited, so **every layer cost a
flat 30 seconds** even when all of its modules were instant manifest
skips — and printed nothing, because the child exited during the sleep
and the loop broke before the heartbeat `echo`. The cost was therefore
invisible in the log. 7 layers x 30s = 3m30s, exactly the number
observed. `run_with_heartbeat` had the same shape for single
invocations.

Confirmed and fixed on a warm 189-module tree with nothing changed:

| | Wall-clock | CPU |
|---|---|---|
| before (15 layers x 30s of sleeping) | 8m18s | 27s |
| after (poll 1s, heartbeat every 30s) | **35.6s** | 23s |

Both loops now poll at 1s and emit a tick every 30s, so the heartbeat
cadence is unchanged and an all-skip layer costs about a second. The
lesson generalises: **when wall-clock hugely exceeds CPU in a build
step, suspect the build's own sleeps before blaming the machine.**

**Expected win, revised with real DAG shape in hand**: parallelism
helps in proportion to layer *width*, and is bounded by the DAG's
*critical path* (the longest chain of layers a single edit's
dependents must pass through), not by the total module count — this
is Amdahl's law applied to the dependency DAG rather than to
independent work items. Concretely: an edit to a wide-fanout hub
module (e.g. `RDF.Graph.Executable.fst`, referenced by dozens of
downstream parsers) re-verifies only that module plus its *own*
extraction (the P2 manifest does not force dependents to reprocess —
see P2's documented trade-off), so P1 buys little for a single-module
edit today. P1's payoff is a **cold or `--force-full` run**, or any
future scheme that does force true dependent re-verification: on the
real 96-module, 7-layer DAG, a 4-core box can in principle collapse
the widest layer (25 modules) into `ceil(25/4) = 7` sequential
slots instead of 25, but the *total* wall-clock win is capped by the
sum of each layer's slowest module (the critical path through the
7 layers), not by 96/4. Measure the cold case
(`rm -f *.fst.checked && ./build-ocaml.sh extract --force-full`)
before quoting a multiplier — not yet done in this container because
of the sibling-process contention above; re-run when the container is
idle.

### P2 — retire the mtime chain-dirty skip — CONFIRMED, implemented 2026-07-04

Implemented in [build-ocaml.sh](../../formal/fstar/build-ocaml.sh)'s
extract step. `EXTRACT_CHAIN_DIRTY` (which forced every module
*positioned after* any re-extracted module in the hand-ordered list to
re-run fstar.exe, regardless of true dependency) is gone, replaced by
an incremental-extract manifest.

**Design (current, after the 2026-07-29 soundness fix).**
`ocaml-output/.extract-state/manifest.tsv` records, per module, a
**dependency-closure digest** as of the last successful extract (one
line per module: `<fst-path>\t<sha256>`). The digest is sha256 over the
module's own source hash — `.fst` plus its sibling `.fsti` if present,
issue #293 — concatenated with the closure digests of every in-list
dependency, sorted. `LAYERS` is already topologically ordered, so one
pass computes them all; they are written to
`.extract-state/closure.tsv` because the extract workers are forked
processes that cannot read the parent's arrays. Before invoking
fstar.exe on module `M`, the loop skips the invocation entirely — no
fstar.exe process at all — when (a) `M`'s closure digest matches its
manifest entry, and (b) `M`'s `.ml` already exists in `ocaml-output/`.
`--force-full` bypasses the manifest and reprocesses everything.

`ocaml-patches.sh`'s per-patch idempotency guards (e.g.
`89_fast_string_primitives.sh`'s "already applied, skip" check) make
leaving an untouched, already-patched `.ml` in place safe: the
unconditional whole-directory patch re-run at the end of extract is a
no-op for it.

**The original justification was wrong — issue #320.** Until
2026-07-29 the skip was keyed on the module's OWN source hash, and this
document plus `build-ocaml.sh`'s comments recorded the reasoning as
settled. It ran: a comment-only edit to `Parser.FastString.fst` changes
`Parser.IRI.fst.checked`'s hash (F\* embeds each dependency's digest)
but leaves the extracted `Parser_IRI.ml` byte-identical, because codegen
output is a function of the module's own `.fst` plus the *names* it
calls, not the dependency's internal proofs; and the residual gap — a
dependency changing its extracted signature incompatibly — is caught
loudly at `ocamlopt`.

Every observation there is true. The conclusion is not. **The argument
is about extraction output, but the skip also suppresses
verification.** A dependency can change *semantically* while its
extracted signature stays identical; that invalidates any theorem an
unchanged dependent states about it, and precisely because the `.ml` is
byte-identical, `ocamlopt` has nothing to catch. The developer sees
green. This mattered little when modules mostly carried totality and
refinements; it matters now that `OWL.Semantics.Soundness.fst` and
friends state theorems about *other modules'* functions.

Demonstrated end-to-end against `build-ocaml.sh` (2026-07-29), not
argued:

```fstar
// ZZGap.Dep.fst
let bump (x:nat) : nat = x + 1
// ZZGap.Thm.fst  -- unchanged throughout
let apply_bump (x:nat) : nat = bump x
let lemma_bump_increases (x:nat) : Lemma (bump x > x) = ()
```

Change `bump` to `if x = 0 then 0 else x - 1` — same extracted type
`Prims.nat -> Prims.nat` — and re-run `./build-ocaml.sh extract`:

| | Own-hash skip (before) | Closure digest (after) |
|---|---|---|
| `ZZGap.Thm.fst` | `(up to date, skipped)` | re-verified |
| Re-extracted | 1 (190 skipped) | 2 |
| `Error 19 ... could not prove post-condition` | not reported | reported |
| `BUILD_STATUS` | `OK` | `FATAL: layer 1 had failures` |
| Exit code | **0** | **1** |

`ZZGap_Thm.ml` was byte-identical across the change, so `ocamlopt`
could never have caught it; verifying `ZZGap.Thm.fst` by hand gave the
Error 19 the build had swallowed.

**A second hole surfaced during the fix.** The worker treated the
presence of an `Extracted module` line in F\*'s output as success and
ignored `fstar.exe`'s exit code. F\* prints that line **even when
verification failed** — the run above exits 1, prints `Error 19`, and
still prints `Extracted module ZZGap.Thm` and writes the `.ml`. So a
module that failed to verify was recorded OK. The exit code is now the
authority. Without this, the closure-digest fix would have re-verified
the module and still gone green.

**Cost, honestly.** Editing a wide-fanout hub module
(`RDF.Graph.Executable`, `SPARQL11.Algebra`) now re-verifies its
dependents rather than silently skipping them. That is correctness work
the old scheme bought its speed by not doing. Leaf edits — most
format/parser modules depend on nothing else in the list — are
unaffected, and P1's layered parallel scheduler is what absorbs the hub
case. Manifests written before this change hold bare source hashes,
which match no closure digest, so the first run after it re-extracts
everything once and then self-heals.

**The manifest is tracked in git — CI was never protected from this.**
Issue #320 recorded a mitigating belief worth stating precisely because
it turned out to be false: *"clean CI checkouts do not restore the
manifest, so main-branch CI is likely unaffected."* Checked, not
trusted:

```
$ git cat-file -p HEAD:formal/fstar/ocaml-output/.extract-state/manifest.tsv | wc -l
189
```

`.gitignore` does carry
`formal/fstar/ocaml-output/.extract-state/` with the comment "Local
build-cache state, not a committed artifact" — but gitignore does not
untrack files already in the index, and these were added before the
rule. So **every fresh checkout restores the manifest**, and the
committed `.ml` files (iron rule #9) satisfy the other half of the skip
predicate. Confirmed by running `./build-ocaml.sh extract` in a copy of
the committed state with zero `.checked` files, i.e. what CI has:

```
Re-extracted modules: 10 (181 skipped as unchanged)
```

181 of 191 modules skipped with no `fstar.exe` process at all, in a tree
that had never been verified. The dev-loop/CI distinction the issue
hoped for does not exist; the gap was repo-wide. (The 10 that did run
are the 2 experiment fixtures plus 8 modules whose `.ml` is not
committed — see the note on `ocaml-output/` completeness in the
clean-room artifact.)

**What the digest still does NOT cover.** Do not read it as a proof
that a module's verification is current:

- A changed **patch script** moves no `.fst` hash, so an already-patched
  `.ml` is still left alone — see the invalidate-and-delete recipe just
  below.
- An **F\* or z3 version change** is not in the digest; `.checked`
  digests handle that separately.
- Dependencies **outside the module list** are not in the closure (ulib
  is pre-checked and version-pinned, so this is theoretical today).

**BUT the same guards mean EDITING a patch script does nothing to an
already-patched module.** The guard sees the old patch's marker in
the stale `.ml`, declares "already applied", and skips — your fixed
translation never lands, and every downstream binary keeps the old
behavior. This shipped on 2026-07-05: the #276 regex-quantifier fix
was edited into `63_regex_hash_uuid_stubs.sh`, the wave build ran
extract+compile clean, and only the unit-test battery caught that
`SPARQL11_Algebra.ml` still carried the broken translation (its
`.fst` was unchanged, so extraction skipped it and the guard
no-opped). **Rule: after editing any patch script, invalidate the
manifest entry of every module it patches and delete the stale
`.ml`** so extract regenerates it fresh and the patch applies to
virgin output:

```bash
sed -i '/^SPARQL11\.Algebra\.fst\t/d' ocaml-output/.extract-state/manifest.tsv
rm -f ocaml-output/SPARQL11_Algebra.ml
./build-ocaml.sh extract   # regenerates + patches fresh
```

(`--force-full` also works but reprocesses everything.) And keep a
unit pin on the patched behavior — the pin is what catches the
silent no-op.

Experiment transcript (scratch dir, F* 2025.12.15, z3 4.13.3):
warm no-op invocation on an unaffected module 0.6s; the SAME module
reverified after a genuine dependency change 3.3s (real SMT work, not
avoidable without a full dependency-DAG scheme — see P1). A 4-run
harness reproducing the manifest logic exactly showed: run 1 (no
manifest) both modules processed; run 2 (nothing changed) both
skipped; run 3 (`Parser.FastString.fst` edited) only it reprocessed,
`Parser_IRI.ml` unchanged byte-for-byte; run 5 (`--force-full`) both
reprocessed despite unchanged sources.

**What this does NOT fix**: a module that legitimately depends on a
changed leaf and whose own extraction is genuinely order-adjacent in
the list still pays real fstar.exe invocation + (if actually
type-affected) real SMT reverification cost — that cost is
unavoidable correctness work, not the waste this proposal targets.
True dependency-scoped parallelism/narrowing is P1's job (`--dep
full` + `make -j`), which remains PROPOSED.

Expected win (now measured directionally, not yet on the full
~95-module list): single-module edits far from the bulk of the
dependency graph (most of the ~95-module list — many parser/format
modules do not depend on each other) skip fstar.exe entirely instead
of paying chain-dirty's blanket "everyone after this point" cost.
Modules that ARE true dependents still pay real reverification, same
as before. Follow-up measurement: `time ./build-ocaml.sh extract`
after touching one leaf-ish module (e.g. a single parser format) vs.
one heavily-depended-on module (e.g. `RDF.Graph.Executable.fst`),
before/after this change, on the full list.

### P3 — compile the common modules once, link N times

The compile step runs 6-8 separate `ocamlfind ocamlopt` invocations,
each recompiling all ~90 `COMMON_MODULES` sources from scratch
(CONFIRMED from build-ocaml.sh lines 538-703; step starts with
`rm -f *.cmi *.cmx`). Fix options, in ascending ambition:
(a) one `ocamlfind ocamlopt -c` pass over `COMMON_MODULES` (or a
generated Makefile driving `-c` per module with `make -j`), then one
link per binary; (b) a dune project in `ocaml-output/` with a
library stanza for the extracted modules and executable stanzas per
consumer in `bin/*/`. Why it has not happened: the patch pipeline
rewrites extracted `.ml` in place after every extraction, and the
current script treats `ocaml-output/` as a scratch dir it can
`rm -f` clean — dune needs the directory to be a stable project and
the patch step to run before build. (a) has no such conflict and is
the low-risk first step.

Expected win: common-module compile cost drops from ~8x to ~1x plus
cheap links; with `make -j` on the `-c` step, divided again by
core count. Measurement: `time ./build-ocaml.sh compile` after
touching one `.ml`, before/after.

### P4 — CI cache fixes

- Add the `Cache F* .checked files` block (identical to
  w3c-tests.yml lines 289-295) to
  [check-extraction.yml](../../.github/workflows/check-extraction.yml),
  which today has no `.checked` cache at all — every PR verify runs
  cold (CONFIRMED). This is the cheapest single diff in this list.
- Include toolchain versions in the `.checked` cache key. The
  correct key is `fstar-checked-<OS>-<fstar-version>-<z3-version>-
  ${{ hashFiles('formal/fstar/*.fst', 'formal/fstar/*.fsti') }}`:
  a `.checked` written by a different F\* build is dead weight that
  gets restored, rejected module-by-module, and re-uploaded. Emit
  the versions in an earlier step (`fstar.exe --version`,
  `z3 --version`) into `$GITHUB_ENV`. Keep `restore-keys` on the
  `fstar-checked-<OS>-<fstar-version>-<z3-version>-` prefix so
  partial warms still work.
- Replace the static opam cache keys (`-v3`/`-v4`, which silently
  pin whatever was installed when the key was minted) with a key
  over the requested package set, e.g. a checked-in
  `ci/opam-deps.txt` hashed into the key.

Expected win: PR-gating check-extraction drops from full-cold verify
(~10-25 min) to near-warm on .fst-light PRs. Measurement: CI
wall-clock on a docs-only PR and a one-module PR, before/after.

### P5 — hints — MEASURED AND REJECTED, 2026-07-04

The experiment this proposal asked for was run (scratch-isolated
source copies, F\* 2025.12.15, z3 4.13.3, warm dependency
`.checked`, comment-only edit invalidating the target's `.checked`
so a real re-verify happens, 2-3 repeats per cell, run-to-run spread
under 5%). `--use_hints` replay was slower than plain SMT re-verify
on **every** module tested, including SPARQL11.Algebra — the largest
module in the repo and the case this proposal predicted hints might
win:

| Module (lines) | Plain re-verify | `--use_hints` | `--use_hint_hashes` | Hints file |
|---|---|---|---|---|
| SPARQL.JSON.Escape (97) | 0.73-0.76s | 0.89-0.91s (+20%) | — | 1.9 KB |
| RDF.NQuads.Serialize (152) | 0.79-0.82s | 0.95-1.01s (+21%) | — | 2.5 KB |
| RDF.Bytes (356) | 6.57-6.72s | 11.86-12.01s (+79%) | 12.27s | 21.6 KB |
| SPARQL11.Algebra (5777) | 40.53-40.63s | 60.68-61.38s (+50%) | 63.92s | 274 KB |

This matches the earlier single data point (RDF.Bytes, 2026-07-03)
and generalizes it: for this codebase's query profile, unsat-core
replay overhead exceeds the SMT time it saves, at every module size
tried. Even `--use_hint_hashes` (which *admits* queries whose hash
matches — laxer than replay) was no faster. Recording itself is
free (`--record_hints` 39.4s vs plain 39.8s on Algebra), and a hint
MISS degrades gracefully (rc=0, "Unable to open hints file ... ran
without hints" warning, plain-verify speed) — so the mechanism
works as documented; it just loses on time here.

**Decision: do not wire `--record_hints` / `--use_hints` into
build-ocaml.sh.** The `.checked` digest cache plus the
incremental-extract manifest (P2) remain the caching story. Note the
interaction that motivated this experiment: the manifest skips
fstar.exe entirely for unchanged modules, so hints could only ever
have helped the invocations that DO run (edited modules + true
dependents) — exactly the runs measured above, where they lose.

Revisit only if: (a) the F\* toolchain is upgraded and release notes
claim hint-replay improvements, (b) a module's proofs grow
`--z3rlimit` bumps / long-running quantifier-heavy queries (replay
wins are documented upstream for exactly those), or (c) CI needs
edit-tolerant warm verification that `.checked` cannot give and is
willing to pay the measured slowdown for it. Re-run the same
experiment before adopting; the harness lives in this repo's
session scratchpads and takes ~10 min to reproduce from the
description above (copy all sources to a scratch dir — see the
`--include` contamination hazard in the measurements section).

### P6 — warm the session container

[tools/sandbox-bootstrap.sh](../../tools/sandbox-bootstrap.sh)
currently installs fstar-mcp and symlinks binaries but deliberately
does not touch opam or caches (CONFIRMED). Worth persisting or
pre-baking, in value order: (a) the opam switch itself in the
container image (largest fixed cost, ~10+ min and network-dependent
to rebuild); (b) `formal/fstar/*.fst.checked` across sessions —
digest-keyed, so a stale restore is harmless, it just re-verifies;
(c) ~~`.hints` files if P5 adopts them~~ (P5 measured and rejected
hints, 2026-07-04 — nothing to persist).
A cheap interim: have the bootstrap kick a background
`make -j$(nproc) verify`-equivalent (post-P1) so the cache warms
while the session reads context, honoring rule #20 (background it)
and the `.build.lock` discipline.

Expected win: first verify of a session drops from cold to warm.
Measurement: time-to-first-successful-single-module-verify in a
fresh session, before/after.

### P7 — make `make verify` share the cache — IMPLEMENTED 2026-07-29 (issue #319)

Done, in [formal/fstar/Makefile](../../formal/fstar/Makefile), and it
turned out to be a correctness fix as much as a speed one.

The `MODULES` list named **six** modules while `README.md` said the
command "type-checks all F\* modules against the SMT solver". A
developer following the README got a green result having checked about
3% of the corpus. Issue #319 filed that as the review's cleanest
documentation overclaim.

What landed:

- `ALL_FST := $(sort $(wildcard *.fst))` — the module list is *derived
  from the directory*, so it cannot drift again. Adding a `.fst` adds
  it to `make verify` with no edit to the Makefile. (This also caught
  `RDF.CottasStore.PageCache.Bounds.fst`, present on disk and absent
  from build-ocaml.sh's `ALL_MODULES`, hence verified by nothing.)
- `FSTAR` now carries `--cache_checked_modules`, so the `.checked`
  files `make verify` writes are the ones `./build-ocaml.sh extract`
  consumes, and vice versa. Verify-then-extract no longer pays twice.
- `.verified` touch-markers are gone; the targets are real
  `%.fst.checked` / `%.fsti.checked` files.
- Ordering comes from `fstar.exe --dep full`, regenerated into
  `.depend` whenever any source changes, **filtered** to rules whose
  target is a local `.checked` with absolute-path (ulib) prerequisites
  stripped. Without that filter make sees rules for the F\* standard
  library's own `.checked` files inside the opam switch and may try to
  rewrite them. Measured: 198 local rules (190 `.fst` + 8 `.fsti`),
  zero opam targets in `make -n verify`.
- The recipe fails loudly if `fstar.exe` returns 0 without writing the
  `.checked` (F\* Warning 247 — a dependency lacked a valid `.checked`).
  Otherwise make would loop or, worse, report green.
- `make verify-smoke` preserves the old six-module fast check under a
  name that does not overclaim; `make verify-<Module>` does one module;
  `make verify-list` prints the corpus for anyone auditing a coverage
  claim.

`make -j$(nproc) verify` is safe because make owns one writer per
`.checked` target and orders writers after their prerequisites — this
is concurrency-safety rule 4 above, and the reason to route parallelism
through make rather than backgrounded `fstar.exe` fan-out.

Cost: a cold `make verify` re-proves the whole corpus (hours — see
`docs/clean-room/` for the measured figure). A warm run over an
unchanged tree is seconds. Point env-sanity checks at `verify-smoke`,
not `verify`.

## What this skill does NOT cover

- Toolchain install/repair — [fstar-env](../fstar-env/SKILL.md).
- Which suites to run and score reporting —
  [test-suites](../test-suites/SKILL.md).
- Runtime performance of the extracted engine —
  [perf-benchmarking](../perf-benchmarking/SKILL.md).
- Interactive proof workflows — [fstar-mcp](../fstar-mcp/SKILL.md).
