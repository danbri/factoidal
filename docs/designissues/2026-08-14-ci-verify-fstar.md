# CI never runs `make verify` — issue #436

## What CI does today (read before this change)

Workflows in `.github/workflows/`:

- `check-extraction.yml` — PR gate on `.fst` / `build-ocaml.sh` /
  `ocaml-patches.sh` changes. Runs `./build-ocaml.sh extract` then
  `./build-ocaml.sh compile`. **Never runs `make verify` or any
  `fstar.exe` invocation outside of extraction.** `build-ocaml.sh
  extract` DOES call `fstar.exe --codegen OCaml` per module, which
  does type-check that module — but only for modules in
  `build-ocaml.sh`'s hand-maintained `ALL_MODULES` array, and only
  when the incremental-extract manifest doesn't skip it (see below).
  No `.checked` cache in this workflow — every PR verifies whatever
  `build-ocaml.sh extract` verifies, cold.
- `w3c-tests.yml` — push-to-`main`/`claude/main` + nightly schedule.
  Builds native/JS/wasm and runs the W3C suites. Has a `.checked`
  cache (`actions/cache`, key = `hashFiles('formal/fstar/*.fst',
  '*.fsti')`). Same extraction-only verification as above.
- Neither workflow calls `make verify`.

### The gap, confirmed on disk (not asserted)

`build-ocaml.sh`'s `ALL_MODULES` array names 216 modules.
`formal/fstar/*.fst` on disk has 231 files. The 15 present on disk
but ABSENT from `build-ocaml.sh`'s list — so never even
extraction-checked by CI — are:

```
Parser.FastString.Axioms
Parser.FastString.BaseCases
Parser.FastString.RoundTripLemmas
Parser.NTriples.Locality
RDF.Entailment.RDFS.Completeness
RDF.Entailment.RDFS.FixedPoint
RDF.Indexed.Completeness
RDF.NQuads.Streaming
RDF.NTriples.RoundTrip
RIF.Core.Refinement
SPARQL11.Algebra.BGPRefinement
SPARQL11.EntailmentRegime.RDFS
SPARQL11.Parser.AskBgpRoundTrip
SPARQL11.Parser.TokenRoundTrip
SPARQL11.Expression.Refinement
```

This matches issue #422's 15-module sweep exactly (`RDF.CottasStore.
PageCache.Bounds.fst` — #422's own example — is on disk and IS in
`build-ocaml.sh`'s list, but many of its proof-only siblings are not:
these 15 are largely `.Refinement`/`.Completeness`/`.RoundTrip`
theorem modules that produce no extracted `.ml` a consumer calls, so
nobody ever added them to the extraction list — but F* still needs
to type-check them, and nothing does).

`formal/fstar/Makefile`'s `verify` target does NOT have this gap: `ALL_FST
:= $(sort $(wildcard *.fst))` derives its module list from the
directory listing, so it already covers all 231 modules including
the 15 above (confirmed by issue #319's landing, which is what
caught `RDF.CottasStore.PageCache.Bounds.fst` in the first place).
**`make verify` already exists and already has full-corpus
coverage. It has just never been wired into CI.**

## Design

Add a new workflow, `verify-fstar.yml`:

1. **What it runs**: `make -j$(nproc) verify` in `formal/fstar/`,
   using the Makefile's wildcard-derived `ALL_FST` target — no
   parallel module list to maintain, no risk of the #422 gap
   reopening as new modules get added (a new `.fst` is automatically
   in scope).
2. **Caching**: reuse the SAME `actions/cache` mechanism already used
   by `w3c-tests.yml`, not a new mechanism. Two layers:
   - `~/.opam` cache, same key pattern as the existing workflows.
   - `.checked` cache, key = `fstar-checked-verify-${{ runner.os }}-
     ${{ steps.versions.outputs.fstar }}-${{
     steps.versions.outputs.z3 }}-${{ hashFiles('formal/fstar/*.fst',
     'formal/fstar/*.fsti') }}`, restore-keys prefixed to the
     toolchain-version segment (P4's proposed key fix from
     `skills/fast-verify-extract/SKILL.md` — toolchain version is
     now IN the key, so a `.checked` from a different F*/z3 build is
     never restored and silently rejected module-by-module).
   - Deliberately a SEPARATE cache key namespace
     (`fstar-checked-verify-...`) from `check-extraction.yml`'s
     `fstar-checked-...` and `w3c-tests.yml`'s — those two write
     `.checked` files that come from `build-ocaml.sh extract`'s
     partial module list; mixing that into this job's cache would
     under-warm it for the 15 modules extract never touches. Separate
     namespace, same `actions/cache` action, same restore-keys
     pattern — reuse of the *mechanism*, not literal key-sharing of a
     narrower cache.
   - `formal/fstar/*.fst.checked` is git-ignored and per-module
     content-digest keyed (not mtime), so a stale restore from an
     older commit is harmless: F* validates each `.checked`'s digest
     against its current source + dependency closure and only
     re-verifies the modules that actually changed. This is the same
     property that makes `w3c-tests.yml`'s existing cache useful on
     .fst-light pushes.
3. **Why not pull from the `checked-cache` orphan branch instead**:
   that branch is the session-restore mechanism for interactive
   sessions/local containers (`tools/install-toolchain-cache.sh` step
   4b), gated by the "gates-green snapshot only" rule in
   `skills/session-restore/SKILL.md`. Reusing it here would couple
   a CI gate's cache freshness to whenever a human/agent last pushed
   a snapshot from a passing local run — an indirection this gate
   should not depend on. `actions/cache` is already GitHub Actions'
   own mechanism, already used by two sibling workflows in this repo,
   and self-refreshes on every green run with no separate push step.
   That is "reuse the existing mechanism" read as "use the pattern
   this repo already established for CI," not as "pull from the
   branch meant for a different consumer."
4. **Parallelism**: `make -j$(nproc) verify`. Safe per
   `skills/fast-verify-extract/SKILL.md`'s concurrency rules — make
   owns one writer per `.checked` target via the dependency-ordered
   `.depend` file (`fstar.exe --dep full`), so concurrent `fstar.exe`
   processes only ever run on modules whose prerequisites are already
   validated. This is NOT the "concurrent ad-hoc fstar.exe" hazard the
   skill warns about (that hazard is backgrounded `cmd1 & cmd2 &` fan-out
   with no target ownership) — it's the documented-safe `make -j` path.
5. **Trigger + honest scope statement**: `pull_request` on
   `formal/fstar/**.fst` / `**.fsti` / `Makefile` changes, so it gates
   every PR that touches the proof corpus, PLUS a nightly full run
   (`schedule`) as a safety net so a cache-poisoning or toolchain-drift
   issue doesn't hide silently between PRs that happen to touch few
   modules. This IS full-corpus coverage on every triggering PR (`make
   verify`'s target list is the whole corpus, not a diff) — the
   `.checked` cache only changes how much of that work is FREE, never
   how much is CHECKED. A PR that changes one leaf module still gets
   all 231 `.fst.checked` targets built (230 from cache validation,
   ~1 genuinely reverified) and the job still fails if any one of
   them fails. So there is no "verify-changed-only" narrowing here —
   full coverage on every run was achievable and is what's shipped.
6. **Failure semantics**: the Makefile's own rule already fails hard
   — `%.fst.checked: %.fst` has a `test -f $@ || exit 1` guard against
   F* returning 0 without writing `.checked` (Warning 247), and any
   `fstar.exe` non-zero exit fails that make target, which fails
   `make -j verify`, which fails the job. No `continue-on-error`.

## What ships

`.github/workflows/verify-fstar.yml` (new).

## Validation (see report) — two runs, both against the exact command
the workflow executes locally: (a) clean tree, real wall-clock,
expected PASS; (b) one module holding a deliberately false lemma in
a throwaway scratch copy (never committed), expected FAIL.
