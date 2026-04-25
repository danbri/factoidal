# 2026-04-25 — Agent Dalet — rdfc10_runner build wiring audit + harden

## Symptom
Wave 8 build (`.claude-runs/rebuild-20260425-004630-wave8.log`) produced
`w3c_runner`, `factoidal`, `factoidal-http`, `owl_runner` — but **no
`rdfc10_runner`** binary at `bin/darwin-arm64/rdfc10_runner`. The
public test-results page logs `"rdfc10_runner not found — skipping
RDFC-1.0 suite"` because `generate-report.sh` (correctly) skips a
missing binary.

## Root cause
**Wave 8 ran with the pre-Gimel build script.** Timeline:

| time (UTC+1) | event |
|--------------|-------|
| 00:46:30 | Wave 8 build kicked off (filename timestamp) |
| 00:58:58 | Gimel commits `126d4be` adding `rdfc10_runner.ml` + the build wiring |
| 01:05:14 | Wave 8 build finished (mtime on log) |

So the script that *Wave 8* invoked did not contain the rdfc10_runner
ocamlopt block at all. The log shows it cleanly — Step 2 prints four
"Built:" lines (w3c_runner / factoidal / factoidal-http / owl_runner)
and then jumps straight to Step 3 with no rdfc10_runner attempt or
error in between. No silent compile failure. No swallowed `|| true`.
No missing-file guard. The wiring was simply not present yet.

## Audit of the post-Gimel script (HEAD)
File: `formal/fstar/build-ocaml.sh` lines 297–318.

- `rdfc10_runner.ml` exists in `ocaml-output/` (committed by Gimel,
  432 lines, opens `RDF_Graph_Executable`, calls `Parser_Turtle.parse_turtle_with_base`
  + `Parser_NQuads.parse_nquads`, both present in `COMMON_MODULES`).
- Compile flags identical to `owl_runner` (same `$STATIC_FLAGS`,
  `$COMMON_MODULES`, `$PARQUET_NATIVE_STUBS`, same package list incl. `unix`).
- No `[ -f rdfc10_runner.ml ]` guard.
- No `|| true`. The call goes through `run_with_heartbeat`, which
  returns the child's exit code, and `set -euo pipefail` (line 51)
  guarantees a hard abort on non-zero rc.
- Symlink `ln -sf ../../../bin/${PLATFORM}/rdfc10_runner rdfc10_runner`
  is present (line 318).
- `generate-report.sh` already wired (lines 38, 43, 48, 69–75, 119–164):
  picks up the binary if it exists, computes "RDFC-1.0 tests: N pass,
  M fail, K stub (out of T)", folds into the `rdf-canon` row of the
  RDF table.

## Verdict
The wiring is correct. Wave 9 (which is currently extracting in
foreground at the time of writing) **will** produce
`bin/darwin-arm64/rdfc10_runner` on the next compile pass.

## Hardening change
The compile step relies on `set -e` to bubble up a failure from
`run_with_heartbeat`. That's good for failing loudly, but the
heartbeat function buffers all output in `_ocamlopt_rdfc10_runner.log`
and only emits it via `cat` AFTER a successful return. If compilation
ever does fail, the abort happens *before* the `cat`, so the human
sees the abort but not the underlying error. Same gap is present for
all four other runners but is most worth fixing for the new one
(since it's the one we know we'll be iterating on through Phase 1
when the F*-extracted canonicaliser lands).

Applied: capture rc, dump log on failure with a clear marker, then
re-fail with the same code.

## Out of scope
- Not touching `.fst` files.
- Not touching the runner logic itself (Gimel did Phase 0).
- Not running `./build-ocaml.sh extract` or `compile` (Wave 9 in flight).
- Not modifying the four pre-existing runners' build steps (would
  blow scope; same hardening can be applied later as a sweep).
