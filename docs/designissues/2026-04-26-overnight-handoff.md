# Overnight handoff — 2026-04-26 → 27 (Phase 2.6 unwind progress + regression)

## What landed cleanly

| Commit | What |
|---|---|
| `c99dc31` | Tet3 redirect #1 — `estimate_fast_inner` to F\* `PresenceBitmap.rg_could_contain` |
| `ce922d7` | Tet3 redirect #2 — `search_fast_inner` (the actual 4-second cost site) |
| `0bf57f3` | Tet3 redirect #3 — `search_fast_limited` |
| `8f586c7` | Compound `(p,o)` bitmap design doc (issue #104) — sparse-roaring, ~12-20 MB on parliament |
| `435637f`/`e053665` | Yod7 audit — Lamed3 reader is dead post-q03-bypass; `.po.presence` writer rule-#11(b) acceptable |
| `51c6a79`/`d447ba4` | Tau3 audit — Bet7 still load-bearing, retire ONLY after 2.6 |
| `420169a` | Unwind doc Phase 2.6 progress section |
| `6a7f26b` | Unwind doc lamed3 regression update |

All three Tet3 prune call sites now consult F\* `RDF.CottasStore.PresenceBitmap` first and fall back to per-column Hashtbls only if the companion bitmap is absent. Smoke confirms `[tet3-fstar-trace] estimate_fast_inner: rg-tests via_fstar=78 via_hashtbl=0` — the F\* path is the runtime ground truth.

W3C unchanged at 1657/1/4 across all Tet3 commits.

## What didn't land — Lamed3 cleanup regressed

Yod7's option (a) ("keep writer, delete reader patch + delete q03 bypass") was attempted in worktree, source edits applied, build cycle ran. Build "succeeded" but **silently regressed** Mem5 + all three Tet3 F\* redirects.

### Root cause (issue #105)

Lamed3 isn't just a reader — it's also the patch that **renames** the base `search_fast` / `estimate_fast` to `*_inner` so the dispatcher can wrap them. The chain:

1. `cottas_ondisk_runtime.sh` produces base `search_fast` / `estimate_fast`.
2. Tet3 (subj+obj prune) patches them in place.
3. **Lamed3** renames to `*_inner` and adds dispatcher wrapping `match X_via_offsets ... | None -> X_inner`.
4. Mem5 patches `estimate_fast_inner`.
5. Tet3 F\* redirects patch the gates inside `*_inner`.

Yod7 classified the entire reader half (incl. dispatcher wrapping) as deletable. But the rename is structural — Mem5 + 3 Tet3 redirects all anchor against the `*_inner` names. With Lamed3 trimmed, the names don't exist, all four downstream patches silently bail (warnings logged but exit 0), binary regresses to pre-Mem5 state.

Reverted in HEAD. Build re-run, daemon restarted on fresh binary at 00:50.

### Fix paths (recommend (b))

- **(a)** Decompose Lamed3 into three patches: writer / rename-pivot / reader. Trim reader.
- **(b)** Move the rename pivot to its own patch upstream, between Tet3 and Lamed3. Lamed3 becomes reader-only. Then Yod7's option (a) works trivially. ← cleanest
- **(c)** Have downstream patches anchor against post-rename + post-Lamed3 dispatcher structure. Fragile.

Tracked in **issue #105**. Next session.

## Other artefacts

- Parliament queries sweep: 28/48 passed (22/24 Vendored, 6/24 Modernised), 7 with rows>0, 20 server-side 504 timeouts. Sweep was concurrent with the build, so the daemon was loaded — not a clean baseline. Re-run after compound `(p,o)` bitmap lands for a real comparison.
- Three locked stale agent worktrees in `.claude/worktrees/` — `agent-a080d667` (lamed3 cleanup), `agent-a5647c4d` (psi3, way back), `agent-afd79cd5` (older). Safe to remove with `git worktree remove --force` when convenient.
- Util_Log.ml + Parquet_Footer.ml occasionally show as modified in `git status`; revert to HEAD if seen — they're extracted output that gets regenerated.

## Live demo state

- Daemon PID 19825 on port 3032, fresh binary 00:50 with Tet3 F\* redirects.
- Q03 still ~3.8s (the redirects move the prune to F\* but don't fix the joint-`(p,o)` gap that requires compound bitmap).
- The 3.8s breaks down as: ~0ms parse, ~10ms estimate, ~3.8s execute (the `rg=22` four-column DLBA decode). Compound bitmap (issue #104) closes this; lazy column decode would also work.

## Recommended next-session pick-up

1. **Issue #105 — move rename pivot upstream.** This unblocks Yod7's lamed3 cleanup + makes the patch chain less entangled in general.
2. **Compound `(p,o)` writer (task #104).** Per nun4 design doc — new patch, new companion file `.po.presence`, hooks into Vav3 column-decode walk. Reader integration deferred.
3. **Yod6 redirect (task #103).** Same shape as Tet3 redirects. Predicate-presence prune to F\* `PresenceBitmap.rg_could_contain_token`. Should work without rename-pivot fix since Yod6 anchors against `search_fast` directly (pre-Lamed3-rename).
4. **Tet3 main retirement (task #105[?])** — only safe AFTER all 3 redirects land AND the no-companion fallback path is decided. Delete `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh`.

## Phase 2.4 / 2.5 / 2.7 still blocked

- **2.4 (Aleph6)**: blocked on 2.5 / 2.6 / 2.7 (Chi3 audit).
- **2.5 (cottas_ondisk_runtime.sh, 688 LoC)**: needs F\* perf parity first. The big domino.
- **2.7 (Bet7)**: blocked on 2.6 — Vav3 *populates* same Hashtbls Bet7 populates (Tau3 audit).

## Misc

- Phase 2.8 CI gates installed (Omega3, commit `a5c2483`): purity check (rule #11) + UK Parliament bench. Soft mode default; flip with `FSTAR_PURITY_HARD=1` / `UKPAR_BENCH_HARD=1`.
- Debug tool `tools/factoidal-debug-query.sh` is a useful single-shot CLI wrapper for `--explain`. Tav6 evaluation suggests Skill packaging (not MCP); fix the `-s cmdfile` bug if reactivating ocamldebug recipes.
