# Splitting factoidal into factoidal-core and factoidal-builds

Status: PLAN for owner review, 2026-08-27. Nothing executed.

Owner, 2026-08-27, verbatim:

> "I have made two new sibling repos under danbri: factoidal-core as
> successor to this one and factoidal-builds for the CI that keeps us
> with fresh binaries. We will need git history only for formal/\* file
> paths. The binaries and their builds will migrate to own repo."

Both repos exist and are writable: `danbri/factoidal-core`,
`danbri/factoidal-builds`.

## 1. Measured baseline

Tracked content, this working tree:

| path | tracked size | files | commits touching |
|---|---|---|---|
| `bin/` | **1.3 GB** | 284 | 616 |
| `formal/` | 58 MB | 1,295 | 1,217 |
| `docs/` | 134 MB working | 585 | — |
| `third_party/` | 604 MB working | 5,230 | — (15 submodules) |
| whole repo history | — | — | 2,531 commits |

Object store today: 11.12 GiB loose (unreachable), 4.87 GiB packed,
3,619 packs. **A fresh history-filtered clone drops all of the
unreachable 11 GiB by construction.** The split therefore also fixes the
repository-size problem, without the `git prune` the owner declined on
2026-08-27 as too risky.

## 2. The trap in "history only for `formal/*`"

`formal/` is **not** pure source. It already contains build output:

| inside `formal/` | files | size |
|---|---|---|
| `.ml` (extracted OCaml) | 188 | 6.3 MB |
| `.cmi` | 180 | 2.9 MB |
| `.o` | 15 | 556 KB |
| `.cmx` | 13 | 80 KB |
| `.log` | 61 | 1.6 MB |

A path-prefix filter on `formal/*` carries all of it into core. That is
the opposite of the stated intent, and `formal/fstar/ocaml-output/*.ml`
is arguably the single most build-shaped thing in the tree.

So the filter cannot be a path prefix. It has to be a path prefix minus
an artifact rule, and WHICH artifacts stay is a design decision, not a
detail — see section 3.

## 3. The design question: where does the extraction boundary live?

This is the decision everything else follows from. Three coherent
answers.

### Option A — core is specs only

Core keeps `.fst`, `.fsti`, `.lean`, proofs, `lakefile`. Builds owns
extraction, `.ml`, binaries, npm packaging, site artifacts.

- Cleanest conceptually. Core needs no toolchain.
- **Cost:** the extraction drift guard becomes a CROSS-REPO check. Its
  two sides — the `.fst` and the committed `.ml` — end up in different
  repositories with independent histories.

### Option B — core is specs + extraction + extracted `.ml` (RECOMMENDED)

Core keeps everything in `formal/` except object files and logs:
`.fst`, `.fsti`, `.lean`, `.ml`, `build-ocaml.sh`, the patch scripts.
Builds owns compiled binaries (`bin/<platform>/`), the `.cmi`/`.cmx`/
`.o`, npm publishing and site artifacts.

- Keeps the drift guard inside ONE repository, where both sides live.
- That guard was repaired on 2026-08-26 after it had been blind through
  a real defect: HDT stage-4 parity was 0 pass, 6 fail in the shipped
  engine while CI recorded 6 pass, 0 fail, because CI re-extracted and
  the shipped binary did not. Making it a cross-repo check reintroduces
  exactly the class of gap that let that through.
- **Cost:** core is bigger, and carries generated files.

### Option C — core is specs + scripts, `.ml` regenerated not committed

Drift becomes "re-extract and compare against a committed hash
manifest".

- Smallest core.
- **Cost:** any check needs the F\* toolchain; iron rule #9 (commit
  binaries so a fresh clone runs tests with no toolchain) no longer
  holds for the OCaml layer.

**Recommendation: B.** The drift guard is the project's main defence
against shipping an engine nobody verified, and it has already failed
once from being too weak. Do not spread it across a repository boundary
in the same month it was repaired.

## 4. Questions the owner's instruction does not settle

Each changes the filter materially.

1. **Tests.** `tests/` (340 files) and the 15 `third_party/testing/*`
   submodules are the project's evidence. Do they go to core (so core
   can prove conformance), to builds (so builds can gate binaries), or
   both? They reference `formal/` 61 times.
2. **`docs/`.** 585 tracked files: the site, the dashboard, hub
   notebooks whose live cells run the npm bundle. Notebooks are
   documentation of the specs; the dashboard is a build product.
   Probably split, not assigned whole.
3. **`npm/`.** The package embeds artifacts from both sides. Publishing
   is build-shaped; the API surface is spec-shaped.
4. **`skills/`, `CLAUDE.md`, `docs/designissues/`.** The working
   discipline. Core, builds, or duplicated?
5. **Does `factoidal` stay alive** as an archive, or become a redirect?

## 5. Coupling that will break, measured

`formal/fstar/build-ocaml.sh` references paths outside `formal/`:

    ../../../bin/      90 references
    ../../docs/        28 references
    third_party/        1
    npm/                1

and from outside, references INTO `formal/`:

    tests/       61      docs/     43      tools/    19
    npm/         18      .github/  10      examples/  7

So `build-ocaml.sh` is not a `formal/` file in any useful sense — it is
the seam. Under option B it moves to builds and reaches into core, or it
splits into an extract half (core) and a compile/link half (builds).
That split is the single largest piece of real work in this migration.

## 6. Mechanics

**Tool: `git filter-repo`, not `filter-branch`.** Not installed here
(`git 2.43.0`); `pip install git-filter-repo`. `filter-branch` is
deprecated, quadratic, and mangles tags.

Order that keeps a rollback available at every step:

1. **Freeze.** Land everything in flight; confirm
   `git log --branches --not --remotes` is empty. Done as of
   2026-08-27.
2. **Full mirror backup.** `git clone --mirror` of `danbri/factoidal` to
   a separate location. Nothing below touches the original.
3. **Build the path spec** from the option-3 decision. Write it as a
   FILE (`--paths-from-file`), reviewed and committed, not typed at a
   prompt.
4. **Filter into core**, from a fresh mirror clone. Verify BEFORE
   pushing (section 7).
5. **Filter into builds**, same way.
6. **Push both**, to empty repos.
7. **Rewire.** Submodules, workflows, the `build-ocaml.sh` seam, npm
   paths, hub asset paths. This is where the time goes, not in step 4.
8. **Dual-run**, both repos green on their own CI, before anything is
   archived.
9. **Archive or redirect `factoidal`** only after 8.

## 7. Verification, before either push

A filtered history is easy to get subtly wrong and hard to notice.
Check, do not assume:

- **File-set equality at the tip.** `git ls-files` in the filtered repo
  equals the intended subset of the original, exactly. Diff the lists;
  do not eyeball counts.
- **Content equality at the tip.** Every surviving file's blob hash
  matches the original's. A filter that alters content is a filter bug.
- **Commit count sanity.** Core should land near 1,217 (commits touching
  `formal/`), not 2,531 and not 40. A number far from the expectation is
  a bug report, not a result.
- **The suites still run.** Core's tests green in core; builds' gates
  green in builds. A migration that ships a repo whose tests cannot run
  has not been verified, whatever the file lists say.
- **Authorship preserved.** Every commit still attributed to the human
  (iron rule #13). `filter-repo` rewrites committer identity by default
  — pass `--preserve-commit-encoding` and check `%an`/`%ae` on a
  sample.

## 8. Risks

| risk | mitigation |
|---|---|
| drift guard split across repos | option B keeps both sides together |
| submodule pointers broken by rewrite | `filter-repo` rewrites `.gitmodules`; re-init and verify all 15 |
| `build-ocaml.sh` seam | budget it as the main work item, not a side effect |
| lost history nobody notices | verify file-set AND content at the tip before pushing |
| the old repo is needed again | mirror backup first; do not archive until both repos are green |
| in-flight work stranded | freeze first — currently clean, so the window is now |

## 9. What is NOT in scope here

npm publishing continues from wherever `package.json` ends up; that is a
consequence of the decision in section 4.3, not an independent choice.
The 0.2.0 release should land BEFORE the split, so the first published
version from the new layout is not also the first version to exercise a
new CI path.
