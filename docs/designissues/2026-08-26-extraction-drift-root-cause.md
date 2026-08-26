# Extraction drift found by npm-publish run 1 (2026-08-26)

Status: root cause established. The drift is NOT caused by the
incremental-extract manifest.

## What CI reported

`npm-publish.yml` run 1
(<https://github.com/danbri/factoidal/actions/runs/32979330856>) ran
`./build-ocaml.sh extract --force-full` and then
`git diff --exit-code -- 'formal/fstar/ocaml-output/*.ml'`. The diff was
8 files changed, 2736 insertions, 213 deletions:

| File | Lines in CI diff |
| --- | --- |
| `RDF_CottasStore.ml` | 2010 |
| `Parquet_Footer.ml` | 220 |
| `Math_Sigmoid.ml` | 216 |
| `RDF_CottasStore_OnDiskIndex.ml` | 158 |
| `RDF_CottasStore_PageCache.ml` | 155 |
| `SPARQL11_Algebra.ml` | 141 |
| `RDF_CottasStore_ColumnSeq.ml` | 39 |
| `SHACL_Validation.ml` | 10 |

## The hypothesis that was tested and refuted

The starting hypothesis was: the incremental extraction path does not
reproduce the full one, because a manifest hit lets `extract` skip a
module and skip its patch with it.

Refuted, for two independent reasons.

1. `ocaml-patches.sh` runs UNCONDITIONALLY at the end of the extract
   step (`build-ocaml.sh`, after the manifest-compaction block). It
   walks the whole `$OUTDIR`, not the set of re-extracted modules. Every
   patch is idempotent by a marker test. So a skipped module still gets
   its patches re-applied on every `extract`. Patch state cannot drift
   through the manifest.
2. The manifest is not tracked by git. `git ls-files
   formal/fstar/ocaml-output/.extract-state/` is empty. In CI the
   manifest starts absent, so plain `extract` already re-extracts every
   module and `--force-full` changes nothing there. The comment at
   `npm-publish.yml` line 99 ("bypass the COMMITTED incremental-extract
   manifest") describes a file that does not exist in the repository;
   that comment is wrong and is corrected in this landing.

Measured refutation: copying the committed `ocaml-output/*.ml` to a
scratch directory and running `./ocaml-patches.sh <scratch>` — the
extract step's own patch call, with no `fstar.exe` at all — reproduces 7
of the 8 CI-reported files:

```
Parquet_Footer.ml               213 added,  7 removed
RDF_CottasStore.ml             2000 added, 10 removed
RDF_CottasStore_ColumnSeq.ml     22 added, 17 removed
RDF_CottasStore_OnDiskIndex.ml  146 added, 12 removed
RDF_CottasStore_PageCache.ml    139 added, 16 removed
SHACL_Validation.ml              10 added,  0 removed
SPARQL11_Algebra.ml             118 added, 23 removed
```

The committed `.ml` for those 7 files is UNPATCHED output. The
divergence is not between the incremental and full extraction paths. It
is between the committed `.ml` and any run of the patch step.

## The actual mechanism

Three commits put `.ml` files into git that had not been through
`ocaml-patches.sh`, or that came from a different F* build.

### 1. `2a2d50ddee2` + `3d9b9c47188`, both 2026-08-24, both titled "Lean N-Quads: ..."

Both are single-parent commits whose stated deliverable is Lean 4 source.
Both also carry the working-tree residue of an unrelated in-flight F*
workstream:

- `2a2d50ddee2` carries `formal/fstar/RDF.CottasStore.fst`, 258 lines
  changed. Its message does not mention it.
- `3d9b9c47188` carries the rewritten
  `experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh`
  (236 lines: the 8-`assume val` realisation reduced to 1) and five
  freshly extracted, UNPATCHED `.ml` files — `RDF_CottasStore.ml`
  (4679 to 2780 lines), `RDF_CottasStore_ColumnSeq.ml`,
  `RDF_CottasStore_OnDiskIndex.ml`, `RDF_CottasStore_PageCache.ml`,
  `Parquet_Footer.ml`, `SPARQL11_Algebra.ml`. Its message does not
  mention them either.

The `.ml` files were captured between `fstar.exe --codegen OCaml` and
`./ocaml-patches.sh`. `RDF_CottasStore.ml` held the marker
`Cottas_subject_offset_idx` at `96183ba8af6` (2026-08-15) and holds 0
occurrences after `3d9b9c47188`.

### 2. `6e6f7171ce9`, 2026-08-24, "Lean harness: run the OWL entailment regimes"

Deletes 10 lines from `formal/fstar/ocaml-output/SHACL_Validation.ml` —
that file's patch — alongside two Lean files. Same shape.

### 3. `760dba15ff0`, 2026-08-22, "LATERAL x SERVICE ... unblock macOS builds"

Force-adds `Math_Sigmoid.ml` (131 lines), extracted on macOS. This file
is the only `.ml` in the tree written in the pre-2025.12.15 F* emission
style (`let (x : t) = fun s -> ...`); every other `.ml` uses the current
style (`let x : t= ...`, curried parameters). Re-extracting
`Math.Sigmoid.fst` here with F* 2025.12.15 gives 91 lines and a 220-line
diff against the committed file, with no semantic difference — the whole
diff is emission style. That machine ran a different F* version.

`formal/fstar/.gitignore` carries `*.ml`, so a newly extracted module is
invisible to `git status` until force-added. That is how a
different-toolchain `.ml` entered the tree; it is not how the seven
unpatched files entered, because those were already tracked and
therefore visible as modified.

## Consequence for the shipped artifacts

`bin/linux-x86_64/factoidal` and `w3c_runner` are dated 2026-08-24
20:46, after `3d9b9c47188` (19:27). The shipped linux binaries were
compiled from the unpatched `.ml`. `docs/test-results/latest.json` is
dated 2026-08-24 16:37 UTC, before it. The before/after suite comparison
in the follow-up commit measures what that cost.

## Why the extraction CI did not catch it

Three workflows look like they should have. None can.

- `check-extraction.yml` runs `./build-ocaml.sh extract` and
  `./build-ocaml.sh compile` and stops. It never diffs the result
  against the committed `.ml`. It checks that extraction SUCCEEDS, not
  that the committed output MATCHES it. Its name says "Check F*
  Extraction"; its reach is "extraction still compiles".
- `check-derived-files.yml` blocks hand-edits to a hardcoded 12-file
  allowlist, and exits 0 as soon as any `.fst` also changed in the PR.
  `2a2d50ddee2` changed a `.fst`, so this gate would have passed by
  construction. `RDF_CottasStore.ml` is not on the allowlist anyway.
- Both trigger on `pull_request` only. All three losing commits were
  pushed straight to `claude/main` with no PR, so neither workflow ran
  at all.

`ocaml-patches.sh` also prints `All patches applied successfully.`
unconditionally, before the warning count, and always exits 0. That line
in the run-1 CI log is not evidence that the patches applied.

## The guard

See the follow-up commit: `check-extraction.yml` gains the same
`--force-full` + `git diff --exit-code` drift check `npm-publish.yml`
runs, and runs it on `push` as well as `pull_request`, with
`experimental_ocaml_glue/**`,
`minimal_regrettable_glue_code_each_with_an_open_issue/**` and
`ocaml-output/*.ml` added to its path filter.
