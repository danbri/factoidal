# Restructuring `formal/fstar/` into folders

Owner's framing, verbatim: "i still hope for formal/fstar/* to evolve
into a work of beauty with clean abstraction vs impl grunge. Current
dir feels overwhelmingly cluttered. Are folders permitted???"

This is a design doc only. No file moves, no `build-ocaml.sh` edits
land in this slice.

## 1. Are folders permitted?

Yes, with one mechanism to wire up: **`fstar.exe --include <dir>`**.

Today `formal/fstar/` holds 134 `.fst` + 8 `.fsti` = 142 files, all
flat, and **zero `--include` flags exist anywhere in the build** —
`build-ocaml.sh`, the `Makefile`, and every CI workflow invoke
`fstar.exe` with `cwd == formal/fstar` and bare filenames
(`RDF.Term.fst`, `Parser.NTriples.fst`, ...). This works only because
F* implicitly searches the current working directory for a module's
source file. Confirmed experimentally (z3 4.13.3, `fstar.exe --version`
→ `F* 2025.12.15`, this sandbox):

- A module `B.fst` that does `open A` and lives in a different
  directory from `A.fst` **fails to resolve** ("Namespace 'A' cannot
  be found") unless `A.fst`'s directory is passed with
  `--include <dir>`.
- `--include` is additive and repeatable — one flag per subdirectory
  that holds a dependency (`--include core --include parsers ...`).
  `cwd` itself remains implicitly searched; only *other* directories
  need an explicit flag.
- `.fst.checked` files are **content-digest keyed, not path-keyed**.
  Moving both a module's `.fst` and its already-valid `.fst.checked`
  into a new directory together, then re-invoking `fstar.exe` with an
  updated `--include`, reuses the cache with **no re-verification** —
  confirmed by mtime: the moved file's own `.checked` mtime is
  unchanged, and - the part that matters - a **dependent** module's `.fst.checked`
  (e.g. `B.fst.checked`, which embeds a digest of `A`'s interface) is
  *also* left untouched by the move, because `A`'s content and
  extracted signature didn't change. The invalidation is transitive
  through content, not through path.

So: folders are permitted, F* has no objection to a source tree with
subdirectories, and the plumbing cost is bounded and mechanical — add
`--include` flags at every `fstar.exe` call site, and update every
place that currently assumes flatness via a literal glob or a bare
relative filename. Section 3 enumerates every such site found in this
repo.

**Existing precedent for folders in this codebase:** `formal/roaring/`
is already a self-contained subsystem with its own `src/`, its own
`Makefile`, and its own flat file group — proof that F* tolerates
project-level directory structure. It doesn't, however, prove the
harder case this doc is about: splitting *one* tightly-coupled
142-file tree with live cross-directory `open`s (roaring never
imports from `formal/fstar/`, so it never needed `--include` either).
The `core/`+`parsers/` experiment above is the evidence for that
harder case. Also worth noting: `experimental_ocaml_glue/`,
`minimal_regrettable_glue_code_each_with_an_open_issue/`,
`ocaml-output/`, `ocaml-output-ci/`, and `c-output/` are *already*
folders sitting next to the flat `.fst` pile — the tree is not
folder-averse today, it's specifically the spec-source pile that
never got organized.

## 2. Proposed taxonomy

Six top-level folders (within the requested 6-10), three of them with
one level of internal nesting where the codebase's own dotted-name
seams (`SPARQL.Plan.*`, `SPARQL.HTTP.*`, `RDF.CottasStore.*`,
`HDT.*`) already draw the line. All 142 files accounted for.

| Folder | Files | What it holds |
|---|---|---|
| `foundations/` | 10 | Primitives everything else depends on: string/IRI scanning, XSD value space, byte/list helpers, logging. No RDF-specific semantics. |
| `terms-and-graphs/` | 24 | The RDF/RDFS/OWL data model: terms, triples, graphs, vocabulary, closure rules, canonicalization, dataset merge, pretty-printing. |
| `parsers/` | 19 | Concrete syntaxes: N-Triples, Turtle, N-Quads, TriG, RDF/XML, XML/XPath, RIF/XML, SPARQL result formats (SRX/CSV/JSON), JSON, JSON-LD syntax. |
| `sparql/` (+ `sparql/plan/`, `sparql/http/`) | 30 | Algebra, parser, protocol, store dispatch, update, query planning, HTTP endpoint logic. |
| `store/` (+ `store/cottas/`, `store/hdt/`) | 34 | On-disk backend: capability dispatch, COTTAS/Parquet columnar store, HDT container format, delta log. |
| `standards/` (+ `owl/ shacl/ shex/ rif/ rml/ jsonld/ csvw/ vc/`) | 25 | Reasoning and format standards layered on top of the core: OWL, SHACL, ShEx, RIF, RML, JSON-LD algorithm, CSVW, Verifiable Credentials. |

Total: 10 + 24 + 19 + 30 + 34 + 25 = 142.

### `foundations/` (10)

| File | Notes |
|---|---|
| `RDF.IRI.fst` / `.fsti` | Real abstraction boundary per `fstar-module-style` — a natural `.fsti` candidate already. |
| `XSD.Datatypes.fst` | **Judgment call**, see "hard to place" below. |
| `Parser.FastString.fst` | Class F (fires every suite) per the foundational-tier discipline. |
| `Parser.IRI.fst` | Class F. |
| `Parser.Combinators.fst` | Shared parser-combinator library used by every concrete syntax. |
| `RDF.Bytes.fst` | Byte-level helpers (pragmatics tier). |
| `RDF.List.Helpers.fst` | Tail-recursion helpers (pragmatics tier). |
| `Util.Log.fst` | Logging primitive, in `COMMON_MODULES`. |
| `RDF.Format.fst` | Class F. |

### `terms-and-graphs/` (24)

`RDF.Vocabulary.fst`/`.fsti`, `RDF.Vocabulary.Axioms.fst`,
`RDF.Term.fst`/`.fsti`, `RDF.Triple.fst`/`.fsti`,
`RDF.Indexed.fst`/`.fsti`, `RDF.Graph.fst`/`.fsti`,
`RDF.Graph.Executable.fst`, `RDFS.Closure.fst`/`.fsti`,
`OWL.Closure.fst`/`.fsti`, `RDF.Canonical.fst`,
`RDF.Canonical.Manifest.fst`, `RDF.Dataset.Graphs.fst`,
`RDF.Dataset.Merge.fst`, `RDF.Pretty.fst`,
`RDF.NQuads.Serialize.fst`, `RDF.Turtle.Serialize.fst`,
`RDF.Store.Loader.fst`.

This is the foundational-core cluster the `fstar-module-style` roadmap
already names as one unit ("split `RDF.Graph.Executable` into
`RDF.Term`, `RDF.Triple`, `RDF.Graph` plus `RDFS.Closure`,
`OWL.Closure`") — note that split is **partially done**: the four
target files already exist alongside `RDF.Graph.Executable.fst`,
which is still ~3,500 LoC and still the thing every OWL-closure edit
recompiles through. Folder placement doesn't finish that split; it
just gives the eventual smaller pieces a home. `RDF.Store.Loader.fst`
is a naming-vs-role mismatch (see below) placed here on role, not name.

### `parsers/` (19)

`Parser.NTriples.fst`, `Parser.Turtle.fst`, `Parser.TurtleScanner.fst`,
`Parser.NQuads.fst`, `Parser.TriG.fst`, `Parser.RDFXML.fst`,
`Parser.XML.fst`, `XML.Wellformedness.fst`, `XML.Namespaces.fst`,
`Parser.XPath.fst`, `XPath.Eval.fst`, `Parser.RIFXML.fst`,
`Parser.SRX.fst`, `Parser.CSVResults.fst`, `Parser.JSONResults.fst`,
`Parser.JSON.fst`, `Parser.JSONLD.fst`, `Parser.OWLFunctional.fst`,
`SPARQL.JSON.Escape.fst`.

### `sparql/` (30)

Top level (14): `SPARQL11.Algebra.fst`, `SPARQL11.Parser.fst`,
`SPARQL11.IRI.Resolve.fst`, `SPARQL11.Store.fst`,
`SPARQL.Protocol.fst`, `SPARQL.GraphStore.fst`,
`SPARQL.ServiceDescription.fst`, `SPARQL.Update.Analysis.fst`,
`SPARQL.Update.Sandbox.fst`, `SPARQL.Query.Analysis.fst`,
`SPARQL.Diagnostics.fst`, `SPARQL.Explain.fst`,
`SPARQL.Eval.Limits.fst`, `SPARQL.Eval.TimeBudget.fst`.

`sparql/plan/` (6): `SPARQL.Plan.AccessPath.fst`,
`SPARQL.Plan.Estimate.fst`, `SPARQL.Plan.Explain.fst`,
`SPARQL.Plan.Loader.fst`, `SPARQL.Plan.Pruning.fst`,
`SPARQL.Plan.Streamable.fst`.

`sparql/http/` (10): `SPARQL.HTTP.fst`, `SPARQL.HTTP.Admin.fst`,
`SPARQL.HTTP.BackendInfo.fst`, `SPARQL.HTTP.Client.fst`,
`SPARQL.HTTP.QueriesIndex.fst`, `SPARQL.HTTP.Response.fst`,
`SPARQL.HTTP.Routes.fst`, `SPARQL.HTTP.RunQuery.fst`,
`SPARQL.HTTP.StaticFiles.fst`, `SPARQL.HTTP.Timing.fst`.

`SPARQL11.Algebra.fst` (~6,000 LoC / 251 KB) is the other module the
roadmap already flags for an internal split (algebra datatypes / eval
semantics / function library / numerics-XSD value space) — same
caveat as `RDF.Graph.Executable`: the folder gives the future pieces
somewhere to live, it doesn't do that split.

### `store/` (34)

Top level (13): `RDF.Store.Capabilities.fst`,
`RDF.Store.Capabilities.Cottas.fst`, `RDF.Store.Capabilities.Delta.fst`,
`RDF.Store.Combine.fst`, `RDF.Store.LazyTermCache.fst`,
`RDF.Store.HDTTermCacheRegistry.fst`,
`RDF.Store.Columnar.OffsetIndex.fst`, `RDF.Store.Columnar.DeltaLog.fst`,
`RDF.Store.Columnar.DeltaMerge.fst`, `Parquet.Footer.fst`,
`Parser.Ballyhoo.fst`, `Parser.BallyhooBloom.fst`,
`Parser.BallyhooCOTTAS.fst`.

`store/cottas/` (16): `RDF.CottasStore.fst`,
`RDF.CottasStore.BaseWriter.fst`, `RDF.CottasStore.ColumnSeq.fst`,
`RDF.CottasStore.CompoundPresenceBitmap.fst`,
`RDF.CottasStore.CompoundPresenceWriter.fst`,
`RDF.CottasStore.DictWriter.fst`, `RDF.CottasStore.LazyDict.fst`,
`RDF.CottasStore.LazyDictRegistry.fst`,
`RDF.CottasStore.OffsetsWriter.fst`, `RDF.CottasStore.OnDiskIndex.fst`,
`RDF.CottasStore.OnDiskRuntime.fst`, `RDF.CottasStore.PageCache.fst`,
`RDF.CottasStore.PageCache.Bounds.fst`,
`RDF.CottasStore.PresenceBitmap.fst`,
`RDF.CottasStore.PresenceWriter.fst`, `RDF.CottasInMem.fst`.

`store/hdt/` (5, **pilot cluster**): `HDT.Container.fst`,
`HDT.Dictionary.fst`, `HDT.Triples.fst`, `Parser.BallyhooHDT.fst`,
`Parser.BallyhooHDTQ.fst`.

(13 top level + 16 `cottas/` + 5 `hdt/` = 34.)

### `standards/` (25)

`standards/owl/` (6): `OWL.Vocabulary.fst`,
`OWL.DirectMapping.Filter.fst`, `OWL.QueryRewrite.fst`,
`OWL.QueryEval.fst`, `OWL.Tests.Manifest.fst`, `Tableau.fst`.

`standards/shacl/` (1): `SHACL.Validation.fst`.

`standards/shex/` (2): `ShEx.Schema.fst`, `ShEx.Validation.fst`.

`standards/rif/` (6): `RIF.Core.Builtins.fst`,
`RIF.Core.Conformance.fst`, `RIF.Core.Eval.fst`, `RIF.Core.Syntax.fst`,
`RIF.Core.Tests.fst`, `RIF.Core.Translation.fst`.

`standards/rml/` (3): `RML.Eval.fst`, `RML.Mapping.fst`,
`RML.Sources.fst`.

`standards/jsonld/` (3): `JSONLD.Context.fst`, `JSONLD.Expand.fst`,
`JSONLD.Loader.fst`. (`Parser.JSONLD.fst`, the concrete-syntax entry
point, stays in `parsers/` — see below, this split is actually a
clean illustration of the taxonomy working as intended.)

`standards/csvw/` (3): `CSVW.Conversion.fst`, `CSVW.Metadata.fst`,
`CSVW.URITemplate.fst`.

`standards/vc/` (1): `VC.Credential.fst`.

### Files that are hard to place (stratification opportunities)

These aren't folder-assignment ambiguities to resolve quietly — each
one names a real seam the taxonomy surfaces, worth its own tracked
follow-up per `fstar-module-style`'s "do these opportunistically, one
commit-sized slice at a time" guidance. None of them block this move;
the folder holds the file as-is and the note travels with it.

1. **`RDF.Graph.Executable.fst`** — still the ~3,500 LoC monolith the
   2026-05-08 roadmap flagged for splitting; the split it names
   (`RDF.Term`/`RDF.Triple`/`RDF.Graph`/`RDFS.Closure`/`OWL.Closure`)
   already exists as separate files *alongside* it, not *instead of*
   it. Placed in `terms-and-graphs/` on role. The folder move doesn't
   discharge the outstanding split; don't let it read as having done so.
2. **`SPARQL11.Algebra.fst`** — same shape, ~6,000 LoC / 251 KB,
   flagged for a four-way split (algebra datatypes / eval semantics /
   function library / numerics-XSD). Placed in `sparql/` on role.
3. **`XSD.Datatypes.fst`** — literally an external standard's value
   space (a `standards/xsd/` case on name), but its actual dependency
   role is foundational: `RDF.Term` literal equality and
   `SPARQL11.Algebra` numeric promotion touch it constantly. Placed in
   `foundations/` on role, flagged because the name argues the other
   way.
4. **`RDF.Store.Loader.fst`** — name says `store/`, but it's bundled
   into `COMMON_MODULES` (`build-ocaml.sh:766`) alongside the
   foundational-tier set and compiled into every OCaml target, i.e.
   treated as core infrastructure, not backend-specific. Placed in
   `terms-and-graphs/` on role; `COMMON_MODULES` bundling is a
   compile-order list independent of directory, so this doesn't
   change linkage either way — flagging only because the name
   disagrees with the folder.
5. **`RDF.Store.HDTTermCacheRegistry.fst`** — name says HDT-specific,
   but it's a generic registry pattern under the `RDF.Store.*` prefix
   alongside backend-agnostic siblings. Placed in `store/` top level,
   not `store/hdt/`, on the same reasoning as #4.
6. **`SPARQL.JSON.Escape.fst`** — sits between `parsers/` (it's a
   byte-level string-escaping routine, same register as
   `Parser.JSONResults`) and `sparql/` (its callers are query-result
   serialization). Placed in `parsers/`; issue #271 and the mirrored-
   JSON-escape bug (`fstar-module-style` extraction-semantics trap
   #4) are the case law that makes this module's boundary matter —
   don't let the folder move touch its content.
7. **`Parser.Ballyhoo*` family** (`Parser.Ballyhoo.fst`,
   `.BallyhooBloom`, `.BallyhooCOTTAS`, `.BallyhooHDT`,
   `.BallyhooHDTQ`) — a genuine naming smell independent of this
   move: these are storage-backend loaders, not concrete W3C syntax
   parsers, yet they carry the `Parser.*` prefix that otherwise means
   "N-Triples/Turtle/RDF-XML/etc." A future `Store.Ballyhoo*` rename
   would be more honest, but per "what NOT to do" below, module
   renames are explicitly out of scope for the directory move —
   record the idea here, do it as its own commit if ever done.
8. **`Parser.JSONLD.fst` vs `JSONLD.Context/Expand/Loader.fst`** — not
   actually a problem, included here because it's worth naming as the
   positive case: `Parser.JSONLD` (concrete syntax, → `parsers/`) and
   the JSON-LD *algorithm* (context resolution, expansion, remote
   loading, → `standards/jsonld/`) are already cleanly separated at
   the module level. The folder split just makes visible a boundary
   that was already correct.

## 3. Migration mechanics

Every place in this repo that assumes `formal/fstar/` is flat, found
by reading the actual scripts (not guessed):

### `formal/fstar/build-ocaml.sh` (1,803 lines, cwd = `formal/fstar`)

- **`ALL_MODULES` array** (lines 357–456, ~96 bare filenames) — the
  extraction-order/manifest-cleanup list. Every entry needs its new
  relative path prefix (e.g. `Parser.NTriples.fst` →
  `parsers/Parser.NTriples.fst`).
- **`*.fsti` pre-check glob** (lines 490–498, `FSTI_FILES=(*.fsti)`) —
  a flat shell glob; must become a recursive `find . -name '*.fsti'`
  or an explicit list mirroring the new `.fsti` locations
  (`terms-and-graphs/RDF.Vocabulary.fsti` etc., 8 files today).
- **`fstar.exe --dep full "${PRESENT_MODULES[@]}"`** (line 515) and
  **every per-module `extract_worker` invocation** (line 603) — need
  a `--include <dir>` per subfolder added to the command line. Cleanest
  fix: compute one `FSTAR_INCLUDES=(--include foundations --include
  terms-and-graphs --include parsers --include sparql --include
  sparql/plan --include sparql/http --include store --include
  store/cottas --include store/hdt --include standards/owl ...)`
  array once near the top of the script and splice it into all four
  call sites (`.fsti` pre-check, `--dep full`, `extract_worker`, and
  the karamel step below) rather than hand-duplicating includes.
- **karamel pilot step** (lines 114–154, `STEP == "karamel"`) — its
  own hardcoded 5-filename list (`SPARQL.JSON.Escape.fst`,
  `SPARQL.Update.Analysis.fst`, `SPARQL.Query.Analysis.fst`,
  `SPARQL.HTTP.StaticFiles.fst`, `SPARQL.HTTP.QueriesIndex.fst`) needs
  the same path-prefix + `--include` treatment.
- **`COMMON_MODULES`** (line 766) and **`FSTAR_MODULES`** (lines
  1329–1401) — these are **`.ml` names** (dots already converted to
  underscores, e.g. `RDF_Term.ml`) used only to reference
  `$OUTDIR` (`ocaml-output/`, which stays flat per Iron Rule #9/#11 —
  extraction output is module-name-keyed, not path-keyed, confirmed:
  `fstar.exe --codegen OCaml --odir "$OUTDIR"` always writes
  `Foo_Bar.ml` regardless of where `Foo.Bar.fst` lives). **These two
  lists need no changes.** This is the one piece of good news: moving
  `.fst` source files does not touch `ocaml-output/`, `bin/*`, or any
  compile/link step downstream of extraction.

### `formal/fstar/Makefile`

- `MODULES = RDF.Graph.Executable SPARQL11.Algebra Tableau
  SPARQL.ServiceDescription SPARQL.GraphStore` and the pattern rule
  `%.verified: %.fst` — `make`'s pattern rules match on the full
  relative path, so `MODULES` entries need their new prefixes
  (`terms-and-graphs/RDF.Graph.Executable`, `sparql/Tableau`... wait,
  `Tableau.fst` → `standards/owl/Tableau.fst`, etc.) and `$(FSTAR) $<`
  needs the same `--include` set as above.
- `extract-c: c-output/RDF_Graph_Executable.c` /
  `c-output/RDF_Graph_Executable.c: RDF.Graph.Executable.fst` — the
  krml prerequisite path needs updating to
  `terms-and-graphs/RDF.Graph.Executable.fst`; verify krml's own
  include-search behavior separately during the pilot (not yet
  exercised by this repo's karamel usage against a subdirectory).

### CI workflows (`.github/workflows/`)

- **`check-extraction.yml`** — `paths: ['formal/fstar/*.fst', ...]`
  (line 6, won't fire on changes inside a subfolder) and the
  `.checked` cache `path: formal/fstar/*.fst.checked` /
  `key: ...${{ hashFiles('formal/fstar/*.fst', 'formal/fstar/*.fsti') }}`
  (lines 39–40) — all need `**/*.fst` / `**/*.fsti` globs.
- **`check-derived-files.yml`** — `paths: ['formal/fstar/ocaml-output/*.ml']`
  is unaffected (flat, stays flat), but the internal
  `git diff --name-only ... -- 'formal/fstar/*.fst' ...` (line 41)
  needs the recursive glob too, or a module move with no content
  change would misfire as "no F* source changed" and block a
  legitimate re-extraction-free `.ml` diff (there shouldn't be one
  during a pure move, but the check's logic depends on this glob
  matching the moved files).
- **`debug-bytecode-build.yml`** — already triggers on `formal/fstar/**`
  (line 7), already recursive, unaffected.
- **`dashboard-refresh.yml`**, **`w3c-tests.yml`** — reference only
  `ocaml-output/` / `ocaml-output-ci/` paths (flat, unaffected).
- **`check-ocaml-output-cleanliness.yml`**, **`check-fstar-purity.yml`**
  — reference `ocaml-output/*.ml` and `experimental_ocaml_glue/*.sh`
  (flat, unaffected — neither directory is part of this move).

### Patch scripts / glue directories

`ocaml-patches.sh`, `experimental_ocaml_glue/*.sh`,
`minimal_regrettable_glue_code_each_with_an_open_issue/*.sh` — grepped
for hardcoded `.fst` paths outside `ocaml-output/`: the only hits are
**prose comments** (e.g. `67_rdfxml_validation.sh` says "lives in
formal/fstar/XML.Wellformedness.fst"), not executable path
dependencies. These scripts patch `.ml` files in `ocaml-output/` by
name, which is flat and unaffected. Comments referencing the old flat
path should be updated for accuracy but don't block anything.

### F* MCP daemon (`.mcp.json`, `tools/fstar-mcp-server.sh`)

HTTP transport, no hardcoded file paths — `ROOT` is computed via
`git rev-parse --show-toplevel`. Unaffected. The daemon's *queries*
(via `fstar-mcp` skill) will need whatever `--include` set the
project settles on, same as any interactive `fstar.exe` invocation —
worth a one-line addition to `skills/mcp-setup-readme/SKILL.md` once
the folders exist, not a design concern now.

### Dependency-graph tool (`docs/web/demos/dep-graph/`)

No generator script is committed in the tree — the `.dot`/`.mmd`/
`.json`/`.txt` artifacts under `docs/web/demos/dep-graph/` were
produced ad hoc from `fstar.exe --dep graph`, and they key entirely on
**dotted module names** (`RDF.Graph.Executable`, not a file path).
Confirmed: `modules.txt` header says "80 modules, 139 in-project
edges" — stale relative to today's 134 modules, so this artifact
already isn't regenerated automatically; whoever refreshes it next
does so by module name regardless of directory layout. **Unaffected**
by the move — good news, since module identity
(not file location) is the thing every downstream tool actually keys
on.

### `.checked` cache mechanics — the real cost, precisely

Two caches exist, both currently **flat-path-shaped**:

1. **Local machine cache** (`formal/fstar/*.fst.checked`, gitignored).
   Confirmed experimentally: moving a module's `.fst` **and** its
   already-valid `.fst.checked` together, then re-running with an
   updated `--include`, leaves both the moved module's own `.checked`
   file *and* every dependent's `.checked` file untouched (same
   mtime, same content) — no cascading re-verify. **This means a
   migration commit done with a warm local cache, where the mover
   also moves each `.fst.checked` alongside its `.fst` in the same
   `git mv`-adjacent operation, costs nothing in re-verification
   time**, provided every `--include` is updated correctly in the
   same commit.
2. **`checked-cache` git branch** (`tools/install-toolchain-cache.sh`
   step 4b) and **CI's `check-extraction.yml` cache** (keyed on
   `hashFiles('formal/fstar/*.fst', ...)`) are both **flat by
   construction** — the toolchain-cache tar is extracted with
   `tar -C "$REPO_ROOT/formal/fstar" -xzf ...` (flat target dir) and
   its own trigger check
   (`[ ! -e "$REPO_ROOT/formal/fstar/RDF.Graph.Executable.fst.checked" ]`)
   hardcodes a flat path. After the move, that flat path never exists
   again, restoration becomes a no-op-that-looks-like-a-hit
   (extracted files land at the wrong, no-longer-matching paths), and
   the **first cold run** — locally on a fresh clone, or the first CI
   run against the new paths — pays the full ~2 hour re-verify that
   `session-restore` already documents as the cache's entire reason
   to exist. This is a **one-time toll paid once, by the wave that
   completes the full migration** (or by the pilot, at pilot scale,
   which is small enough to not matter) — after that toll, a fresh
   `checked-cache` snapshot gets captured from the new gates-green
   state (same "orphan branch, gates-green only" rule as any other
   cache refresh) and restoration is fast again.

**Net verdict:** the migration itself is verification-cost-neutral in
the steady state; it costs exactly one full cold re-verify to migrate
the two out-of-tree caches to the new paths, timed to land in the
wave that finishes the move (or absorbed cheaply during the pilot).

### Git history

Use `git mv` per file (not delete+recreate) so `git log --follow`
and `git blame` survive the move. Bash's `git mv dir1/*.fst dir2/` works
per-file; for a wave touching N files, a small script doing
`git mv "$f" "$dest/$f"` per list entry is more auditable in a PR diff
than a bulk `git mv formal/fstar/*.fst formal/fstar/newdir/`.

## 4. Staged rollout

**Pilot: the HDT cluster (`store/hdt/`, 5 files).** Recommended over
the XPath/XML pair for three reasons, checked against the actual
dependency data (`formal/fstar/ocaml-output/.extract-state/depend-joined.make`,
a real `fstar.exe --dep full` run already cached in this tree — the
committed `docs/web/demos/dep-graph/modules.txt` snapshot is stale,
80 modules vs 134 today, so it was not used for this call):

- Smaller: 5 files (`HDT.Container`, `HDT.Dictionary`, `HDT.Triples`,
  `Parser.BallyhooHDT`, `Parser.BallyhooHDTQ`) vs. the XML/XPath pair's
  5 files with a messier external fan-out (`Parser.RDFXML`,
  `Parser.SRX`, `Parser.RIFXML`, `RIF.Core.Conformance` all depend
  directly on `Parser.XML`).
- The whole HDT cluster can move as **one atomic unit**: internally
  `HDT.Container → HDT.Dictionary → HDT.Triples`,
  `Parser.BallyhooHDT → {HDT.Container, HDT.Dictionary, HDT.Triples}`,
  `Parser.BallyhooHDTQ → Parser.BallyhooHDT`. The only edge crossing
  the new folder boundary is `SPARQL11.Store.fst` (destined for
  `sparql/`) depending on `Parser.BallyhooHDT.fst` (destined for
  `store/hdt/`) — exactly **one** cross-folder `--include` to prove
  the mechanism works end to end, not zero (a zero-edge pilot would
  under-test the real risk) and not dozens (which would make a first
  attempt hard to debug).
- It touches all three build-list sites at once at small scale:
  `ALL_MODULES` (5 entries get path prefixes), the `.fsti` glob (no
  `.fsti` files in this cluster — confirms the pilot doesn't
  accidentally dodge that site, it just has nothing to change there),
  and `SPARQL11.Store.fst`'s dependency resolution needs the new
  `--include store/hdt`.

**Pilot gate:** full suite green — `./build-ocaml.sh extract` (all
142 modules, not just the 5 moved — a bad `--include` can silently
break resolution for files that didn't move if the include list is
malformed), `compile`, `test`, plus the W3C HDT-relevant suites
(`w3c_runner`) unchanged pass count. Only after this gate does the
next wave start.

**Wave plan after the pilot** (5 further waves, one folder-cluster
each, in dependency-depth order — shallowest/most-independent first
so early waves have the fewest cross-folder edges to get right while
the process is still being learned):

1. **`foundations/`** (10 files) — everything else depends on these,
   nothing here depends on anything outside itself. Highest edge
   count *outbound* (every other folder will need `--include
   foundations`), zero inbound risk.
2. **`terms-and-graphs/`** (24 files, HDT's `RDF.Graph.Executable`
   dependency already covered by wave 1's include) — second because
   nearly everything downstream needs it; verifies the `--include`
   list scales past 2 folders correctly.
3. **`parsers/`** (19 files) — depends on foundations + terms-and-graphs
   only (plus the already-moved `store/hdt` for nothing — no parser
   depends on HDT).
4. **`store/`** minus the already-moved `store/hdt/` (29 files:
   13 top-level + 16 `cottas/`) — depends on foundations +
   terms-and-graphs + parsers (Ballyhoo loaders touch
   `Parser.NTriples`/`Parser.Combinators`).
5. **`standards/`** (25 files across 8 sub-clusters) — each
   sub-cluster (`owl/`, `shacl/`, `shex/`, `rif/`, `rml/`, `jsonld/`,
   `csvw/`, `vc/`) can land as its own commit within the wave since
   they don't depend on each other; do them in any order.
6. **`sparql/`** (30 files across 3 sub-clusters) — last, because it
   has the widest fan-in from every other folder (algebra, parser,
   protocol, planning all sit on top of the full stack) — moving it
   last means every `--include` it needs already exists from prior
   waves, so this wave only adds `sparql/`, `sparql/plan/`,
   `sparql/http/` to the include list, nothing retroactive.

Each wave's gate is the same as the pilot's: full extract + compile +
test, floors unchanged (no suite regresses versus the measured
baseline immediately before the wave). Estimated risk per wave:

| Wave | Files | Cross-folder edges introduced | Risk |
|---|---|---|---|
| Pilot (`store/hdt/`) | 5 | 1 | Low — small, single edge, easy to debug if wrong |
| 1 `foundations/` | 10 | many outbound, 0 inbound | Low — pure leaf, but every later wave's `--include` depends on this one being right |
| 2 `terms-and-graphs/` | 24 | high fan-in from later waves | Medium — largest single wave by LoC (includes `RDF.Graph.Executable`) |
| 3 `parsers/` | 19 | moderate | Low-medium — parsers are mostly leaves themselves |
| 4 `store/` remainder | 29 | moderate | Medium — `RDF.CottasStore.*` internal graph is dense (14+ mutually-referencing files) |
| 5 `standards/` | 25 | low (mostly self-contained sub-clusters) | Low — 8 independent sub-moves, easy to bisect a failure |
| 6 `sparql/` | 30 | 0 new (all prior includes already exist) | Medium — largest wave, includes the `SPARQL11.Algebra` monolith and the widest test-suite fan-out (every SPARQL W3C suite touches this folder) |

**Rollback note:** every wave is one `git revert` away from the prior
green state, because each wave is a pure path change (no content
edits) plus mechanical `build-ocaml.sh`/`Makefile`/CI updates in the
same commit — reverting the commit restores the flat layout and the
old scripts atomically. The only non-trivial rollback cost is the
`.checked` cache: a revert after a wave's cold re-verify has already
happened means the *next* session pays another cold re-verify to get
back to the flat-path `.checked` set, unless that flat-path snapshot
was kept (tag it before wave 1 starts, just in case).

## 5. What NOT to do

- **Do not rename modules in this pass.** `RDF.Term` stays
  `module RDF.Term` regardless of which folder `RDF.Term.fst` lives
  in — F* module names are declared inside the file
  (`module RDF.Term`), not derived from the folder path, so nothing
  *requires* a rename, and doing one anyway would conflate two
  unrelated risks (a path change everyone can `git mv`-revert
  trivially, vs. a semantic rename that touches every `open` site).
  The `Parser.Ballyhoo*` naming smell (finding #7 above) is exactly
  the kind of thing to fix *separately*, later, as its own reviewed
  commit.
- **Do not mix the move with stratification splits.** `RDF.Graph.Executable`
  and `SPARQL11.Algebra` both have standing "split this file"
  entries in the roadmap (finding #1 and #2 above) — folder-move
  commits touch zero lines of `.fst` content; splitting a monolith
  touches many. Doing both in one commit makes a failed suite run
  undiagnosable (which change broke it, the move or the split?).
- **Do not touch `ocaml-output/` layout.** Confirmed above:
  `fstar.exe --codegen OCaml --odir ocaml-output` names its output
  files from the **module name**, not the source path
  (`RDF.Term.fst` anywhere on disk still extracts to
  `ocaml-output/RDF_Term.ml`). `ocaml-output/`, `ocaml-output-ci/`,
  `bin/*`, and every hand-written OCaml consumer are unaffected by
  this migration and should stay exactly where Iron Rule #9/#11 put
  them — flat, committed, reserved for extraction output and glue.

## 6. Aesthetics — what "clean abstraction vs impl grunge" means here

Operationally, the folder tree itself becomes the abstraction map: a
newcomer (or a future agent) reading `formal/fstar/` sees six names —
`foundations`, `terms-and-graphs`, `parsers`, `sparql`, `store`,
`standards` — before reading a single line of F*, and each name
answers "what tier is this, and which W3C concern does it belong to"
without opening the file. The `.fsti` interface files
(`RDF.IRI`, `RDF.Term`, `RDF.Triple`, `RDF.Graph`, `RDF.Vocabulary`,
`RDF.Indexed`, `RDFS.Closure`, `OWL.Closure` today) sit inside
`terms-and-graphs/` as the readable surface of that folder — the
"what this abstraction means" layer the `fstar-module-style` reading-
order convention already prescribes file-by-file, now also true
folder-by-folder. The genuinely grungy parts — `experimental_ocaml_glue/`,
`minimal_regrettable_glue_code_each_with_an_open_issue/`,
`ocaml-output/`, `c-output/` — are already quarantined at the bottom
of the tree by name (their names *say* "regrettable" and
"experimental"); this move just stops the ~142 spec files that
represent the actual product from sitting in the same flat pile as
that quarantine, so the directory listing itself communicates "this
part is the spec, that part is acknowledged debt" before anyone reads
a docstring. A natural follow-up, once the folders exist and are
stable, is generating one `assume val` inventory per folder (a
per-store, per-parsers, per-standards table rather than one repo-wide
list) so the "acknowledged gap" ledger Iron Rule #3 requires reads at
the same granularity as the tree it audits.
