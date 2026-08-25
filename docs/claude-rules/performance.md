# Performance status and history

Operational guidance for measuring and recording performance lives in
[`skills/perf-benchmarking/SKILL.md`](../../skills/perf-benchmarking/SKILL.md).
This file records where the engine stands and how it got here.

## Current status (measured 2026-07-03)

The Turtle path is no longer the bottleneck it was. Against the
committed `bin/linux-x86_64/factoidal` (`--count`, median of 3, cloud
container):

| N triples | Time | Rate |
|-----------|------|------|
| 1,000 (prefixed) | 0.02 s | ~50k triples/s |
| 1,000 (full-IRI) | 0.04 s | ~25k triples/s |
| 100,000 | 0.93 s | ~108k triples/s |
| 1,000,000 | 9.66 s | ~104k triples/s |

Large-file check (2026-07-04, committed linux-x86_64 binary): 500MB
Turtle (10,117,857 triples) parses via the streaming count path in
195s (~52k triples/s) at 971MB peak RSS; the fully-materialised
load-and-query path measured 69s / 1.99GB RSS at 100MB (~1KB/triple),
extrapolating to ~10GB RAM for 500MB — use `cottas-import` + the
persistent artifact at that scale instead.

Scaling is near-linear through 1M triples. Re-measure with
`formal/fstar/bench-turtle-metrics.sh` (or the committed binary + the
same fixtures) before quoting these; update this table when you do.

For data at rest, still prefer the binary backends (HDT triples,
COTTAS quads) over re-parsing text — see the caveats in
`docs/designissues/2026-04-19-hdt-fstar-status.md` (the HDT path is
interface-only in F\* and shells out to `hdtSearch`; COTTAS has the
substantial verified `Parquet.Footer` reader).

The walls have moved, not vanished. In-memory: compliant and, since
the #259 sort-and-group `build_indexed` fix, **linear** — measured
2026-07-03: the lifesci Q01 that took 137s in the
`2026-05-01-perf-fast-path-vs-load.md` incident now runs in 2.2s on
the same 43k quads; 1M quads end-to-end (parse + index + GRAPH-count)
in ~41s at ~1.2 GB peak RSS. The remaining in-memory walls are the
~25k quads/s end-to-end constant and ~1.2 KB RAM per quad. On-disk
COTTAS: serves the 3.14M-quad UK Parliament corpus, but only via the
unverified OCaml runtime override whose retirement is scoped in
`2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md`.
The current-walls summary lives in
[`skills/perf-benchmarking/SKILL.md`](../../skills/perf-benchmarking/SKILL.md)
§ "Scaling status".

## OWL 2 DL suite wall-clock (measured 2026-07-15)

Measured on the merged tree of the Wave-B (dateTime facets) and
Z33kr-Phase-0 landings, freshly rebuilt binaries, remote container,
`FACTOIDAL_OWL_CAP_SEC=20`, single run each
(`.claude-runs/z33kr-land-gates-owl.log`):

- type-inconsistency (DL regime): **43.1s** for 112 pass, 16 fail
  (out of 128). Confirms the svf2 depth-cap landing's claim
  (`2e4e328e`, 141s → 45s) still holds on the current tree; the
  Wave-B facet rules and the Phase-0 recogniser module add no
  measurable cost (43.1s vs the 44.8s pre-Wave-B baseline).
- type-consistency catalog (DL regime): **7m 33.8s** total —
  PE 121.8s (103 pass, 101 fail out of 204), NE 9.5s (22 pass,
  1 fail out of 23), Cons 321.7s (334 pass, 18 fail out of 352).
  The consistency phase dominates; it is the next timing target if
  OWL suite wall-clock needs to shrink.

## Corpus: QUDT v3.4.0 all-in-one (SHACL-at-scale, measured 2026-07-10)

`third_party/qudt/QUDT-all-in-one-SHACL.ttl` (6,791,181 bytes,
131,169 triples) is the project's first real-ontology-scale SHACL
corpus (vendored for the `qudt` suite —
`docs/designissues/2026-07-10-qudt-scoping.md` Layer A). Committed
`bin/linux-x86_64` binaries, cloud container, single runs:

| Operation | Time |
|-----------|------|
| Parse + count (`factoidal count`) | 1.8 s (~74k triples/s) |
| `SHACL_Validation.validate`, empty shapes graph (fixed cost: class closure + distinct-subjects + report plumbing) | 20 s |
| Cheapest `sh:sparql` ruleset shape (176 focus nodes via `sh:targetSubjectsOf qudt:currencyNumber`) | >419 s (cap trip ⇒ >2.4 s/focus) |
| QUDT user ruleset (5 sh:sparql shapes) over the full distribution | >570 s (cap trip) |

`qudt:Concept`-targeting shapes have 11,510 SHACL instances after
subclass closure; every shape in the contributor ruleset targets
≥176 focus nodes, so none completes within the 10-minute cap.
The wall is per-focus-node SPARQL-constraint evaluation:
`SHACL.Validation.fst` re-parses and re-evaluates each `sh:sparql`
query per focus node over the list-represented data graph, so a
wide-target shape costs (foci × query-eval-over-131k-triples). This is
the standing perf finding behind the `qudt-integrity` suite's
budget-skips (`.github/test-suites/qudt.yaml` `remaining:`); an
indexed/pre-compiled evaluation path for SPARQL constraints is a
perf-program work item. Correctness is unaffected (shacl-sparql
22 pass, 0 fail).

## History: the slow-Turtle era (2026-04, fixed)

Measured 2026-04-17, same fixtures: 1,000 triples took 25 s
(~40 triples/s), 10,000 took >8 minutes (killed), 35.8 MB never
finished — super-linear scaling. Two root-cause passes were needed:

1. Parser-side taxes
   (`docs/designissues/2026-04-19-turtle-parser-speed.md`):
   `nat` positions extracting to GMP `Z.t`, eager `span_to_string`
   per token, O(n) list append in the grammar folders.
2. The dominant cost, found later
   (`docs/designissues/2026-04-24-turtle-parser-perf-diagnosis.md`):
   Θ(N²) dedup-scan + tail-append in `graph_add`/`mem_triple` in
   `RDF.Graph.Executable` — not in the parser at all.

Both were fixed in F\* (byte-indexed `Parser.FastString` hot paths,
deferred span materialisation, bulk prepend + one-shot
canonicalisation). The durable lessons — profile before blaming the
tokenizer; F\* data-structure and extraction choices dominate at
scale; fixes land in F\*, not OCaml patches — are captured in the
`perf-benchmarking` skill.

## Standing rules

- Ad-hoc parse/query tests MUST be capped at 10 minutes per rule #17
  (see `anti-patterns.md`).
- Never claim a speed win unless it was measured separately from a
  compliance change.
- Never leave a perf claim in a doc without a date and a binary
  provenance.

## Persistence program (owner, 2026-08-25) — verbatim

Recorded verbatim because these set the direction for all storage
work; paraphrase drifts. Context the owner gave with them: COTTAS has
consumed many files and lines against little demonstrated payoff; HDT
has traction but is triples-only; "until we have a credible
persistence solution our toolkit is just a nice-to-have set of
utilities rather than the heart of anyones data operation."

> My persisitence plans are:
>
> 1. Become one of a handful of most performant and scaleable rdf
>    databases
> 2. Implement bit for bit perfect replicas for common rdf on disk
>    storage/indexing patterns, where documented.
> 3. Be corpus/datarepo centric: allow for named graphs to be at rest
>    on disk and OPTIONALLY and CLEVERLY brung up into "hot" use
>    (indicices loaded, caches warmed and in memory) such that the
>    full corpus might be many times larger than what we might expect
>    from a normal rdf db. Yet useful working subsets sliced and
>    diced to remove the pain of deciding which named graphs to have
>    hot warm or cold.
> 4. Allow for NGs to be further decomposed into large sets of
>    instantiated shapes such that a geaph g1 might be covered by
>    1000000 pccurences of shape sh632 sh734 etc.
> 5. Be comparable in perf to the likes of Qlever and adopt all
>    public opensource and published perf best practices from high
>    perf systems including compact IDs.

And the wasm memory-layout direction, same message, verbatim:

> Next: wasm to js bridge is limited (cf js to webgpu) and slightly
> reminiscent of other bytes to code situations like those of binary
> disk formats eg hdt, cottas. Consider if in memory wasm layout of
> rdf quads could be same as disk layout and whether memory mapping
> style techniques could allow subdatasets / nquads to be pages in
> and out of use. Add this to perf.md doc too.

### Analysis (Claude, 2026-08-25 — inferred, not owner-decided)

Plan-by-plan reading, with the published practice each one points at:

- **Plan 2 (bit-perfect replicas of documented formats).** Realistic
  targets in order of documentation quality: HDT (spec published; we
  already read `.hdt` bytes on three surfaces), QLever's index
  layout (open source, undocumented-but-readable), Jena TDB2
  (partially documented). This plan fits the repo's existing
  discipline exactly: byte formats specified in the formal source
  (rule #11 Option-B, hash-witness CI), so a "replica" is a proved
  serializer against a foreign reader, not a resemblance.
- **Plan 3 (corpus-centric hot/warm/cold named graphs).** Needs a
  graph-level manifest (which graphs exist, sizes, index state) with
  lazy per-graph index construction. The existing symlink-current
  compaction layout and delta log already separate immutable base
  from mutation; the missing piece is per-named-graph granularity
  and an eviction/warming policy. The wasm dataset-handle API
  (issue 585) is the natural in-memory face of the same lifecycle.
- **Plan 4 (graphs decomposed into instantiated shapes).** This is
  the step that makes Parquet a principled choice instead of an ad
  hoc one: a shape occurrence is a ROW whose columns derive from the
  shape, so shape-decomposed storage IS columnar storage. The
  published literature calls the unsupervised version of this
  "characteristic sets" (Neumann & Moerkotte) and property tables;
  Factoidal's difference is that SHACL shapes make the schema
  explicit, validated, and queryable. Candidate layout: one Parquet
  row-group family per shape id, plus a residual triples table for
  whatever no shape covers — coverage is then a measurable number
  per graph.
- **Plan 5 (QLever-class performance, compact IDs).** The published
  practices to adopt, in dependency order: dictionary-encoded
  compact integer IDs (interacts with the FastString re-founding);
  sorted, delta-compressed permutations over those IDs (RDF-3X /
  QLever pattern); vocabulary kept on disk with only the
  frontier in memory; join orders from cardinality estimates over
  the permutations. Each is measurable in isolation; per
  `skills/measuring-inference` and anti-pattern #28, adopt only
  with a benchmark that can see the failure.

**Unified disk/memory layout for wasm.** The observation holds: wasm
linear memory is a flat byte array, and the current Lean-heap
representation of a dataset (boxed objects, pointers, GC) is the
opposite of a disk format, which is why bytes are re-serialized at
every boundary today. If the quad-store layout is defined once as a
position-independent (offset-based, little-endian, page-aligned)
byte format in the formal source, then:

1. disk file, HTTP response body, JS `ArrayBuffer`, and wasm linear
   memory all hold the SAME bytes — load is a copy, not a parse;
2. "memory mapping" in wasm, which has no real `mmap`, becomes
   manual paging: copy in only the pages a query touches (browser:
   HTTP Range requests; Node: `fs.read` at offsets), evict by
   dropping page refs — which is also exactly plan 3's hot/warm/cold
   mechanism at page granularity rather than graph granularity;
3. the engine queries the flat buffer through a verified accessor
   layer (the store lives OUTSIDE the Lean/OCaml heap, reached
   through the existing C shim, so the GC never walks it);
4. HDT already proves the pattern viable for triples — its succinct
   in-memory structure is its on-disk structure; the work here is
   the quads + named-graph + shape-table generalisation.

Costs to respect: a fixed endianness and versioned page header;
mutation via the existing delta log over immutable base pages (never
in-place writes); and the accessor proofs are the price of zero-copy
— without them this is exactly the "bytes to code" hazard the owner
names.

Tracking: https://github.com/danbri/factoidal/issues/595 (program
issue; supersedes ad hoc COTTAS scope decisions, links
https://github.com/danbri/factoidal/issues/579).

### Baseline (measured 2026-08-25, quad-store import/query, workstream A of #595)

Environment: container Linux 6.18.44-fc-v21, x86_64, 4 vCPU. Binary
`bin/linux-x86_64/factoidal`, sha256
`9934f3506d1463d45252eff6df275d22c2667edca03c8b44d207b691ec6ad3cd`, built
at commit `5e3e4667b66b7ecb28514620be026220c6ed8f44` (2026-08-17), run
against measurement commit `abd7ff61cfbe86b1be4cf507d6ab8c3d84abb6d9`.
Harness: `tools/bench-quadstore-baseline.sh` (median of 3 runs, 120s
cap per run, no F\* toolchain). Full data:
[`docs/test-results/perf-quadstore-baseline.json`](../test-results/perf-quadstore-baseline.json).
Fixtures: deterministic synthetic N-Quads, 4 quads per subject
(2 properties + 1 chain predicate `next` + 1 more property), 10k/100k/1M
default-graph quads plus a quads100k variant split across 4 named
graphs.

**QLever probe (15-minute timebox).** `pip install qlever` succeeds —
it installs only the Python control script. `qlever index --system
native` fails: `qlever-index: command not found` — the QLever C++
binaries are not shipped by the pip package and are not present in
this container. The package's default, `--system docker`, cannot
reach a daemon either: `docker ps` reports `dial unix
/var/run/docker.sock: connect: no such file or directory`. No native
or containerized QLever run was possible here; a same-hardware
QLever-vs-Factoidal comparison needs a container with either a
prebuilt QLever binary or a working Docker daemon — noted as a CI
candidate on issue #595, not attempted further under the timebox.

**Finding: `factoidal cottas-import`'s own output is unreadable by
this binary.** Issue #445 (2026-08-15, landed 10 days before this
baseline) added a format-compatibility gate
(`RDF.CottasStore.cottas_ondisk_version_ok`) that accepts only stores
whose Parquet `FileMetaData.version` field carries
`Parquet.Footer.cottas_format_version` (445) — a value only the
native F\* writer (`RDF.CottasStore.BaseWriter.fst`, invoked via
`factoidal import`) stamps. The pycottas/DuckDB writer behind
`factoidal cottas-import` writes the Parquet-conventional version
field, so `cottas_ondisk_open` rejects every store it produces:
`was not written by this store's current writer (FileMetaData version
mismatch)`. Two consequences measured directly, not inferred:

- `factoidal cottas-import --build-sidecars` **fails outright** (exit
  1) at every size tested (10k/100k/1M/quads100k): eager sidecar
  building self-queries the store it just wrote via `--explain`, and
  that query is rejected by the same gate. The base `data.cottas` file
  is written successfully before the failure (its bytes are still
  reported below), but the whole `cottas-import` invocation returns
  nonzero and no sidecars exist.
- `factoidal cottas-import` without `--build-sidecars` exits 0 and
  writes a `data.cottas` file, but that file cannot be opened by
  `factoidal query --data-cottas` on this binary at all — confirmed
  once against the 10k store, cited (not re-tested per size; the gate
  is unconditional on writer identity, not data size).

Query latency "through the store path" below therefore uses the
**native writer** (`factoidal import --nq FILE --out DIR`) exclusively
— it is the only writer whose output this binary opens.
`cottas-import`'s numbers below are cold-import time and on-disk size
only.

**Import.** Seconds are median of 3; peak kB is `RUSAGE_CHILDREN.
ru_maxrss`, max of the 3 runs (a peak of peaks, not a median).

| Writer | Sidecars | Dataset | Quads | Seconds | Peak RSS | `data.cottas` bytes | Sidecars bytes |
|---|---|---|---|---:|---:|---:|---:|
| pycottas (`cottas-import`) | no | 10k | 10,000 | 1.76 | 153 MB | 10,193 | — |
| pycottas | no | 100k | 100,000 | 12.28 | 352 MB | 73,698 | — |
| pycottas | no | 1M | 1,000,000 | 66.98 | 1,812 MB | 704,704 | — |
| pycottas | no | quads100k | 100,000 | 14.15 | 382 MB | 73,924 | — |
| pycottas | yes | all 4 sizes | — | — | — | (base written; see above) | **SKIP: exit 1, issue #445 self-query rejection** |
| native (`import`) | no | 10k | 10,000 | 0.71 | 59 MB | 377,799 | — |
| native | yes | 10k | 10,000 | 0.79 | 59 MB | 377,799 | 646,508 |
| native | no | 100k | 100,000 | 7.98 | 415 MB | 3,898,116 | — |
| native | yes | 100k | 100,000 | 9.10 | 415 MB | 3,898,116 | 6,585,570 |
| native | no | 1M | 1,000,000 | 95.76 | 2,049 MB | 40,120,436 | — |
| native | yes | 1M | 1,000,000 | — | — | 40,120,436 (base written) | **SKIP: exceeded 120s cap** |
| native | no | quads100k | 100,000 | 9.75 | 404 MB | 3,945,718 | — |
| native | yes | quads100k | 100,000 | 9.85 | 422 MB | 3,945,718 | 6,585,691 |

Two scaling directions, opposite sign, both measured not assumed:
pycottas throughput RISES with size (5,680 quads/s at 10k to
14,930 quads/s at 1M — fixed DuckDB/subprocess startup cost amortizing
away); native-writer throughput FALLS with size (14,164 quads/s at 10k
to 10,443 quads/s at 1M) and the native writer is slower than pycottas
in absolute terms at 1M (95.76s vs 66.98s) despite running in-process
with no subprocess/DuckDB overhead. Cause not diagnosed here (report
only, per task scope) — candidate for the layout RFC or a follow-up
profiling pass.

On-disk size: pycottas' zstd-compressed output is far smaller than the
native writer's uncompressed output on this fixture — 0.70 B/quad
(pycottas, 1M) vs 40.12 B/quad (native, 1M), a 57x gap. The fixture's
long, highly-repetitive IRI strings (`http://example.org/oN-<index>`)
favor dictionary compression disproportionately; this ratio is a
property of this synthetic corpus's string entropy, not a
general claim about the two writers. Sidecar overhead (native writer,
where measured): sidecars run 1.67-1.69x the base file's own size
(100k: 6,585,570 sidecar bytes vs 3,898,116 base; quads100k:
6,585,691 vs 3,945,718) — the 1M sidecar figure is the timeout skip
above, not a silent omission.

Named-graph segmentation cost: quads100k (100,000 quads across 4
named graphs) took 9.75s to import (native, no sidecars) against
7.98s for the same quad count in the default graph — a 22% cost
attributable to graph-splitting alone at this scale, on this binary,
today.

**Query latency: store path (native writer) vs in-memory path**,
same three fixed queries against the same underlying quads, seconds
median of 3, peak RSS max of 3 (sidecars=false rows shown; sidecars
=true numbers are in the JSON and track within ±10% of these):

| Dataset | Query | Store seconds | Store peak RSS | Memory seconds | Memory peak RSS |
|---|---|---:|---:|---:|---:|
| 10k | q1 point lookup | 0.22 | 20 MB | 0.26 | 21 MB |
| 10k | q2 star join | 0.28 | 20 MB | 0.24 | 21 MB |
| 10k | q3 two-hop path | 0.20 | 20 MB | 0.27 | 25 MB |
| 100k | q1 | 1.67 | 72 MB | 2.46 | 89 MB |
| 100k | q2 | 1.58 | 72 MB | 2.60 | 89 MB |
| 100k | q3 | 1.61 | 72 MB | 3.11 | 144 MB |
| 1M | q1 | 4.14 | 152 MB | 26.73 | 855 MB |
| 1M | q2 | 4.37 | 146 MB | 29.86 | 855 MB |
| 1M | q3 | 5.54 | 187 MB | 41.81 | 1,402 MB |
| quads100k | q1 | 2.02 | 67 MB | 2.80 | 78 MB |
| quads100k | q2 | 2.35 | 71 MB | 2.84 | 78 MB |
| quads100k | q3 | 2.44 | 67 MB | 3.14 | 126 MB |

At 10k and 100k the store and in-memory paths are within the same
order of magnitude (a roughly 0.2s fixed process-startup cost
dominates both at 10k). At 1M the gap opens sharply: the store path is
6.5x (q1) to 7.6x (q3) faster than the in-memory path, and uses 5.6x
(q1) to 7.5x (q3) less peak RSS. The in-memory path's own seconds grow
faster than the query count would predict — q1 to q3 at 1M goes from
26.73s to 41.81s (1.56x) for a query that adds one join step, while
the store path's q1-to-q3 growth over the same step is 1.34x (4.14s to
5.54s). This in-memory SPARQL-evaluation growth is a distinct
operation from the known `dump-nq`/`canonicalize` superlinearity and
the RDF/XML stack overflow already flagged in
[`skills/perf-benchmarking/SKILL.md`](../../skills/perf-benchmarking/SKILL.md)
(measured 2026-07-04, on the parse/serialize path, not SPARQL
evaluation) — cited for context, not re-diagnosed as the same defect.
`sidecars=true` vs `sidecars=false` made no consistent measurable
difference on this fixture's query shapes (single-valued predicates
per subject; sidecar prune value is expected to show on
higher-predicate-cardinality corpora, not measured here).

**Extra corpora.** `third_party/data/ukparliament/*.trig` and
`examples/data/third_party/Berlin.ttl` are both absent from this
checkout — documented skips in the JSON's `import_skipped`, not a
silent omission.
