# On-disk F\* binary indexes + query optimization — deep dive

Date: 2026-07-11. Method: three read-only analysis passes over the F\*
source and the committed perf docs (storage layer, query-planning layer,
and the VC track are separate reports; VC is in
[`2026-07-11-vc-canivc-eecc-plan.md`](2026-07-11-vc-canivc-eecc-plan.md)).
Every claim here is either **verified now** (file:line read or grep run
this pass) or **cited from a dated doc** — the two are kept distinct.
This doc is the strengths / weaknesses / next-phase-goals assessment that
feeds the revised `/goal`.

## The shared north star

Two strategic pressures shape everything below, and the storage and query
layers share both:

1. **Drop the rule-#11 qualifier.** Until the boundary audit reaches zero
   `VIOLATION-SEM`/`MIXED` rows, every README/demo/talk carries the
   "on-disk backend has unverified OCaml-side optimization layers being
   migrated back to F\*" caveat (CLAUDE.md rule #11, epic #200). Storage
   and query are the two subsystems that still carry it.
2. **Full coverage is the foundation for the perf-research program.** The
   `/goal` frames measured, verified performance as the payoff of
   completeness. Storage + query is where "verified *and* fast" is won or
   lost — so the perf numbers below are first-class, not footnotes.

A third theme emerged from the analysis and ties the two layers together:
**Roaring and KaRaMeL-stratification are each a single change that
unblocks multiple debts** — see the unified roadmap (§4).

---

## 1. Storage / on-disk index layer

### 1.1 Architecture (verified this pass)

| Artifact | Magic | Indexes | Verified-F\* vs OCaml-shim |
|---|---|---|---|
| `data.cottas` (Parquet base) | `PAR1` | the quad set | Reader `Parquet.Footer.fst` = verified `Tot`. Native writer `RDF.CottasStore.BaseWriter.serialize_cottas_v2` (`:1076`, wired into `factoidal import`/`compact --native-writer` at `factoidal_cli.ml:1300`) = verified `Tot`, 0 `assume val`; general round-trip lemma admitted (base case only) |
| `.dict` ×4, `.presence` ×4, `.p.offsets`, `.po.presence` | `COTD`/`COTP`/`COTO`/`COPO` | dictionary / presence / offsets / compound-PO | **Byte-format spec in F\* with round-trip lemmas; production writer is a hand-written OCaml "Option B" re-implementation** (`experimental_ocaml_glue/*.sh`), checked only by SHA-256 hash-roundtrip on 4–5 fixtures each — the OCaml does not call the extracted F\* `serialize_*` |
| `data.deltalog` / `data.compacted-epoch` | `DLE1`/`DLB1`/`DLOG` / `CEP1` | append-only UPDATE log + epoch guard | Framing + merge-on-read: verified `Tot` (`DeltaLog.fst`, `DeltaMerge.fst`), 5 I/O `assume val`s under #282, realised 4 ways (Unix/C/wasm-IndexedDB/in-mem) |
| HDT container/dict/triples (`--data-hdt`) | HDT | read-only container | Verified F\* (`Parser.BallyhooHDT.fst`, landed 2026-07-06, shim deleted). Rank/select is naive O(n) (stage 3); indexed stage 5 not started |
| Roaring (`formal/roaring/`) | — | nothing in production | Pure F\* Phases A–D (1,101-line `Container.fst`); **not referenced by any `formal/fstar/*.fst`** — 4 phases from load-bearing |

### 1.2 Strengths (evidence-backed)

- **Crash-safety proven *and* measured**: `lemma_delta_entry_roundtrip` +
  `lemma_merge_on_read_matches_apply_entries`, plus 270/270 + 25/25 +
  25/25 SIGKILL-point clean recoveries.
- **Python removed from the store-creation path**: native F\* Parquet
  writer, DuckDB-byte-exact, wired into the CLI (contradicts the
  `disk-storage-format` skill's stale "not wired in" note — §3.3 of the
  storage report; an obsolescence-sweep fix).
- **Density**: in-mem bytes store 64.4 B/quad (COUNT) / 160.9 (lookup) vs
  877 B/quad heap — ~13.6× win.
- **Bound-side query fix landed**: subject point lookup 12.06s→2.17s
  (5.6×), two-pattern join 31.08s→4.07s (7.6×), by eliminating a
  corpus-wide dictionary populate a bound query used to pay.

### 1.3 Weaknesses / risks

1. **No subject/object row-offset sidecar** — only predicates have
   `.p.offsets`. Bound-S/O lookups prune to a row *group* then decode it
   fully → 2.17s / 4.07s vs Jena TDB2's 1.16–3.88s on the same corpus.
   The single clearest "missing index for the slow access pattern."
   **Partially closed 2026-07-13** for the S half: `.s.offsets`
   (`RDF.CottasStore.SubjectOffsetsWriter.fst` /
   `RDF.Store.Columnar.SubjectOffsetIndex.fst`) records each subject's
   CONTIGUOUS global row range (rows are subject-primary sorted, so one
   `(start, end)` pair per subject is exact — no per-row-group breakdown
   needed, unlike `.p.offsets`). Wired into `cottas_ondisk_search_tok`'s
   candidate-rg intersection and `cottas_ondisk_count_exact_tok`'s
   bound-subject branch. Measured on the gene corpus (888,949 quads, 8
   row groups): q3 subject point lookup 3.15s→2.35s median (old
   committed binary/no sidecar vs new binary/with sidecar, 3 runs each,
   byte-identical answers) — the win comes from skipping a second,
   dict-page-unprunable (DELTA_LENGTH_BYTE_ARRAY-encoded) row group the
   old dict-page-probe fallback always included; the row group that
   DOES contain the subject is still fully decoded (no partial in-row-
   group decode primitive exists — see the O assessment below and the
   q6 indexed-decode refutation, `docs/claude-rules/current-state.md`).
   The O half is NOT implemented: `BaseWriter` sorts `(s, p, o, g)`, so
   object values are contiguous only within a fixed `(s, p)` pair, not
   globally — a dense per-object global-range table would be as
   impractical as a naive `.p.offsets`-style matrix at object
   cardinality (per this doc's own scaling note). `.po.presence`
   already gives object-side row-group pruning when `p` is co-bound;
   a genuine `.o.offsets` would need a different structure (e.g.
   sorted `(o) -> per-rg extents`) and is left as a follow-up.
2. **Companion writers are "Option B"** — byte-format proven in F\*, but
   the runtime writer is hand-OCaml verified only by hash-test; the
   actual rule-#11 residual for storage.
3. **No compression in the native writer** — the native writer *is*
   wired into the CLI and used (§1.2); the point is the *codec it emits*.
   It writes UNCOMPRESSED Parquet (DLBA-encoded, no from-scratch zstd
   encoder — `BaseWriter.fst:32-38`), so native output is 13.90 B/quad vs
   pycottas zstd+RLE_DICTIONARY 1.14–1.17 (~12× gap). The reader handles
   both codecs (the same commit added the UNCOMPRESSED branch), so native
   files are readable by us and DuckDB — but pycottas/DuckDB stays the
   import path when small files matter, until a zstd (or the in-flight
   RLE_DICTIONARY v2) encoder lands in F\*. "Used" and "emits compressed
   bytes" are independent: it's the first, not yet the second.
4. **`DictWriter`/`PresenceWriter` round-trip lemmas are base-case-only**
   (ADMITTED general case; not a rule-#10 breach — no `--lax`, just tests
   cover the inductive case).
5. **HDT rank/select naive (stage 5 unstarted); Roaring 4 phases out**;
   row-group-size footgun bounded-not-eliminated; a dead
   `RDF.CottasInMem.fst` scaffold.

---

## 2. Query planning / execution layer

### 2.1 Architecture (verified this pass)

Two parallel evaluator stacks: **Stack A** in-memory
(`SPARQL11.Algebra.fst`, `graph_store` over `RDF.Indexed`) and **Stack B**
backend-neutral (`SPARQL11.Store.fst` over the `store_caps` capability
seam in `RDF.Store.Capabilities.fst`), the latter being the production
path for COTTAS/HDT. Join ordering (`choose_best_tp(_backend)`) is
**cost-aware and adaptive** — re-estimates live selectivity per output row
and peels the cheapest pattern — and joins use a real hash join (build
side by post-hoc length) since 2026-07-06.

### 2.2 Strengths (evidence-backed)

- **The 8 codenamed OCaml shadow planners (Yod6/Tet3/Lamed3/Mem5/Pe5/
  Bet7/Tav5/Heth3) are all retired as OCaml semantic logic** — rule #11
  is genuinely satisfied for them; `factoidal-explain` now calls the real
  `choose_best_tp_backend` (divergent shadow deleted in `ae1b912`).
- **Cost-aware join ordering in the verified core** for both backends.
- **O(n²) fixes with measured before/after**: GROUP BY >600s→27s
  (quadratic→linear), point lookups 62s→17.7s→2.17s, joins 92s→31s→4.07s,
  correctness byte-diff-pinned by 116+521+381-assertion regressions.
- **The Plan.\* modules that exist are individually well-specified and
  KaRaMeL-clean** — ready to be the production planner the day they're
  wired in.

### 2.3 Weaknesses / risks

1. **New finding: three `SPARQL.Plan.*` modules are unwired dead code.**
   `Plan.Estimate`/`Pruning`/`AccessPath` have **zero production
   callers**; `RDF.CottasStore.fst` carries its *own inline duplicate* of
   the identical cardinality formula (`:2174` and `:2274`). The recovery
   plan's "one reusable F\* module per capability" half didn't happen even
   though the OCaml-shadow half did — a single-source-of-truth debt,
   distinct from (and smaller than) a rule-#11 violation.
2. **Two glue files remain `VIOLATION-SEM`** — `cottas_ondisk_runtime.sh`
   (#118) + `cottas_ondisk_z_lazy_open.sh` (#254), ~1,384 lines of
   unverified OCaml, kept alive only by **three non-production consumers**
   (a unit test, the smoketest binary, `factoidal_explain.ml`'s encode
   side) still calling id-based entry points. The live query path already
   bypasses them via the `_tok` entry points.
3. **`SPARQL11.Algebra`/`SPARQL11.Store` do not extract through KaRaMeL**
   — monomorphization stack-overflow; blocks **16 of 18** C/wasm-blocked
   modules including the join executor itself, `SPARQL.Plan.Explain/
   Streamable`, `SPARQL.HTTP.RunQuery`, `SPARQL11.Parser`. The query
   *execution engine* is the one piece of "verified SPARQL" that can't
   yet reach C/wasm.
4. **Cardinality estimation is one coarse uniform-density formula** — no
   histograms, no distinct-value counts (despite on-disk dictionaries
   that would give NDV for free), no join-selectivity term; the cross-BGP
   `GP_Join` gets no reordering at all (only the hash build side is
   chosen, post-hoc).
5. **The ~13× GROUP BY constant vs Jena (27.17s vs 2.05s) is unprofiled**
   beyond a one-line attribution.

---

## 3. Cross-cutting themes

- **Rule-#11 caveat-drop is close on both tracks but not done.** Storage:
  migrate companion writers Option B→A. Query: retire #118/#254 by
  migrating three residual consumers to `_tok`. Neither is on the live
  path; both block the qualifier drop (epic #200).
- **One change retires two debts, twice over.** *Roaring Phase E* becomes
  the shared rank/select core for both the missing S/O offset index
  (storage §1.3.1) and HDT stage 5 (storage §1.3.5). *KaRaMeL
  stratification of `SPARQL11.Algebra`* unblocks 16 modules across both
  layers. Prioritize the shared-leverage items.
- **The on-disk dictionaries are an unused statistics source.** They sit
  on disk already; using their sizes as a distinct-value proxy would give
  the query estimator real cardinalities at zero extra I/O — a storage
  asset the query layer doesn't yet consume.
- **Perf gap to Jena is now a constant, not a complexity class.** The
  O(n²)→linear fixes landed; what remains is a ~1–2 order-of-magnitude
  constant on bound-S/O lookups (missing row-level index) and ~13× on
  GROUP BY (unprofiled). Both are addressable and measured.

---

## 4. Goals for the next phase (unified, ranked by leverage)

1. **Subject/object row-offset sidecar** (`.s.offsets`/`.o.offsets`,
   mirroring `.p.offsets` — the OffsetsWriter already generalizes to any
   column). Closes the clearest perf gap (2.17s/4.07s → toward Jena's
   1.16–3.88s band) with an already-proven spec/writer/test pattern.
   **S half landed 2026-07-13** (§1.3 item 1 has the measurement + the
   contiguity finding that made the S format simpler than `.p.offsets`).
   O half assessed and NOT implemented — objects aren't globally
   contiguous under the `(s,p,o,g)` sort, so the same dense-range
   structure doesn't apply; see the same section for the follow-up
   shape.
   *Storage, highest single perf item.*
2. **Roaring Phase E + wire it as the shared rank/select core** for the
   new offset sidecar and HDT stage 5. One verified module retires two
   "naive/dense" debts. *Cross-layer.*
3. **KaRaMeL stratification of `SPARQL11.Algebra`/`SPARQL11.Store`** (split
   evaluator from datatypes per the `fstar-module-style` roadmap).
   Unblocks 16 modules incl. the join executor for C/wasm — the largest
   single KaRaMeL blocker. *Query, highest reach item.*
4. **Finish the rule-#11 caveat-drop on both tracks**: storage companion
   writers Option B→A (byte proofs already exist, swap the call site);
   query retire #118/#254 by migrating the three residual consumers to
   `_tok`. Removes ~1,384 lines of unverified OCaml and the qualifier
   blockers for these subsystems. *Both.*
5. **Real cardinality estimation**: wire the unwired `SPARQL.Plan.Estimate/
   Pruning/AccessPath` into `RDF.CottasStore.fst` (delete the inline
   duplicate at `:2174`/`:2274`), then replace uniform-density with a
   distinct-value-based estimate off the on-disk dictionaries + a
   join-selectivity term. *Query; also fixes the dead-code debt.*
6. **zstd (or equivalent) in the native writer** — closes the 12× size
   gap and removes the last pycottas import dependency. *Storage.*
7. **Prove the general-case `DictWriter`/`PresenceWriter` round-trip
   lemmas**; **profile the 13× GROUP BY residual** to a specific function
   before optimizing it; **HDT stage 5** after Roaring (#2) lands.

Sequencing note: #2 (Roaring E) precedes #1's index if the offset sidecar
is to share Roaring's popcount core, and precedes #7's HDT stage 5. #3
(stratification) is independent and can run in parallel. #4 is
low-engineering-risk and directly advances the qualifier drop.
