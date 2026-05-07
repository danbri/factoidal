# 2026-05-07 — Query planning & storage abstraction: recovery into F\*

## Status
Plan. Drafted in response to "this was a disaster" feedback on the
project's drift of query-planning + access-method logic into
post-extraction OCaml patches.

## What went wrong

Between roughly 2026-04-25 and 2026-04-26, the COTTAS on-disk path
acquired a series of "fast paths" — predicate-presence row-group
prune, subject/object-presence prune, per-RG predicate offset index,
estimate-from-presence-bitmap, --explain mode, lazy hashtable
populate, row-cap circuit breaker, SIGALRM timeout. Each landed as
an `experimental_ocaml_glue/*.sh` patch that ran *after* F\*
extraction and inserted the optimization directly into
`formal/fstar/ocaml-output/RDF_CottasStore.ml` (or sibling files).

This had three consequences, all bad:

1. **The verified core became dead code.** The F\* implementation
   of `cottas_ondisk_search` / `_estimate` is faithful but slow.
   The OCaml-side shadows are fast but unverified. Production
   queries flow through the shadows. The F\* module is decorative.
2. **The "verified" claim collapsed.** A query against a COTTAS
   store can take a wrong-answer path through the shadow that the
   F\* spec never sanctioned. CLAUDE.md rule #11 acknowledges this
   with a "qualified verified" footnote that has to appear on
   every README, demo page, and talk slide.
3. **Multi-target extraction is impossible.** KaRaMeL extracts
   F\* modules to C; `js_of_ocaml` extracts the OCaml files. The
   shadow patches are post-extraction OCaml manipulations — they
   cannot extract to C, Rust, or WASM. The SPARQL evaluator a C
   consumer would link against is the slow F\*-only path.

The shadow patches were also internally tagged with subagent
codenames (Yod6, Tet3, Lamed3, Mem5, Pe5, Bet7, Tav5, Heth3) that
communicate nothing to a reader. The codenames stuck in trace tags,
commit messages, and even in `docs/code-name-glossary.md`.

This plan retires the entire pattern.

## Principle

> **Every RDF/SPARQL semantic decision lives in F\*. OCaml is a
> realisation language for `assume val` declarations only. Tools
> that wrap the verified library (CLI, HTTP server, runners) are
> consumers — they may live in any host language and are not
> claimed to be verified.**

Concrete consequences:

- A "query plan" is an F\* value of an F\* type. The planner is a
  pure F\* function. The evaluator consumes that value.
- A "storage abstraction" is an F\* signature. Each concrete store
  (in-memory, COTTAS, HDT, future Parquet) implements it.
- An "optimization" is an F\* function from a storage view + a
  query fragment to a faster equivalent computation, with a
  correctness lemma `denote(optimised) = denote(naive)`.
- The only OCaml inside `formal/fstar/ocaml-output/` is what F\*
  extracts. Hand-written `factoidal_*.ml`, `*_runner.ml` etc. move
  to `bin/<consumer>/`. They become call-sites, not logic.

## Storage abstraction map

The recovery makes "which operations require which storage
capabilities" explicit. Capabilities compose: a COTTAS store has
all of them; an in-memory store has the bottom row only.

| Capability | Operation | Required by |
|---|---|---|
| **Term lookup** | `lookup : tp -> bindings list` | every store |
| **Counting** | `count : tp -> nat` | every store |
| **Cheap estimate** | `estimate : tp -> nat` (may be approximate) | optional; falls back to `count` |
| **RG enumeration** | `row_groups : list rg_id` | columnar stores |
| **Presence bitmap** | `presence : (col, rg) -> bitmap` | columnar stores w/ presence |
| **Offset index** | `offset_of : (rg, predicate_id) -> option offset` | columnar stores w/ offset index |
| **Page cache** | `page_for : (rg, col, page_id) -> bytes` | columnar stores w/ paging |
| **Companion files** | `read_companion : path -> bytes` | columnar stores w/ on-disk artifacts |

Capabilities are F\* type classes / record-of-functions / refinement
predicates depending on which extracts cleanest to C. Initial
proposal: a record of optional functions, with each capability
detected via `Some f`. This avoids polymorphism KaRaMeL doesn't like.

## Proposed module layout

Descriptive names, no codenames. Storage axis is explicit in the
hierarchy. New modules listed below; existing modules retained
verbatim where they already make sense.

```
RDF.Store/
  RDF.Store.Capabilities.fst         -- the contract (record of capability-fns)
  RDF.Store.InMemory.fst             -- (renames RDF.CottasInMem)
  RDF.Store.Columnar/
    RDF.Store.Columnar.RowGroup.fst       -- RG-level operations (existing pieces collected)
    RDF.Store.Columnar.PresenceBitmap.fst -- (existing) + prune predicates
    RDF.Store.Columnar.CompoundPresence.fst -- (existing)
    RDF.Store.Columnar.OffsetIndex.fst    -- NEW: per-RG predicate row-offset index
    RDF.Store.Columnar.PageCache.fst      -- (existing)
    RDF.Store.Columnar.CompanionFiles.fst -- file format spec for on-disk artifacts
  RDF.Store.COTTAS.fst              -- (renames RDF.CottasStore) wires Columnar.*
  RDF.Store.HDT.fst                 -- (existing-ish; explicit Capabilities instance)

SPARQL.Plan/
  SPARQL.Plan.BoundStatus.fst       -- (lifted from SPARQL.Explain) BS_Var/Hit/Miss/Other
  SPARQL.Plan.Pruning.fst           -- "can this RG possibly match this tp?" predicate
  SPARQL.Plan.Estimate.fst          -- cardinality estimation (cheap path + naive fallback)
  SPARQL.Plan.AccessPath.fst        -- "given a tp + a Capabilities, what's the cheapest reader?"
  SPARQL.Plan.Explain.fst           -- plan introspection, JSON renderer
  SPARQL.Plan.Loader.fst            -- companion-file-present? if not, fall back to in-RAM build

SPARQL.Eval/
  SPARQL.Eval.Iterator.fst          -- streaming iteration primitives (take, drop, fold)
  SPARQL.Eval.Limits.fst            -- row-cap circuit breaker (a LIMIT for evaluation policy)
  SPARQL.Eval.TimeBudget.fst        -- cooperative cancellation; assume val now : ML clock
```

Notes:
- `SPARQL.Plan.*` are pure F\*. They take a `Capabilities` value
  and a `triple_pattern` / sub-query and produce a plan or estimate.
  Multi-target extractable.
- `SPARQL.Eval.*` are also pure F\* except `TimeBudget`, which
  requires a single `assume val now_ms : unit -> ML int`. That
  realisation is the ONLY allowed OCaml/C-side thing.
- Storage hierarchy mirrors the access-pattern hierarchy: an
  in-memory store implements only `Capabilities.basic`; a
  COTTAS store implements `Capabilities.basic + columnar +
  presence + offset_index + page_cache`.

## Mapping the disaster onto real names

| Old codename | What it is | Right F\* home | Effort |
|---|---|---|---|
| **Yod6** | Predicate-presence RG-skip predicate | `SPARQL.Plan.Pruning.fst`, consuming `RDF.Store.Columnar.PresenceBitmap` | S |
| **Tet3** | Subject/object-presence RG-skip predicate | same module + `CompoundPresence` | S |
| **Lamed3** | Per-RG predicate row-offset index lookup | new `RDF.Store.Columnar.OffsetIndex.fst` reader + `SPARQL.Plan.AccessPath` chooses it | M |
| **Mem5** | Cardinality estimate from presence bitmap | `SPARQL.Plan.Estimate.fst`, calls into `Columnar.PresenceBitmap` | S |
| **Pe5** | --explain mode plan dump | `SPARQL.Plan.Explain.fst` (extends what's already in `SPARQL.Explain.fst`) | M |
| **Bet7** | Lazy hashtable populate when companion file missing | `SPARQL.Plan.Loader.fst` decision; `RDF.Store.InMemory.fst` builder | S |
| **Tav5** | Result-row cap | `SPARQL.Eval.Limits.fst` (a `take n stream` combinator) | XS |
| **Heth3** | Per-query timeout | `SPARQL.Eval.TimeBudget.fst` + `assume val now_ms` realisation | M |

Effort: XS=<30min, S=<2h, M=half-day, L=multi-day.

Total effort estimate to retire all 8: ~2-3 weeks of focused work
plus reviews. Most modules build on `RDF.Store.Columnar.*` and
`RDF.Store.Capabilities.fst`, which themselves are ~1 week of
careful design + proof.

## Sequencing

Strictly ordered; later steps depend on earlier ones.

| Phase | Deliverable | Output | Blockers |
|---|---|---|---|
| **0. Boundary audit** | `docs/designissues/fstar-ocaml-boundary-audit.md`: every OCaml fn classified (extracted-pure / `assume val` realisation / consumer / **violation-must-migrate**); every shadow patch enumerated. | One doc PR. | None. Unblocks rule #11 freeze. |
| **1. Capabilities contract** | `RDF.Store.Capabilities.fst`: the record-of-functions interface. `RDF.Store.InMemory.fst` retitled and made the reference impl (lowest capability set). | One PR. | Audit complete. |
| **2. Columnar layer** | `RDF.Store.Columnar.RowGroup.fst` + reorg of existing `Columnar.PresenceBitmap`, `CompoundPresence`, `PageCache`. No semantic change yet — pure namespace + capability binding. | One PR. | Phase 1. |
| **3. Easy violators** | Migrate Tav5 + Bet7 in parallel. Each retires its glue patch. | 2 PRs. | Phase 2 (Bet7); Phase 1 (Tav5). |
| **4. Pruning + estimate** | `SPARQL.Plan.Pruning.fst` + `SPARQL.Plan.Estimate.fst`. Retires Yod6, Tet3, Mem5 simultaneously (they share the presence-bitmap reader). | 1 PR. | Phase 2. |
| **5. Time budget** | `SPARQL.Eval.TimeBudget.fst` design PR + `assume val now_ms` realisation glue + `SPARQL.Eval.Limits.fst` for `--max-rows` interaction. Retires Heth3. | 2 PRs (design + migration). | Phase 3 done. |
| **6. Offset index** | `RDF.Store.Columnar.OffsetIndex.fst` (new file format spec + verified reader) + `SPARQL.Plan.AccessPath.fst` chooses it. Retires Lamed3. **Performance-critical**: must preserve the 6s → 200ms win. Benchmark required. | 1-2 PRs. | Phase 4. |
| **7. Explain** | `SPARQL.Plan.Explain.fst`: plan dump with all access-path decisions surfaced. Retires Pe5. | 1 PR. | Phases 4 + 6. |
| **8. Consumer relocation** | Move `factoidal_*.ml`, `*_runner.ml` from `formal/fstar/ocaml-output/` to `bin/<consumer>/`. Update build-ocaml.sh. Tighten CI gate so `formal/fstar/ocaml-output/` accepts only F\*-extracted output + a fixed list of `assume val` realisation files. | 1 large PR. | Phase 7. |
| **9. Drop the qualifier** | Delete the "qualified verified" footnote from CLAUDE.md rule #11, READMEs, demo pages. CI gate now enforces the property. | 1 doc PR. | Phase 8 + audit shows zero violators. |

After Phase 9, the project can credibly say "verified RDF/SPARQL"
without footnotes. The C-build pilot (separate plan,
`2026-05-07-c-build-and-roaring-plan.md`) becomes meaningful — the
verified library is genuinely host-language-agnostic.

## Done criteria

- `experimental_ocaml_glue/*.sh` contains zero patches that touch
  `RDF_CottasStore.ml`'s `cottas_ondisk_*` functions, or any
  function in `factoidal_explain.ml` or `factoidal_http.ml` that
  involves SPARQL evaluation, planning, or storage decisions.
- `find experimental_ocaml_glue/ -type f` shows only:
  - `_*_assume_val_*.sh` files (each realising one `assume val`)
  - the file-system / clock realisations
  - `_runner_io_glue.sh` (or whatever's left for raw I/O)
- `find formal/fstar/ocaml-output/ -name '*.ml'` shows only files
  with a "GENERATED BY F\*" header. No hand-written `.ml` files.
- `bin/factoidal-cli/`, `bin/w3c-runner/`, `bin/rdfc10-runner/`,
  `bin/owl-runner/` exist; their `.ml` files contain only
  argv-parsing, file I/O, and calls to F\*-extracted functions.
- The CI workflow `check-fstar-purity.yml` enforces all of the
  above.
- For every operation in the storage-abstraction-map table, the
  set of stores that implement it is recorded in
  `RDF.Store.Capabilities.fst` and a unit test exercises it on
  each store.
- Codenames Yod6, Tet3, Lamed3, Mem5, Pe5, Bet7, Tav5, Heth3 do
  not appear in any code path. They survive only in `git log`
  archaeology and in `docs/code-name-glossary.md` as historical
  notes.

## What this plan does NOT do

- It does not replace existing in-flight Track-1 quick-win PRs
  (`bs_json`, `tp_explain`, `term_nq`, `escape_literal_lexical`,
  `kind_label` + `is_test_type_iri`). Those are pure renderers /
  classifiers. They're forward-compatible: they migrate logic
  from OCaml into F\* in modules that this plan keeps.
- It does not replace the C-build pilot plan
  (`2026-05-07-c-build-and-roaring-plan.md`). The two plans
  reinforce each other: this plan removes the OCaml-only logic
  that blocks C extraction; the C-build plan exercises the
  resulting cleanly-extractable F\* modules.
- It does not propose a rewrite of existing F\* modules that are
  already well-named (`RDF.CottasStore.PresenceBitmap.fst`,
  `RDF.CottasStore.OnDiskIndex.fst`, etc.). The "Columnar"
  reorg in Phase 2 is namespace-level — it moves modules under
  `RDF.Store.Columnar.*` without changing their content.

## Open questions

1. **Capabilities encoding for KaRaMeL.** F\* type classes don't
   extract well to C. Records-of-functions do, but require
   monomorphisation. Decision: record-of-functions, with each
   `Capabilities` instance constructed at top level (no
   polymorphism over `Capabilities`).
2. **Cancellation semantics.** Cooperative-checkpoint vs hard
   interrupt. The current Heth3 uses SIGALRM (process-global).
   The proposed `TimeBudget` polls. Polling needs the evaluator
   to call `check_budget` between every N tuples. Where to put
   the polling call sites? Decision: the iterator combinators in
   `SPARQL.Eval.Iterator.fst` poll at every yield boundary.
3. **Offset-index format.** Reuse the existing `.p.offsets` mmap
   format if it's already specified somewhere; otherwise spec it
   in F\* and migrate the writer at the same time. Per the
   corrected taxonomy from this morning's discussion, the
   serialiser must be in F\*; OCaml only does `write`.
4. **Companion-file writer audit.** Vav3-style writers may
   contain byte-encoding logic in OCaml today. Phase 0's audit
   must enumerate which writers are pure-I/O (acceptable) vs
   contain layout logic (must migrate). For migrating ones, add
   `serialize : data -> Tot (list u8)` in F\* + reduce OCaml to
   `write_bytes`.

## How this fits with the corrected taxonomy

Earlier today we corrected the "acceptable glue" taxonomy from
three categories to one:

> **Inside the verified library boundary, the only acceptable
> OCaml is an `assume val` realisation. Companion-file writers
> with byte-layout logic are not a separate category — they're
> `assume val`s with structured signatures, where the structuring
> belongs in F\*. "Trivial dispatch shims" aren't part of the
> verified library at all — they're the consumer/binding layer
> and belong outside `formal/fstar/ocaml-output/`.**

This plan operationalises that taxonomy. Phase 0's audit applies
the new rule. Phases 1-7 migrate logic. Phase 8 separates the
consumer layer. Phase 9 ratifies the new state.
