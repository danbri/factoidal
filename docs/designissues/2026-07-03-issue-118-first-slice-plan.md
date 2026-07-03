# #118 first slice — retire the 10 remaining sed substitutions in cottas_ondisk_runtime.sh

**Date:** 2026-07-03.
**Tracker:** GitHub issue #118 / boundary-audit `cottas_ondisk_runtime.sh`.
**Refines:** the first phase of
[`2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md`](2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md).
**Status:** planned, not yet executed. Four commit-sized work packages.

## Where the tree actually is (the 2026-05-13 plan is partly stale)

The parent plan proposed Option C: 9 **new** `assume val` perf
primitives in a new `RDF.CottasStore.OnDiskRuntime.fst`. Since it was
written, Phases 2.5b–2.7-mini landed and changed the ground:

1. The `cottas_ondisk_search` / `cottas_ondisk_estimate` /
   `cottas_ondisk_search_limited` substitutions are **already
   retired** — the F\*-extracted bodies at
   `formal/fstar/RDF.CottasStore.fst:1123`, `:1346`, `:1375` are the
   runtime, decoding through the global page cache and pruning via
   `plan_candidate_rgs` + the compound (p,o) bitmap. The patch's own
   Phase 2.5e comment (`cottas_ondisk_runtime.sh:737-752`) confirms
   this.
2. Eight token/id oracles already exist as `assume val`s in
   `RDF.CottasStore.fst` and are already realised:
   - `ondisk_id_to_{subj,pred,obj,graph}_token_global`
     (`RDF.CottasStore.fst:400-407`)
   - `ondisk_lookup_{subj,pred,obj,graph}_id_global`
     (`RDF.CottasStore.fst:451-458`)
   both realised by
   `experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh`
   via `lookup_with_ensure` / `id_to_token_with_ensure`, which trigger
   Bet7's `ensure_*_loaded` lazy populate and then do one
   `Hashtbl.find_opt`.
3. `RDF.CottasStore.OnDiskRuntime.fst` exists (Phase 2.5c) with
   `ondisk_{encode,decode}_*_indexed` / `_via_registry` assume vals —
   but **zero F\* consumers** (grep confirms only the module itself
   mentions them). It is scaffolding this slice supersedes.

What is still substituted by `cottas_ondisk_runtime.sh` (787 lines
today) is exactly **10 sed replacements of real F\* `Tot` bodies**:
4 `cottas_ondisk_encode_*`, 4 `cottas_ondisk_decode_*`,
`cottas_ondisk_predicate_present` (the `shim_replacements` dict,
`cottas_ondisk_runtime.sh:623-735`), and `cottas_ondisk_named_graphs`
(`:754-784`). These are load-bearing because Bet7's lazy open leaves
the F\* handle's `coh_*` lists **empty**, so the extracted F\* bodies
(`revmap_lookup` / `list_nth` over those lists) would return
None/sentinels on every call.

**First-slice thesis:** no new assume vals, no new glue, no
`OnDiskRuntime` expansion. Rewrite the 10 F\* `Tot` bodies to route
through the 8 already-realised oracles (which honour lazy populate),
then delete the 10 substitutions and the OCaml they dispatched to.
Unlike Option C's "assume val + round-trip lemma" shape, this makes
the F\* body **be** the runtime for these functions — the
decorativeness gap closes structurally; the soundness surface
concentrates on the 8 oracle realisations, whose contract comments
already live at `RDF.CottasStore.fst:425-450`.

## Shared gating block (run for every package)

```bash
eval $(opam env --switch=fstar)              # Iron Rule 12
cd formal/fstar
make verify                                  # no --lax (Iron Rule 10)
./build-ocaml.sh                             # extract (applies glue patches) + compile + unit tests
cd ../..
tests/local/cottas_corpus_regressions.sh     # on-disk COTTAS behaviour (named + default graph)
tests/local/backend_parity_regressions.sh    # plain vs COTTAS drift witness
cd formal/fstar/ocaml-output
./w3c_runner                                 # all SPARQL 1.1 suites
```

Report suite results with labelled numerators/denominators (anti-
pattern #25). Background the full build (anti-pattern #20); cap ad-hoc
runs at `timeout 600` (anti-pattern #17). Note `./build-ocaml.sh
compile` alone does **not** apply patches (anti-pattern #11) — always
go through the full script or `extract` after touching a `.fst`.

Patch-pipeline post-conditions for every package:

- `./ocaml-patches.sh` applied twice is a no-op (idempotency markers
  intact).
- The `[cottas_ondisk_runtime] perf-shim applied N/M` stderr line is
  updated to the new expected denominator and treated as a hard check
  (mismatch = investigate, not shrug).

## WP1 — encode path: route `cottas_ondisk_encode_*` + `predicate_present` through the token→id oracles

One commit. Deletes 5 of the 10 substitutions.

### (a) F\* functions to change

| Function | Current location |
|---|---|
| `cottas_ondisk_encode_subject` | `formal/fstar/RDF.CottasStore.fst:151-154` |
| `cottas_ondisk_encode_predicate` | `formal/fstar/RDF.CottasStore.fst:156-159` |
| `cottas_ondisk_encode_object` | `formal/fstar/RDF.CottasStore.fst:161-164` |
| `cottas_ondisk_encode_graph_name` | `formal/fstar/RDF.CottasStore.fst:166-169` |
| `cottas_ondisk_predicate_present` | `formal/fstar/RDF.CottasStore.fst:232-237` |

Prerequisite reshuffle in the same commit: the oracle declarations at
`RDF.CottasStore.fst:380-458` (both assume-val blocks plus
`id_to_raw_token_via_global`) currently sit **below** the encode
section. F\* is declaration-order-sensitive — hoist that block up to
just after `list_nth` (`RDF.CottasStore.fst:98-102`). Comment blocks
move with it unchanged.

### (b) Sketch

```fstar
// Raw column-token forms. COTTAS columns store N-Triples-shaped
// tokens; these must byte-match what the corpus writer emitted.
// Literal parity with the writer was established by the #261 fix,
// which already routes literals through the F-star N-Quads
// serializer. Add near the module opens (RDF.CottasStore.fst:3-9):
//   module NQS = RDF.NQuads.Serialize

let subject_to_raw_token (s : subject) : Tot string =
  NQS.nq_subject_to_string s          // "<iri>" or "_:b"

let iri_to_raw_token (i : iri) : Tot string =
  "<" ^ i ^ ">"

let object_to_raw_token (o : rdf_term) : Tot string =
  NQS.nq_term_to_string o             // IRI / bnode / escaped literal

// Replaces the body at RDF.CottasStore.fst:151-154. Signature
// unchanged (callers: cottas_ondisk_build_bound_qp_opt at :1459,
// the _ml fallbacks at :270-296).
let cottas_ondisk_encode_subject
  (ds : cottas_ondisk_store) (s : subject)
  : Tot (option cottas_term_ref) =
  ondisk_lookup_subj_id_global ds.cods_handle.coh_path
    (subject_to_raw_token s)

// encode_predicate / encode_object / encode_graph_name: identical
// shape via ondisk_lookup_pred_id_global (iri_to_raw_token p),
// ondisk_lookup_obj_id_global (object_to_raw_token o),
// ondisk_lookup_graph_id_global (iri_to_raw_token g).

// Replaces the body at RDF.CottasStore.fst:232-237.
let cottas_ondisk_predicate_present
  (ds : cottas_ondisk_store) (pred : wf_iri)
  : Tot bool =
  Some? (ondisk_lookup_pred_id_global ds.cods_handle.coh_path
           (iri_to_raw_token pred))
```

These bodies compute exactly the keys today's OCaml shims compute
(`encode_subject_fast` builds `"<" ^ i ^ ">"` / `"_:" ^ b`;
`encode_object_fast` uses `nq_term_to_string` for literals — see
`cottas_ondisk_runtime.sh:529-586`) and dispatch to the same Hashtbls
through `lookup_with_ensure`. Behaviour change: none intended.

### (c) Deletable patch lines

`formal/fstar/experimental_ocaml_glue/cottas_ondisk_runtime.sh`:

- `shim_replacements` entries for `encode_subject` (`:624-633`),
  `encode_predicate` (`:634-642`), `encode_object` (`:643-651`),
  `encode_graph_name` (`:652-660`), `predicate_present` (`:713-724`).
- The `encode_*_fast` / `predicate_present_fast` OCaml definitions
  (`:529-586`) become call-path-dead but are **kept until WP4**:
  `cottas_ondisk_runtime_indexed.sh` still names them in its
  (unconsumed) `_indexed` realisations, and
  `cottas_ondisk_z_lazy_open.sh:305-396` text-anchors its
  `ensure_*_loaded` wraps on their bodies. Deleting them here would
  silently no-op those anchors mid-chain; WP4 removes both ends
  together.

### (d) Gating

Shared block. Extra: after `./build-ocaml.sh`, grep the patched
`ocaml-output/RDF_CottasStore.ml` — every `cottas_ondisk_encode_*`
body must call `ondisk_lookup_*_id_global`, none may mention
`Cottas_ondisk_runtime.encode_`. Expected shim counter: `applied 4/4`
(decode shims remain until WP2 — update the denominator).

### (e) Risks

- **Handle-not-registered path.** `lookup_with_ensure` returns None
  when the path is absent from `Cottas_ondisk_runtime.handles`; the
  old shim's `tables_for` would rebuild instead. Every
  `cottas_ondisk_store` is produced by `cottas_ondisk_open` →
  `load_handle`, which registers, so the case is unreachable from the
  public API; parity tests gate it anyway.
- **Escaping parity for literals.** Already pinned by #261 (both
  sides use `nq_term_to_string`); the parity suite is the witness.
- **Declaration-order churn.** The hoist is textual; `make verify`
  catches any missed forward reference.

## WP2 — decode path: route `cottas_ondisk_decode_*` through the id→token oracles + the F\* N-Triples term parsers

One commit. Deletes 4 more substitutions. Also deletes a latent
unescape bug: the OCaml `unescape_literal`
(`cottas_ondisk_runtime.sh:133-146`) maps `\n` to the letter `n`
(naive backslash-drop); `Parser.NTriples.parse_string_literal`
implements the real ECHAR/UCHAR rules.

### (a) F\* functions to change

| Function | Current location |
|---|---|
| `cottas_ondisk_decode_subject` | `formal/fstar/RDF.CottasStore.fst:182-187` |
| `cottas_ondisk_decode_predicate` | `formal/fstar/RDF.CottasStore.fst:189-211` |
| `cottas_ondisk_decode_object` | `formal/fstar/RDF.CottasStore.fst:213-218` |
| `cottas_ondisk_decode_graph_name` | `formal/fstar/RDF.CottasStore.fst:220-225` |

Parsers to reuse (all `Tot`, all already extracted):
`Parser.NTriples.parse_subject` (`Parser.NTriples.fst:540`),
`parse_iri` (`:195`), `parse_object` (`:564`); result type
`parse_result` from `Parser.Combinators.fst:17-22`.

### (b) Sketch

```fstar
// Add near the opens:  module NT = Parser.NTriples
// (parse_result constructors come via Parser.Combinators, which
// Parser.NTriples re-exports; byte length via Parser.FastString.)

// Parse one whole raw column token as one term. Dictionary tokens
// carry no trailing bytes, so require full consumption; anything
// else falls to the loud out-of-range sentinel, matching the
// existing corrupt-file behaviour.
let parse_subject_token (tok : string) : Tot (option subject) =
  match NT.parse_subject tok 0 with
  | ParseOk s pos ->
    if pos = Parser.FastString.fs_byte_length tok then Some s else None
  | ParseFail _ _ -> None

// parse_predicate_token via NT.parse_iri  : Tot (option wf_iri)
// parse_object_token    via NT.parse_object : Tot (option rdf_term)
// parse_graph_token     via NT.parse_iri  : Tot (option iri)
//   (wf_iri subtypes iri; graph tokens are always "<iri>")

// Replaces the body at RDF.CottasStore.fst:182-187.
let cottas_ondisk_decode_subject
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : Tot subject =
  match ondisk_id_to_subj_token_global ds.cods_handle.coh_path id with
  | None -> S_BNode "cottas_decode_oor"
  | Some tok ->
    (match parse_subject_token tok with
     | Some s -> s
     | None -> S_BNode "cottas_decode_oor")

// decode_predicate: same shape; keep the loud sentinel
// "urn:factoidal:cottas-decode-predicate-unknown-id" + assert_norm
// from :209-211 (its comment shrinks: the shim it apologises for is
// gone). decode_object falls to T_BNode "cottas_decode_oor";
// decode_graph_name falls to "".
```

### (c) Deletable patch lines

`cottas_ondisk_runtime.sh` `shim_replacements` entries:
`decode_subject` (`:661-673`), `decode_object` (`:674-685`),
`decode_predicate` including its correctness-bug comment
(`:686-703`), `decode_graph_name` (`:704-712`). The `decode_*_fast`
definitions (`:501-527`) stay until WP4 (same anchor reasoning as
WP1).

Also in this commit: extend `tests/local/data/cottas_sample.nq` with
escaped-literal rows (`\n`, `\"`, `\\`, a `@lang` tag, a `^^` typed
literal) if not already present, so the corpus + parity scripts pin
the round-trip `encode(decode(id)) = id` at the byte level. This is
the slice's stand-in for the parent plan's hash-witness gate.

### (d) Gating

Shared block, with the new fixture rows in place **before** flipping
the F\* bodies (run once against the old binary to record baseline —
the naive-unescape divergence, if visible, must show up as a fix, not
a silent change). Expected shim counter: `applied 0/0` or dict
removed to a stub — either way the WARN path must not fire.

### (e) Risks

- **Perf: decode now parses per row occurrence** instead of one
  Hashtbl hit against pre-parsed terms. Token parse is the FastString
  hot path (same code that parses whole corpora at MB/s), but a
  3.14M-row full materialisation re-parses ~9M tokens. The sample
  corpus won't see it; before merging, spot-check the parliament
  corpus with a bounded query per
  [`perf-benchmarking`](../../skills/perf-benchmarking/SKILL.md)
  (full ukparliament-bench gating stays scheduled for the parent
  plan's week-4 step). If it regresses, the fallback is memoising via
  the existing `LazyDict` `_ml` variants (`RDF.CottasStore.fst:297-328`)
  — no new glue either way.
- **Unescape behaviour change** (documented above): strictly a
  correctness fix, but any downstream test that accidentally pinned
  the buggy `n`-for-`\n` output will flip; the fixture makes this
  visible in this commit rather than later.
- **Full-consumption check** uses byte length, not codepoint length —
  use `fs_byte_length`, never `String.length` (anti-pattern #10
  territory).

## WP3 — `cottas_ondisk_named_graphs`: F\* enumeration over the graph oracle

One commit. Deletes the last substitution (the `#261 fix part B`
block).

### (a) F\* functions to change

| Function | Current location |
|---|---|
| `cottas_ondisk_named_graphs` | `formal/fstar/RDF.CottasStore.fst:249-251` |
| `named_graphs_aux` (delete, now unused) | `formal/fstar/RDF.CottasStore.fst:242-247` |

### (b) Sketch

```fstar
// Enumerate named graphs by walking dense ids through the graph
// id->token oracle. Ids are assigned 0..n-1 by the open-time /
// lazy dictionary builder (the "DEFAULT" sentinel never enters the
// dictionary — collect_distinct_graph and ensure_graphs_loaded both
// skip it), so the first None terminates the walk. Fuel: the total
// row count bounds the number of distinct graphs.
let rec named_graphs_via_global_loop
  (path : string) (idx : nat) (fuel : nat)
  (acc_rev : list (iri & cottas_graph_ref))
  : Tot (list (iri & cottas_graph_ref)) (decreases fuel) =
  if fuel = 0 then acc_rev
  else
    match ondisk_id_to_graph_token_global path idx with
    | None -> acc_rev                       // dense ids: first gap = end
    | Some tok ->
      let acc_rev' =
        match parse_graph_token tok with    // WP2 helper
        | Some g -> (g, idx) :: acc_rev
        | None -> acc_rev in                // malformed token: skip loudly-logged upstream
      named_graphs_via_global_loop path (idx + 1) (fuel - 1) acc_rev'

// Replaces the body at RDF.CottasStore.fst:249-251.
let cottas_ondisk_named_graphs (ds : cottas_ondisk_store)
  : Tot (list (iri & cottas_graph_ref)) =
  let path = ds.cods_handle.coh_path in
  let fuel : nat =
    match probe_parquet_num_rows path with
    | Some n -> n
    | None -> 0 in
  list_rev (named_graphs_via_global_loop path 0 fuel [])
```

The oracle's realisation calls `ensure_graphs_loaded` on every hit,
so the Bet7 problem the OCaml replacement existed for (empty
`coh_graphs` until first populate) is handled on the F\* side's first
lookup. On a corpus with zero named graphs this is a single oracle
call.

### (c) Deletable patch lines

`cottas_ondisk_runtime.sh:754-784` — the `old_named_graphs` /
`new_named_graphs` pair, the `content.replace`, and the applied-check
warn block.

### (d) Gating

Shared block. `tests/local/cottas_corpus_regressions.sh` exercises
named-graph and default-graph queries against the sample corpus and
is the primary witness; also confirm `GRAPH ?g {}` enumeration output
against the plain backend in `backend_parity_regressions.sh`.

### (e) Risks

- **Ordering change.** The OCaml replacement iterated a Hashtbl
  (arbitrary order); the F\* walk yields ascending id order. Benign
  and more deterministic, but any test comparing unsorted `GRAPH`
  enumerations line-for-line will need its expectation refreshed.
- **Density contract.** The walk assumes graph ids are contiguous
  from 0. Both populate paths guarantee this via a monotonic
  `next_id` counter; state the contract in the oracle's comment block
  so a future realisation can't silently break it.
- **Fuel = num_rows** is a loose bound but costs nothing: the walk
  exits at the first None, after (distinct graphs + 1) oracle calls.

## WP4 — dead-code sweep: delete the fast-path layer and the superseded OnDiskRuntime scaffold

One commit, all deletion. After WP1-3 nothing on any call path
reaches `Cottas_ondisk_runtime.{encode,decode}_*_fast` or
`predicate_present_fast`; the only remaining references are the
unconsumed `_indexed` realisations and the lazy-open wrap anchors.
Delete producers and consumers together:

1. `cottas_ondisk_runtime.sh`: the `decode_*_fast` / `encode_*_fast`
   / `predicate_present_fast` definitions (`:501-587`) and whatever
   remains of the `shim_replacements` scaffolding (`:623-735`) and
   the retired-substitution commentary (`:737-752`). What stays is
   rule-#11-acceptable open-time I/O: token collectors, dictionary
   build, `load_handle`, `tables_for`, `build_summary_for_handle`,
   the `cottas_ondisk_open` realisation, and the token-parse helpers
   (still used by `ensure_*_loaded`).
2. `cottas_ondisk_z_lazy_open.sh`: Step 4 wrap blocks (`:300-452`) —
   the `search_fast`/`estimate_fast` wraps are already dead (retired
   in #110), the encode/decode wraps die with (1). Steps 1-3
   (lazy module, populators, `build_handle_and_tables` rewrite) stay.
3. `RDF.CottasStore.OnDiskRuntime.fst`: delete the
   `ondisk_{encode,decode}_*_indexed` and `_via_registry` assume vals
   (zero F\* consumers) — reduce the module to its plan-of-record
   comment or delete it outright, and drop
   `RDF_CottasStore_OnDiskRuntime.ml` from the `build-ocaml.sh` lists
   (`build-ocaml.sh:306`, `:431`, `:797`) if deleted.
4. `cottas_ondisk_runtime_indexed.sh`: delete the whole patch (its
   only job was realising the assume vals removed in (3)).
5. Bookkeeping in the same commit: update the `assume val` table in
   [`docs/claude-rules/current-state.md`](../claude-rules/current-state.md),
   the boundary-audit row for `cottas_ondisk_runtime.sh`
   (VIOLATION-SEM → IO-GLUE), and any
   `minimal_regrettable_glue_code_each_with_an_open_issue/` stubs for
   the deleted assume vals (Iron Rule #3: the table shrinks, the
   linked issues get a closing comment).

No F\* semantic sketch needed — the package is deletions plus list
maintenance. Grep post-conditions:

```bash
grep -rn "encode_subject_fast\|decode_object_fast\|predicate_present_fast" \
  formal/fstar/experimental_ocaml_glue/ formal/fstar/ocaml-output/*.ml   # expect: no hits
grep -rn "_indexed\|_via_registry" formal/fstar/RDF.CottasStore.OnDiskRuntime.fst  # expect: gone or file absent
```

### (d) Gating

Shared block, run from a **fresh extraction** (delete the patched
`.ml`, re-run `./build-ocaml.sh`) so a broken anchor in the trimmed
patch chain fails loudly instead of riding a stale file. Run
`./ocaml-patches.sh` twice for idempotency. Commit the rebuilt
`bin/<platform>/` binaries (Iron Rule #9).

### (e) Risks

- **Anchor coupling.** The glue patches text-anchor on each other's
  output; every deletion here must be checked against the remaining
  chain (`cottas_ondisk_z_lazy_open.sh` Step 1/3 anchors on
  `build_handle_and_tables` and `load_handle` text — do not touch
  those regions). The fresh-extraction gate is the enforcement.
- **Scope creep temptation.** The `ft_id_to_{subject,predicate,
  object,graph}` typed tables become write-only after this package
  (populated by `ensure_*_loaded`, read by nothing). Trimming the
  populators to skip typed parsing would save populate time and
  memory but requires anchor surgery in `cottas_ondisk_z_lazy_open.sh`
  — explicitly **out of this slice**; file a follow-up issue.
- If the counter/anchor checks turn hairy, split into 4a (items 1-2)
  and 4b (items 3-5); both halves independently leave the tree green.

## What this slice does and does not close

After WP1-4, `cottas_ondisk_runtime.sh` drops from 787 lines to
roughly 400, contains **zero substitutions of F\* function bodies**,
and is classifiable as open-time I/O glue (dictionary build +
`cottas_ondisk_open` realisation) plus memory layout. Still open for
the parent plan:

- round-trip lemma statements + hash-witness CI for the 8
  `*_global` oracle realisations (the soundness surface this slice
  concentrated everything onto);
- migrating `cottas_ondisk_open`'s dictionary build toward the
  F\*-specified companion-file layout in
  `RDF.CottasStore.OnDiskIndex.fst` (`dict_encode_token` /
  `dict_decode_token` at `:216-309` already specify the byte-exact
  read path — a candidate second slice is realising the four
  `mmap_companion_*` primitives against the `.dict` companions and
  retiring `collect_distinct` for columns whose companions exist);
- the ukparliament-scale perf re-bench (parent plan week 4).

The CLAUDE.md rule-#11 qualifier stays until the boundary audit
signs off the remaining glue as IO-GLUE and the oracle witnesses
land.

## Cross-references

- [`2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md`](2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md) — parent plan (Option C shape superseded as described above).
- [`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md) — recovery roadmap; #118 is its terminal item.
- [`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md) — hash-witness pattern for the follow-up.
- `formal/fstar/RDF.CottasStore.fst` — all first-slice F\* edits land here.
- `formal/fstar/experimental_ocaml_glue/cottas_ondisk_runtime.sh` — the patch being shrunk.
- `formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh` — the oracle realisations everything reroutes through (unchanged by this slice).
- [`skills/ocaml-boundary/SKILL.md`](../../skills/ocaml-boundary/SKILL.md), [`skills/fstar-module-style/SKILL.md`](../../skills/fstar-module-style/SKILL.md) — rules the sketches follow (no block comments in sketches; oracle contracts stated in `//` comments).
