# #254 Bet7 lazy-populate retirement — design plan

**Date:** 2026-05-13 (scoped during the #200 closeout session).
**Tracker:** GitHub issue #254 / boundary-audit `cottas_ondisk_z_lazy_open.sh`.
**Status:** scoped, not yet executed.
**Estimated effort:** 1-2 days for the core lift, +1 day for the
re-verification (W3C SPARQL 1.1 + RDF 1.1 + the ukparliament bench).

## What the patch does today

`formal/fstar/experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh`
(457 lines) is a post-extraction OCaml rewrite that hooks into the
extracted `Cottas_ondisk_runtime` (itself produced by
`cottas_ondisk_runtime.sh`) and bolts on three concrete behaviours:

1. **Skip the subject + object dictionary populate at handle-open
   time.** `build_handle_and_tables` originally called
   `collect_distinct path 0` (subject column) and `collect_distinct
   path 2` (object column) eagerly. On the parliament 3.14M-quad
   corpus each call decodes every row-group data page for that column
   (~25 s + several hundred MB transient alloc). Total open-cost
   pre-Bet7 was ~50 s; post-Bet7 it's ~few seconds.

2. **Lazy populator hooks.** A new `Cottas_ondisk_lazy` OCaml module
   tracks "is this dict for this path populated yet?" via four
   per-path `Hashtbl.t` (subjects, predicates, objects, graphs).
   `ensure_subjects_loaded` / `ensure_objects_loaded` /
   `ensure_predicates_loaded` / `ensure_graphs_loaded` build the dict
   on first lookup that needs it and mark loaded.

3. **Wrap the `*_fast` lookups** (`encode_subject_fast`,
   `decode_subject_fast`, etc.) so they call `ensure_*_loaded` before
   the actual Hashtbl-based lookup.

The semantic surface is unchanged — the F\* spec of
`RDF.CottasStore` still describes a fully-populated handle. The
OCaml runtime just defers the populate work until the first lookup.

## Why it's a rule-#11 `VIOLATION-SEM`

The "when does this dict get built?" decision is a query-planning
choice (eager vs lazy) made in OCaml outside F\*'s knowledge. The F\*
spec assumes the dict is always there; OCaml decides empirically
that some queries never need the subject dict (graph-walking via
just predicate/object) and so skipping it is a real win.

This is one decision step removed from being pure perf glue: an
F\* spec that exposed a `LazyDict t` parameterised by a populate
thunk could host both the choice and the populate logic. Then the
OCaml side would shrink to just realising the `assume val
populate_dict_from_column` primitive.

## F\* migration sketch

Two new modules:

### `RDF.CottasStore.LazyDict.fst`

```fstar
module RDF.CottasStore.LazyDict

(* A populate-on-demand dictionary mapping token-IDs to either a
   subject / object term or a raw token string. The populate function
   is held as an `assume val`-realised closure; the F* side enforces
   "exactly one populate call per LazyDict, on first lookup". *)

assume new type lazy_dict (a : Type) : Type

assume val mk_lazy_dict
  : populate : (unit -> Tot (list (nat & a)))
  -> Tot (lazy_dict a)

(* Lookup: populates on first call, idempotent on subsequent. *)
assume val lookup
  (#a : Type) (d : lazy_dict a) (i : nat) : ML (option a)

(* The "is populated" flag — exposed for tests / introspection. *)
assume val is_populated (#a : Type) (d : lazy_dict a) : ML bool
```

`ML`-effected because populate touches state. The lookup function's
`ML` effect is the one F\* purity gap; everything else (the populate
thunk's return value, the table shape) is fully typed.

### `RDF.CottasStore.HandleOpen.fst`

Rewrites the F\* spec of `cottas_ondisk_handle` to hold four
`lazy_dict` fields instead of populated `list` / `Hashtbl`
equivalents. The `coh_subjects` / `coh_objects` / etc. fields become
`lazy_dict subject` / `lazy_dict rdf_term` / etc.

`build_handle_and_tables` (currently OCaml-only) lifts to F\* as
`open_cottas_ondisk_handle` returning a record of `lazy_dict`s, each
built from an `assume val parse_*_column : path -> col_idx -> list (nat & _)`
realisation.

### OCaml realisation in `89_fast_string_primitives.sh`-style patch

A new minimal patch `cottas_lazy_dict_runtime.sh` realises the
`lazy_dict` `assume val`s as a simple Hashtbl + populated flag,
preserving the current semantics byte-identically.

The big `cottas_ondisk_z_lazy_open.sh` patch deletes; the residual
glue is ~50 lines under the new patch (one Hashtbl per `lazy_dict`).

## Migration order — recommended commit boundaries

1. **Commit 1:** add `RDF.CottasStore.LazyDict.fst` with the
   `assume val`s + the populate-once invariant lemma. Pure additive.
2. **Commit 2:** rewrite `cottas_ondisk_handle` to use `lazy_dict`
   fields. F\*-side spec change; existing `*_fast` consumers update
   to call `LazyDict.lookup`. Verify W3C suites pass against the
   new shape.
3. **Commit 3:** add `cottas_lazy_dict_runtime.sh` realising the
   `assume val`s.
4. **Commit 4:** delete `cottas_ondisk_z_lazy_open.sh`. Re-run
   parliament bench; confirm open-time still ~few seconds (not
   ~50 s).

Steps 1-2 take ~1 day of careful F\* work + ~½ day for verification.
Steps 3-4 are mechanical, ~½ day combined.

## Risk register

- **`ML` effect on `LazyDict.lookup` propagates upward.** Every
  `_fast` consumer becomes `ML`-effected. This breaks `Tot` purity
  on the SPARQL evaluator side. Mitigation: introduce a pure version
  that takes the populated dict as input, plus a thin `ML` wrapper
  that does the populate-on-demand. The pure version is what the
  algebra layer calls; the ML wrapper lives at the
  `cottas_ondisk_search_indexed` boundary.
- **`Hashtbl` consumer semantics.** OCaml `Hashtbl.find` raises
  `Not_found`; the F\* `lookup` returns `option`. The patch's
  current `decode_subject_fast` etc. use the option-returning F\*
  shape already, so no caller-side change beyond the parameter type.
- **The patch also patches in semantic guards** at lines 187-190
  about Yod6 / Tet3 dead Hashtbls. Those are not Bet7 logic — they're
  audit comments from a different retirement. Untangling: confirm
  those Hashtbls aren't referenced by Vav3 or any live caller before
  ripping them out.
- **Parliament bench wallclock regression risk.** The retirement
  preserves the lazy-populate property by construction (the F\*
  `lazy_dict` only populates on first lookup), but the OCaml
  `Hashtbl` realisation has to match the current perf characteristics.
  Use the existing CI bench (ukparliament-bench.yml) to gate the
  retirement.

## Why not now

Multi-day, requires careful verification across the SPARQL 1.1 +
RDF 1.1 W3C suites AND the ukparliament-bench.yml benchmark to
confirm the lazy-populate semantics + perf are preserved. This
session's #200 closeout focused on the higher-leverage migrations
(Section F, OWL-RL indexing, #68 retirement) that don't need
benchmark gating. Scoped for the next dedicated #254 session.

## Cross-references

- `docs/designissues/2026-05-07-query-planning-fstar-recovery.md` —
  the parent recovery plan that classifies Bet7 as the cottas-handle
  lazy-populate state machine retirement.
- `docs/designissues/2026-05-11-owl-rl-find-objects-indexing.md` —
  sister migration with the same "lift an OCaml decision into F\*
  via `assume val`" pattern.
- `formal/fstar/RDF.CottasStore.fst` — current spec (eager populate).
- `formal/fstar/experimental_ocaml_glue/cottas_ondisk_runtime.sh` —
  the underlying runtime patch that Bet7 layers on top of. Its own
  retirement (#118) is multi-week and out of scope here.
