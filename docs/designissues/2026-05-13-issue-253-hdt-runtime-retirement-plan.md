# #253 ballyhoo_hdt_runtime retirement — design plan

**Date:** 2026-05-13 (scoped during the #200 closeout session).
**Tracker:** GitHub issue #253 / boundary-audit `ballyhoo_hdt_runtime.sh`.
**Status:** SUPERSEDED and closed 2026-07-06 by the HDT program's
stage 4 ([`2026-07-06-hdt-program-plan.md`](2026-07-06-hdt-program-plan.md)),
which went further than this plan scoped: instead of keeping
`parse_front_coded_section` as an `assume val` behind a LazyTermCache,
the byte format itself is parsed in F\* (HDT.Container / HDT.Dictionary
/ HDT.Triples) and `ballyhoo_hdt_runtime.sh` was deleted outright. The
LazyTermCache abstraction this plan proposed landed but ended up unused
by the HDT path — retained as a possible stage-5 memoization seam.
**Estimated effort:** 2-3 days for the core lift, +1 day for the
re-verification (HDT W3C interop tests + the BSBM micro-bench).

## What the patch does today

`formal/fstar/experimental_ocaml_glue/ballyhoo_hdt_runtime.sh`
(555 lines) is a post-extraction OCaml rewrite that hooks into the
F\*-extracted `Parser.BallyhooHDT` module and bolts on the runtime
term cache that backs the HDT (Header-Dictionary-Triples) reader.

Three concrete behaviours:

1. **HDT term-ID allocation.** Each HDT file has three Front-Coded
   string dictionaries (subjects, predicates, objects) keyed by
   sequential IDs starting at 1. The OCaml patch maintains four
   per-graph `Hashtbl.t` (subject→ID, predicate→ID, object→ID,
   reverse-lookup ID→string) and three monotonic `next_id` counters.

2. **Lazy population from mmap'd Front-Coded sections.** On first
   ID lookup, the patch decodes the Front-Coded entry into a string
   and caches it; subsequent lookups hit the Hashtbl. This is
   semantically identical to the cottas Bet7 pattern.

3. **`hdt_open_graph_store` realisation.** The F\* `assume val`
   that opens an HDT file is realised here as: open the file,
   parse the header, mmap the dictionary sections, build an empty
   cache, return the handle.

## Why it's a rule-#11 `VIOLATION-SEM`

The cache shape (one Hashtbl per direction, monotonic ID
allocation order) is a query-planning choice made in OCaml. The
F\* spec just says "we have a way to look up term-by-ID and ID-by-
term"; the OCaml decides empirically that a Hashtbl + monotonic
counter is the right shape.

Like #254 (Bet7), this is one decision step removed from being
pure perf glue. An F\* spec that exposed `TermCache t` with a
populate-on-demand contract could host both the cache shape and
the populate logic; OCaml would shrink to realising the
`assume val parse_front_coded_section` primitive plus four
`Hashtbl` instantiations.

## F\* migration sketch

Two new modules — mostly mirror the #254 plan, factor out the
LazyDict abstraction so both #253 and #254 can share it.

### `RDF.Store.LazyTermCache.fst` (shared with #254)

Same shape as the LazyDict from #254's plan but parameterised over
the populate function. Both Bet7 (cottas) and HDT use it.

```fstar
module RDF.Store.LazyTermCache

assume new type lazy_term_cache (a : Type) : Type

(* Populate function returns the full (id, value) list. The cache
   builds two Hashtbls internally (forward + reverse). *)
assume val mk_lazy_term_cache
  (#a : Type)
  (populate : unit -> Tot (list (nat & a)))
  : Tot (lazy_term_cache a)

assume val lookup_by_id   (#a : Type) (c : lazy_term_cache a) (i : nat) : ML (option a)
assume val lookup_by_value (#a : eqtype) (c : lazy_term_cache a) (v : a) : ML (option nat)
assume val is_populated   (#a : Type) (c : lazy_term_cache a) : ML bool
```

### `Parser.BallyhooHDT.fst` spec change

Replace the current `hdt_term_dict` record (three `list (string &
nat)` fields + three `nat` counters) with three `lazy_term_cache`
fields. The `hdt_open_graph_store` `assume val` returns a record
of those.

Front-coded section parsing stays as an `assume val
parse_front_coded_section : mmap_handle -> nat -> list (nat &
string)`, realised in OCaml via the existing front-coded decoder
inside the patch.

### OCaml realisation in a new `cottas_lazy_term_cache.sh`

~80 lines: one Hashtbl per direction + one populated-flag + the
populate-on-first-lookup wrapper. Replaces the 555-line
`ballyhoo_hdt_runtime.sh` plus the equivalent 200 lines from
`cottas_ondisk_z_lazy_open.sh` (#254 shares this).

Net glue reduction: ~755 → ~80 lines.

## Migration order — recommended commit boundaries

Sequencing matters: #254 should land first so the LazyTermCache
abstraction is proven on the cottas side before we ask the HDT
reader to consume it.

1. **#254 Bet7 Commits 1-4** (per the sister plan).
2. **#253 Commit 1:** add `Parser.BallyhooHDT.fst` spec change to
   use `RDF.Store.LazyTermCache`. F\*-pure rewrite.
3. **#253 Commit 2:** add the `assume val parse_front_coded_section`
   realisation to the OCaml glue.
4. **#253 Commit 3:** delete `ballyhoo_hdt_runtime.sh`. Verify HDT
   reader works against the W3C HDT interop fixtures (a small
   external corpus the project's CI already exercises).

## Risk register

- **Front-coded section parsing in F\*.** The Front-Coded format
  is a delta-encoded string list — common-prefix-with-previous +
  literal-suffix. Decoding is a `list (nat & string)` fold. F\*
  expressible, but not trivial; should follow the pattern of the
  existing Parquet footer decoder in `Parquet.Footer.fst`. Could
  hide behind `assume val parse_front_coded_section` if the F\*
  port proves slow.
- **HDT file format details.** HDT spec is W3C member submission
  level (not full Recommendation); the format has multiple
  versions in the wild. The patch's current parser handles the
  ones BSBM and SP2Bench ship with. The migration should preserve
  exactly the same byte-level parse — no spec interpretation
  changes.
- **Reverse-lookup Hashtbl.** The OCaml side maintains both
  forward (string→ID) and reverse (ID→string) tables. F\*-side
  `LazyTermCache` should hold both. OCaml realisation builds both
  from the single `list (nat & string)` returned by populate.
- **Cross-thread safety.** Process-global HDT handles can be
  accessed from multiple HTTP threads. Current Hashtbls are not
  Mutex-protected; OCaml's GC happens to make Hashtbl.find +
  Hashtbl.add safe under GIL-style assumptions, but this is a
  latent bug. The migration should add a `Mutex.t` field per cache
  in the OCaml realisation — that's a strict improvement.

## Why not now

Multi-day, depends on #254 landing first (shared LazyTermCache
abstraction), requires HDT W3C interop fixture verification. The
#253 + #254 pair together represent ~5-7 days of careful work
(specification + realisation + verification + perf re-bench).

This session's #200 closeout focused on the higher-leverage
migrations (Section F, OWL-RL indexing, #68 retirement) that
don't need backend perf-parity verification. #253 + #254 are
scoped here for a dedicated future session.

## Cross-references

- `docs/designissues/2026-05-13-issue-254-bet7-retirement-plan.md` —
  sister plan, must land first.
- `docs/designissues/2026-05-07-query-planning-fstar-recovery.md` —
  the parent recovery plan, classifies HDT cache shape as one of
  the remaining semantic-decision shims.
- `formal/fstar/Parser.BallyhooHDT.fst` — current spec.
- `formal/fstar/experimental_ocaml_glue/ballyhoo_hdt_runtime.sh` —
  the patch this plan retires.
