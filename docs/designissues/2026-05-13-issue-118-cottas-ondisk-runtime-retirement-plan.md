# #118 cottas_ondisk_runtime perf parity — design plan

**Date:** 2026-05-13 (scoped during the #200 closeout session).
**Tracker:** GitHub issue #118 / boundary-audit `cottas_ondisk_runtime.sh`.
**Status:** scoped, not yet executed.
**Estimated effort:** 2-4 weeks of careful F\* perf engineering +
**ukparliament-bench** gating at every step.

## Why this is the multi-week long-pole

`cottas_ondisk_runtime.sh` is the largest single rule-#11 violator
in the codebase (718 lines of OCaml glue) and the most consequential.
Per the patch header:

> **PERFORMANCE**: replaces the extracted F\* `cottas_ondisk_search` /
> `_estimate` / `_decode_*` with `Hashtbl`-backed equivalents. The
> F\* definitions in `RDF.CottasStore.fst` remain the verification
> spec.

The boundary-audit row classifies this as "the explicit reason
`RDF.CottasStore.fst` is decorative per the recovery-plan disaster
note." Translation: today, the F\* spec exists for verification
but the OCaml runtime uses an entirely separate code path. Closing
#118 is the work of making the F\* spec **and** the runtime the
same module.

## What the patch replaces

Three concrete F\* functions whose extracted OCaml is **discarded
and rewritten**:

1. **`cottas_ondisk_search`** — given a triple pattern + bound
   slots, return the row groups that could match. The F\* version
   walks every row group and consults the columnar presence bitmap;
   the OCaml override consults Hashtbl-cached per-graph subject
   sets + a fast-prune cascade (Yod6 → Tet3 → Lamed3 → presence
   bitmap), then iterates only the surviving row groups.
2. **`cottas_ondisk_estimate`** — cardinality estimate for a bound
   pattern. F\* version is a sum over row groups; OCaml replaces it
   with a histogram-from-bloom-filter shortcut + Hashtbl
   accelerator.
3. **`cottas_ondisk_decode_subject` / `decode_predicate` /
   `decode_object`** — go from token-ID to RDF term. F\* version
   does a linear `List.assoc` on the in-memory dict; OCaml uses a
   Hashtbl lookup.

All three are perf-driven: the F\* implementations are correct but
multiple orders of magnitude slower than the Hashtbl-backed OCaml
on parliament-scale corpora (3.14M quads).

## Migration shape: Option C (assume_val perf primitives)

The recovery-plan doc rules out Option A (port the Hashtbl shape
into F\* directly) and Option B (sed-style perf override that's
the current state) for #118 specifically. Option C is the agreed
direction:

Expose the Hashtbl-backed operations as `assume val`s in a new
`RDF.CottasStore.OnDiskRuntime.fst` module that the F\* spec
consumes. Each `assume val` has:

- a precondition stating the input contracts (graph IRI, column
  index, etc.);
- a postcondition stating the output contract relative to the
  spec — e.g. "this is exactly `cottas_ondisk_search_spec` modulo
  the row order, which the caller doesn't depend on";
- a thin OCaml realisation in `cottas_lazy_term_cache.sh` (the
  same realisation file used for #253 + #254 if we sequence the
  three together).

The F\* spec stays in `RDF.CottasStore.fst` as the
verification-time reference; the operational F\* code calls into
`RDF.CottasStore.OnDiskRuntime` for the hot path.

## F\* primitives to expose

About 9 `assume val`s, mirroring the 9 OCaml accelerators the
current patch installs:

```fstar
module RDF.CottasStore.OnDiskRuntime

(* Search: returns the row groups that could contain a match for
   the given bound pattern. Sound (no false negatives) modulo the
   ordering. Backed by a fast-prune cascade in OCaml. *)
assume val ondisk_search
  (h : cottas_ondisk_handle) (bp : bound_pattern)
  : ML (list row_group_idx)

(* Cardinality estimate: a non-negative integer that is bounded
   above by the true row count of (h, bp), and bounded below by 1
   when the search returns a non-empty list. *)
assume val ondisk_estimate
  (h : cottas_ondisk_handle) (bp : bound_pattern)
  : ML nat

(* Token decoders: identical to the F* spec but Hashtbl-fast. *)
assume val ondisk_decode_subject
  (h : cottas_ondisk_handle) (i : nat) : ML (option subject)
assume val ondisk_decode_predicate
  (h : cottas_ondisk_handle) (i : nat) : ML (option wf_iri)
assume val ondisk_decode_object
  (h : cottas_ondisk_handle) (i : nat) : ML (option rdf_term)
assume val ondisk_decode_graph
  (h : cottas_ondisk_handle) (i : nat) : ML (option wf_iri)

(* Encoders (inverse): used by query rewriter to lower constant
   terms into IDs once, then run the search loop over IDs. *)
assume val ondisk_encode_subject
  (h : cottas_ondisk_handle) (s : subject) : ML (option nat)
assume val ondisk_encode_predicate
  (h : cottas_ondisk_handle) (p : wf_iri) : ML (option nat)
assume val ondisk_encode_object
  (h : cottas_ondisk_handle) (o : rdf_term) : ML (option nat)
```

Each is `ML`-effected because the Hashtbl realisation touches
mutable state. The `option` returns reflect "term not in this
graph's dictionary" — the current patch returns the same option
shape.

## Soundness obligation — the hardest part

The current OCaml runtime makes a strong claim: it returns
**exactly** the row groups the F\* `cottas_ondisk_search_spec`
would return (up to ordering). Verifying that the Hashtbl-backed
fast-prune cascade is equivalent to the F\* spec at the level of
"same set of row groups" is the #118 verification job.

The current state lets this drift silently — the F\* spec is
"decorative" because nothing checks the runtime against it. The
retirement plan needs:

1. A **round-trip lemma** for each `assume val`: input contract +
   output contract relative to the spec. F\*-side `Lemma` form.
2. A **hash-witness CI test** like the one #200 PR3/PR4 added for
   the writer round-trips: pick representative fixtures, run both
   the F\* spec and the OCaml fast path, hash the canonicalised
   outputs, pin the hash. Any future drift trips CI.

Without those two, retiring #118 just moves the rule-#11 violation
from "sed rewrite" to "lying assume val." The boundary audit
should reject that.

## Migration order — recommended commit boundaries

This is the multi-week long pole. Recommended sequencing:

1. **Week 1 — #253 + #254 land.** Establishes the shared
   `LazyTermCache` abstraction + the `assume val` realisation
   pattern at a smaller scale (HDT, cottas-handle-open).
2. **Week 2 Phase 1 — `RDF.CottasStore.OnDiskRuntime.fst`** with
   the 9 `assume val`s + their precondition / postcondition
   shapes. F\*-pure rewrite, all decorative until the realisations
   land.
3. **Week 2 Phase 2 — round-trip lemmas + hash witnesses** for the
   three decoders (the easiest case — they're 1:1 with the F\*
   spec's `List.assoc` once you accept Hashtbl as
   "associatively-equivalent").
4. **Week 3 — search + estimate round-trip lemmas.** Harder
   because the fast-prune cascade has multiple soundness
   conditions to discharge. Likely needs `assume val
   fast_prune_witness` style auxiliary helpers.
5. **Week 4 — perf re-bench against ukparliament corpus.** Confirm
   the retirement preserves the existing 2-3 order-of-magnitude
   advantage over the F\*-spec implementation.

## Risk register

- **Soundness verification is hard.** The fast-prune cascade
  (Yod6 → Tet3 → Lamed3 → presence bitmap) has multiple soundness
  conditions. Each rule individually is sound; their composition
  has been hand-verified but never machine-checked. Migrating
  without the round-trip lemma risks shipping an unsound
  optimisation.
- **Perf regression risk.** Going through 9 `assume val` boundary
  calls instead of direct Hashtbl ops adds ~10ns per call. Over
  parliament's 3.14M quads that's a few seconds; should still be
  within the bench's existing budget.
- **Cross-thread safety.** Same as #253. The OnDiskRuntime
  realisation should add Mutexes from the start.
- **Decorativeness gap.** Until the round-trip lemmas land, the
  retirement is structurally complete but semantically still
  unverified. The audit should flag this as `MIXED` (not
  `PURE-FSTAR`) until the lemmas land.

## Why not now

Multi-week. Depends on #253 + #254 landing first to validate the
`LazyTermCache` + `assume val` realisation pattern. Verification
load (round-trip lemmas + hash witnesses + perf bench) requires
dedicated focus.

This session's #200 closeout focused on the higher-leverage
migrations (Section F, OWL-RL indexing, #68 retirement) that don't
need ukparliament-scale benchmark gating. #118 is the
retirement-plan terminal item; closing it removes the last
`VIOLATION-SEM` row from the boundary audit and unlocks the
CLAUDE.md rule-#11 caveat drop.

## Cross-references

- `docs/designissues/2026-05-13-issue-254-bet7-retirement-plan.md` —
  Bet7 lazy-open plan, sequencing predecessor.
- `docs/designissues/2026-05-13-issue-253-hdt-runtime-retirement-plan.md` —
  HDT cache plan, shares the LazyTermCache abstraction.
- `docs/designissues/2026-05-07-query-planning-fstar-recovery.md` —
  the parent recovery plan that classifies #118 as the
  "decorative-spec disaster" anchor.
- `docs/designissues/2026-05-07-io-verification-and-third-party.md` —
  the hash-witness round-trip-CI pattern.
- `formal/fstar/RDF.CottasStore.fst` — current decorative spec.
- `formal/fstar/experimental_ocaml_glue/cottas_ondisk_runtime.sh` —
  the 718-line patch this plan retires.
