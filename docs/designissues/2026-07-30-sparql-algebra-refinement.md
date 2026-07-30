# SPARQL algebra: a declarative semantics and a refinement proof

Status: LANDED 2026-07-30, branch
`claude/sparql-refinement-20260730`. Verify-only proof layer; no
shipping module changed. No admit, no `--lax`, no
`--admit_smt_queries`, no `assume`; z3 4.13.3.

Issue: [#313](https://github.com/danbri/factoidal/issues/313) — the
external-review epic. The finding this answers, quoted verbatim from
the 2026-07-29 review:

> "SPARQL11.Algebra.fst is a substantial executable evaluator … The
> module does not present a second, declarative W3C algebra semantics
> and prove the evaluator equivalent to it."

The generated assurance inventory quantified it as **501 shipping
functions, 0 declarative relations**. This is the first declarative
relation set, plus the refinement theorems against it, for a named
fragment.

Companion to, and built with the method of, the RDF simple-entailment
vertical ([`2026-07-29-simple-entailment-refinement.md`](2026-07-29-simple-entailment-refinement.md)).

---

## 🔴 Two findings, and both are live bugs

The refinement attempt found the evaluator does **not** refine the
specification in two places. Per the pattern doc's §7.7, neither
specification was weakened to fit; both non-refinements are machine-
checked theorems, and **both were then confirmed end-to-end against
the shipping binary**.

### 🔴 SR-1 — `SELECT DISTINCT` returns duplicate rows

Filed as [#336](https://github.com/danbri/factoidal/issues/336).

`distinct_solutions` decides "same solution" with `sm_equal`, which
compares two solution mappings **position by position as ordered
association lists**:

```fstar
let rec sm_equal (m1 m2 : solution_mapping) : bool =
  match m1, m2 with
  | [], [] -> true
  | (v1, t1) :: r1, (v2, t2) :: r2 -> v1 = v2 && rdf_term_eq t1 t2 && sm_equal r1 r2
  | _, _ -> false
```

SPARQL 1.1 §18.3 makes a solution mapping a **partial function**
`μ : V → T`. Two association lists binding the same variables to the
same terms in a different order denote the same mapping; `sm_equal`
says they differ, so DISTINCT keeps both and §18.5's
`Card[Distinct(Ω)][μ] = 1` fails.

The theorem, with a concrete witness and no hypothesis:

```fstar
val theorem_distinct_not_card_conformant : unit ->
  Lemma (exists (omega : list S.smap).
           ~(S.distinct_card_spec omega (distinct_solutions omega)))
```

Reachable from ordinary SPARQL: `tp_match` threads bindings
subject → predicate → object and `sm_bind` **prepends**, so the two
arms of `{ ?x :p ?y } UNION { ?y :q ?x }` build the same mapping in
opposite list order.

✅ Confirmed against `bin/linux-x86_64/factoidal` (2026-07-30):

```
data:  @prefix : <http://ex/> .  :s :p :o .  :o :q :s .

SELECT DISTINCT * WHERE { { ?x <http://ex/p> ?y } UNION { ?y <http://ex/q> ?x } }

  | ?y            | ?x            |
  | <http://ex/o> | <http://ex/s> |
  | <http://ex/o> | <http://ex/s> |
  2 result(s)
```

Two identical rows out of `SELECT DISTINCT`. That is a SPARQL 1.1
conformance failure, not a modelling artefact.

**Fix**: decide DISTINCT with an order-insensitive comparison — the
Spec module ships one, `smap_eqb`, together with
`lemma_smap_eqb_sound` / `lemma_smap_eqb_complete` proving it decides
`smap_eq` exactly. It is a behaviour change to a shipping function and
therefore out of this issue's scope; it needs its own commit with the
sparql11/sparql12 suites re-run.

### 🔴 SR-2 — the hash-join key is finer than the compatibility test it narrows

Filed as [#337](https://github.com/danbri/factoidal/issues/337).

The 2026-07-06 join-algorithm perf fix narrows join candidates with a
hash index keyed by `sm_join_key`, which serializes each bound term
with `nq_term_to_string` — **byte identity**. The narrowed candidates
are then filtered by `sm_compatible`, which accepts on `rdf_term_eq` —
**coarser than byte identity**: `RDF.Term.lang_tag_eq` case-folds
language tags, and two `rdf:XMLLiteral`-typed literals compare up to
exclusive canonical XML.

A hash-join optimisation is only semantics-preserving if its candidate
set is a **superset** of the truly-matching pairs. Here it is not: two
mappings binding the shared join variable to `"x"@en` and `"x"@EN` are
compatible by the engine's own test and land in different buckets.

```fstar
val theorem_join_key_finer_than_compatibility (v tag1 tag2 : string) :
  Lemma (requires String.lowercase tag1 == String.lowercase tag2 /\ tag1 =!= tag2)
        (ensures  (let t1 = T_Literal (sr2_lit tag1) in
                   let t2 = T_Literal (sr2_lit tag2) in
                   rdf_term_eq t1 t2 == true /\
                   sm_compatible [(v,t1)] [(v,t2)] == true /\
                   sm_join_key [v] [(v,t1)] =!= sm_join_key [v] [(v,t2)]))
```

The tag pair is a hypothesis rather than a string constant for the
reason §7.7 of the simple-entailment doc records: `String.lowercase` is
a primitive the normaliser will not evaluate. The **byte-level half is
proved, not assumed** — `lemma_sr2_nq_differs` derives the serializer
disequality from `FStar.String.concat_injective`.

✅ Confirmed against `bin/linux-x86_64/factoidal` (2026-07-30). Data:

```
@prefix : <http://ex/> .
:a :p "x"@en .   :b :q "x"@EN .     # the case-differing pair
:c :p "y"@en .   :d :q "y"@en .     # the control pair
```

| Query | `@en`/`@EN` data | all-`@en` control |
|---|---|---|
| `{ ?s1 :p ?v OPTIONAL { ?s2 :q ?v } }` | `?s2` **UNBOUND** for `"x"@en` | binds `:b` |
| `{ ?s1 :p ?v { SELECT ?s2 ?v WHERE { ?s2 :q ?v } } }` | **1 row** | 2 rows |
| `{ ?s1 :p ?v . ?s2 :q ?v2 FILTER(sameTerm(?v,?v2)) }` | **MATCHES** | matches |

The third line is what makes this decisive. **`sameTerm` says the two
terms ARE the same term, and BGP matching joins them — the hash join
does not.** Whichever reading of RDF term equality is correct, the
engine contradicts itself; this is not a spec-interpretation dispute.

The OPTIONAL row is the worse failure mode: `left_join` falls through
to `[mu1]` when its candidate list yields nothing, so a dropped inner
match does not remove a row, it returns a **wrong** row — as if the
OPTIONAL had not matched.

Note that a plain two-pattern BGP does **not** hit this: `GP_BGP` is
evaluated by `eval_bgp_store`, which threads `tp_match` and never calls
`join`. `join` is reached through `GP_Join` (sub-SELECT, VALUES,
property-path and GRAPH compositions) and `left_join` through every
OPTIONAL.

**Fix**, two candidates:

1. Make the key **coarser than or equal to** the acceptance test —
   key on a canonical form that folds exactly what `rdf_term_eq` folds
   (lowercase the language tag; canonicalise XMLLiteral lexical forms).
   Preserves the perf win; the index stays a narrowing filter.
2. Make the acceptance test **term identity** and lift the case-folding
   into value-equality where SPARQL puts it. This is finding SE-1's fix
   seen from the SPARQL side and would settle both at once.

Either is a behaviour change to a shipping function; out of scope here.

### Relationship to SE-1

SR-2 and finding SE-1 of the simple-entailment vertical are the same
root cause — `RDF.Term.rdf_term_eq` is a D-flavoured, value-ish
equality being used where the specification says term identity —
reached from two different ends of the tree. SE-1 made simple
entailment accept **too much**; SR-2 makes the SPARQL join accept
**too little**, because a second component (`nq_term_to_string`) was
written against the strict reading. A codebase carrying two
inconsistent notions of term equality will keep producing findings of
this shape until one is retired.

---

## 1. What landed

| Module | Role | Status |
|---|---|---|
| `formal/fstar/SPARQL11.Algebra.Spec.fst` | The declarative §18.3/18.4/18.5 semantics, mentioning no function and no type of the evaluator | ✅ verified, 834 lines |
| `formal/fstar/SPARQL11.Algebra.Refinement.fst` | Refinement of the shipping evaluator against it; the two findings | ✅ verified, ~910 lines |
| `formal/fstar/build-ocaml.sh` | one `ALL_MODULES` entry (whole-tree verification vehicle) | ✅ |

Zero change to any shipping module. Verify-only: no extraction, so no
`.ml` list entries.

### Independence is mechanically checkable

`SPARQL11.Algebra.Spec.fst`'s entire `open` list is

```
FStar.List.Tot   RDF.Term
```

It does not open `SPARQL11.Algebra` or `RDF.Graph.Executable`;
`solution_mapping` is **re-declared** as `smap` rather than imported,
for exactly that reason. A reader can diff the module against the W3C
text without the evaluator in view. (§7.1 of the pattern doc, applied
harder than in the simple-entailment vertical, where the Spec module
could share the RDF term model but here the algebra types are inside
the evaluator module itself.)

---

## 2. The fragment: SPARQL-CORE-8

Declared in the Spec module banner and repeated here so no later
document has to reconstruct it.

**IN**: solution mappings and domains (§18.3); compatibility and merge
(§18.3); Join, Union, Minus, Filter, Diff, LeftJoin, Extend, Project,
Distinct (§18.5); BGP matching stated abstractly over a
pattern-instantiation function (§18.3.1).

**OUT — explicitly, and not gestured at**:

* aggregates (§18.5.1 Aggregation / Group / AggregateJoin) — a
  per-group semantics, not a solution-multiset one;
* property paths — their own fixpoint semantics;
* subqueries (ToMultiSet) and SERVICE;
* ORDER BY, Slice (OFFSET/LIMIT), Reduced, ToList — **sequence**
  operators; a refinement statement about them must first fix an
  ordering discipline the evaluator does not currently promise;
* the dataset / GRAPH machinery — everything is relative to a single
  active graph, `eval(D(G), ·)` written `eval(G, ·)`;
* expression evaluation (§17). Filter, LeftJoin and Extend are stated
  **parametrically** in the expression evaluator, exactly as §18.5
  states them ("expr(μ) … has an effective boolean value of true").

Additional in-module boundaries:

* `join`'s **hash path** is not proved sound (only its
  no-shared-variable path, which is definitionally
  `join_nested_loop`). Hash-path soundness needs "`bucket_lookup`'s
  result is a sublist of the indexed sequence", a lemma about
  `RDF.Indexed`'s balanced tree that does not exist yet. Hash-path
  **completeness is false** — SR-2.
* The general `left_join` arm is not proved. See §5.
* Whether `eval_expr_ebv` respects `smap_eq` (`fexpr_congr`) is stated
  as an open obligation, not assumed away and not proved: it is a
  ~480-line mutual recursion over the whole expression language.

---

## 3. Both semantic layers, deliberately

W3C §18.5 is a **multiset** semantics with an explicit `Card[·]`.
Pérez, Arenas and Gutiérrez (*Semantics and Complexity of SPARQL*, ACM
TODS 34(3), Article 16, 2009) — the canonical formal treatment — use a
**set** semantics; that is what makes their complexity results and
their well-designed-pattern normal form clean, but it does not describe
what a conforming engine must return for a query without DISTINCT.

The Spec module formalises both, because they carry different proof
obligations against a list-backed evaluator:

* the **set layer** (`in_join_spec`, `in_union_spec`, `in_diff_spec`,
  `in_leftjoin_spec`, `in_minus_spec`, `in_filter_spec`,
  `in_extend_spec`, `in_project_spec`, `in_distinct_spec`) says *which*
  mappings may appear. This is the layer Pérez et al. share, so their
  established results transfer;
* the **bag layer** (`mult`, `union_card_spec`, `filter_card_spec`,
  `distinct_card_spec`, `project_card_spec`, `minus_card_spec`) says
  *how many times*. This is the normative layer, and it is where a
  list-backed evaluator's duplicate-handling defects live.

**SR-1 is invisible to the set layer and fatal at the bag layer.** A
vertical that had formalised only the Pérez-style set semantics — the
obvious choice, since it is the published one — would have proved
DISTINCT correct and shipped. That is the single most transferable
lesson here (§6.1).

Where the two disagree the W3C multiset reading wins; the divergences
from the papers are listed in the Spec module banner.

---

## 4. The theorems, by name

Every theorem names a **shipping** function of `SPARQL11.Algebra`.

### 4.1 Bridging (§18.3 primitives)

```fstar
val theorem_sm_compatible_sound (mu1 mu2 : S.smap)
  : Lemma (requires sm_compatible mu1 mu2 == true /\ smap_exact mu1)
          (ensures  S.compatible_spec mu1 mu2)

val theorem_sm_compatible_complete (mu1 mu2 : S.smap)
  : Lemma (requires S.smap_wf mu1 == true /\ S.compatible_spec mu1 mu2)
          (ensures  sm_compatible mu1 mu2 == true)

val theorem_sm_merge_is_merge (mu1 mu2 : S.smap)
  : Lemma (S.is_merge mu1 mu2 (sm_merge mu1 mu2))

val theorem_domains_disjoint_sound   / _complete
```

Both hypotheses are load-bearing and both were already known to be, from
the 2026-07-29 refutations (#323):

* `smap_exact` (every bound term is one where `rdf_term_eq` **is** term
  identity) is what quarantines SR-2's root cause. Without it
  `theorem_sm_compatible_sound` is false.
* `smap_wf` (no repeated variable) is required because
  `sm_compatible` is not even reflexive without it —
  `lemma_sm_compatible_not_refl_with_dup_keys`.

`theorem_sm_merge_is_merge` is worth noting: `sm_merge` is **not**
`mu1 @ mu2` and is **not** left-identity as a list
(`lemma_sm_merge_empty_l_not_structural_identity`), but it *is* §18.3's
merge **as a mapping**, because `is_merge` is stated pointwise and is
therefore blind to list layout.

### 4.2 Operators

```fstar
// Union — unconditional, both layers
val theorem_union_card     (o1 o2) : Lemma (S.union_card_spec o1 o2 (union o1 o2))
val theorem_union_sound / _complete

// Filter — unconditional in the expression evaluator
val theorem_filter_sound (base) (e) (omega) (mu)
  : Lemma (requires memP mu (filter_solutions base e omega))
          (ensures  memP mu omega /\ eval_expr_ebv base e mu == true)
val theorem_filter_complete   // the converse
val theorem_filter_card (f) (omega)   // bag layer, needs fexpr_congr f

// Join, at the nested-loop evaluator that IS the algebra's Join
val theorem_join_nested_loop_sound (o1 o2 mu)
  : Lemma (requires memP mu (join_nested_loop o1 o2) /\ seq_exact o1)
          (ensures  S.in_join_spec o1 o2 mu)
val theorem_join_nested_loop_complete (o1 o2 mu1 mu2)
  : Lemma (requires memP mu1 o1 /\ memP mu2 o2 /\
                    S.compatible_spec mu1 mu2 /\ S.smap_wf mu1 == true)
          (ensures  exists mu. memP mu (join_nested_loop o1 o2) /\ S.is_merge mu1 mu2 mu)
val lemma_join_is_nested_loop_no_shared_vars / _empty   // where `join` IS Join

// Minus
val theorem_minus_sound / _complete

// Project — unconditional
val theorem_project_is_proj (pv) (mu) : Lemma (S.is_proj pv mu (project pv mu))
val theorem_project_solutions_length / _spec / _sound

// Distinct
val theorem_distinct_sound                       // never invents a solution
val theorem_distinct_not_card_conformant         // 🔴 SR-1
val theorem_sm_equal_is_not_smap_eq              // 🔴 SR-1, at the primitive

// Extend / BIND
val theorem_fx_bind_rows_length / _rowwise
val theorem_sm_bind_is_extend

// LeftJoin — degenerate arms only (see section 5)
val theorem_left_join_empty_right / _empty_left

// BGP matching, one triple pattern (sections 18.3.1 / 18.5)
val theorem_tp_match_instantiates (tp) (t) (mu mu')
  : Lemma (requires tp_match tp t mu == Some mu' /\ smap_exact mu /\
                    <pattern literals exact, triple terms excluded>)
          (ensures  binding_extends mu' mu /\ smap_exact mu' /\
                    instantiate_tp tp mu' == Some t)

// 🔴 SR-2
val theorem_join_key_finer_than_compatibility
```

### 4.3 Spec-side sanity theorems

The Spec module proves its own transcription coherent rather than
asserting it: `lemma_compatible_empty_l/_r` and
`lemma_compatible_of_disjoint` discharge the note that follows §18.3's
compatibility definition; `lemma_merge_comm_compatible` proves W3C's
merge agrees with Pérez et al.'s symmetric `μ1 ∪ μ2` on compatible
arguments; `lemma_join_comm_spec` is their Proposition 1;
`lemma_merge_unique` shows "the" merge is well-defined as a mapping
even though many association lists represent it;
`lemma_term_id_eqb_sound`/`_complete` prove the module's decision
procedure for term identity exact; `lemma_smap_eqb_sound`/`_complete`
do the same for mapping equality; `lemma_mult_pos_iff_occurs` ties the
bag layer to the set layer.

---

## 5. What is not proved, exactly

* **BGP matching against the store — partially.** `bgp_sol_spec` is
  defined in the Spec module abstractly over a pattern-instantiation
  function, the empty-BGP base case is proved, and
  `theorem_tp_match_instantiates` proves the per-pattern core: if
  `tp_match` accepts, the resulting binding **extends** the incoming
  one and **instantiates the pattern to exactly the matched triple**
  (§18.3.1's "μ(P) is in G", for one pattern). What is NOT proved is
  the lift to `eval_bgp_store`, which needs (a) `store_search`'s
  candidate list to be a superset of the matching triples — a lemma
  about `RDF.Indexed`, needed for the same reason `join`'s hash path
  needs one — and (b) the `choose_best_tp` reordering to be
  semantics-preserving. Both are tractable; neither is small.
  Triple-term patterns are quarantined from the per-pattern theorem by
  explicit `tt_free` hypotheses (routine recursion, doubled case
  analysis, nothing in the fragment needs it).
* **The general `left_join` arm.** Only the two degenerate arms are
  proved. The obstacle is recorded in the module and in §6.3 below —
  it is proof engineering, not semantics.
* **`join`'s hash path, soundness.** Needs the `bucket_lookup` sublist
  lemma. Completeness is **false** (SR-2), so the honest statement is
  that `join` refines §18.5's Join only on the no-shared-variable path
  and on the empty arms, which is exactly what the two `lemma_join_is_
  nested_loop_*` theorems say.
* **`fexpr_congr` for `eval_expr_ebv`.** Stated, not proved. Every
  bag-level Filter/LeftJoin statement carries it as a hypothesis.
* **Aggregates, paths, subqueries, SERVICE, ORDER BY / Slice, the
  dataset.** Out of the declared fragment.

---

## 6. What the next vertical should copy

Additions to the simple-entailment pattern doc's §7, from this run.

### 6.1 Formalise the layer the STANDARD normatively uses, even when the literature uses a cleaner one

The published formal semantics of SPARQL (Pérez et al. 2009) is a set
semantics. Transcribing it would have been defensible, faster, and
citable — and would have **proved DISTINCT correct**, because SR-1 is
invisible at the set layer. The bag layer took an afternoon (a
multiplicity function, a decision procedure for mapping equality, and
its soundness/completeness pair) and is where the bug was.

Generalisation: when the standard and the literature disagree about
what a semantic object *is*, formalise the standard's object, and use
the literature for structure and for knowing which theorems are
already established.

### 6.2 An optimisation's KEY must be coarser than its ACCEPTANCE TEST — check that pair explicitly

SR-2 is a general shape: a hash/index optimisation narrows candidates
with a key `k`, then filters with a test `≈`. Correctness needs
`x ≈ y ⟹ k(x) = k(y)`. Whenever a perf commit introduces a keyed
narrowing over a non-structural equality, that implication is the
proof obligation, and it is one line to state.

This codebase has at least two other keyed narrowings over
`rdf_term_eq`-flavoured tests (`RDF.Indexed`'s `sp_key`/`po_key_opt`/
`so_key_opt` bucket keys). They should be checked for the same defect.

### 6.3 `unfold let` + `trefl` beats `unfold let` alone when the lambda sits under a MATCH

§7.5 of the pattern doc says to try `unfold let` first for
lambda-arguments. Correct, but incomplete: `unfold let jnl_step` alone
did **not** make `join_nested_loop o1 o2 == concatMap (jnl_step o2) o1`
provable — SMT gives two syntactically-distinct closures unrelated
symbols even after unfolding. `assert (…) by (FStar.Tactics.trefl ())`
closes it in one line.

The remaining hard case, which defeated LeftJoin here, is a lambda
under **both** a match on a symbolic scrutinee **and** a boolean guard
that only a hypothesis discharges. `trefl` cannot use hypotheses; SMT
cannot identify closures. The shape that should work is a
`trefl`-provable equation with the `if` **left in the statement and
both branches spelled out**, followed by an SMT step to pick the
branch. Budget for writing the other branch out.

### 6.4 Take the finding to the shipping binary

Both findings were run against `bin/<platform>/factoidal` the same
session, with a control query alongside the failing one. That turned
"the proof does not go through" into "here is a wrong answer, and here
is the identical query that gets the right one" — which is what makes
SR-1 and SR-2 bug reports rather than proof-engineering notes. It cost
about ten minutes and it is the difference between a finding that gets
fixed and one that gets argued about.

For SR-2 the control was decisive in a second way: running
`FILTER(sameTerm(?v,?v2))` established that the engine's *own* term
equality identifies the two literals, converting a spec-reading
question into an internal inconsistency.

### 6.5 Cost

Measured this session, on warm `.checked` dependencies:

| Module | Lines | Single-module verify |
|---|---|---|
| `SPARQL11.Algebra.Spec` | 834 | 1.9 s |
| `SPARQL11.Algebra.Refinement` | ~1050 | 19.5 s |

One session, two modules, 29 theorems, nine operators touched, two
live bugs. As in
the simple-entailment vertical the dominant cost was **deciding what
the specification should say** — specifically the multiset-vs-set
question in §3 and the term-equality question in the Spec banner — not
discharging proof obligations.

---

## 7. Follow-ups

* 🔴 **Fix SR-1**: decide DISTINCT with `smap_eqb` (or an equivalent
  order-insensitive comparison). Needs the sparql11 (631 pass, 0 fail)
  and sparql12 (254 pass, 0 fail) suites re-run. Filed: #336.
* 🔴 **Fix SR-2**: make `sm_join_key` fold exactly what `rdf_term_eq`
  folds, or retire `rdf_term_eq`'s folding in favour of term identity
  (shared fix with SE-1, #324). Same suite gate. Filed: #337.
* Audit `RDF.Indexed`'s other bucket keys for the §6.2 defect.
* Prove the general `left_join` arm (§6.3 gives the shape).
* Lift `theorem_tp_match_instantiates` to `eval_bgp_store` against
  `bgp_sol_spec`; needs the `store_search` superset lemma and the
  `choose_best_tp` reordering argument. Add the triple-term cases.
* Prove `fexpr_congr (eval_expr_ebv base e)`, which unlocks every
  bag-level Filter/LeftJoin statement.
* Prove `bucket_lookup`'s result is a sublist of the indexed sequence
  — unlocks `join`'s hash-path soundness and is shared with the BGP
  work.
* Extend the Spec module to Slice/OrderBy once an ordering discipline
  is decided (that decision is prior to the proof, not part of it).
