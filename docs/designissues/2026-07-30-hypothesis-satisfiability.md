# Hypothesis satisfiability: making the vacuity guard machine-checked

Status: LANDED 2026-07-30, branch `claude/vacuity-guard-20260730`.
Verify-only proof layer; no shipping module changed. No `admit`, no
`assume`, no `--lax`, no `--admit_smt_queries`; z3 4.13.3.

Module: [`formal/fstar/RDF.Semantics.HypothesisWitness.fst`](../../formal/fstar/RDF.Semantics.HypothesisWitness.fst)
(one new module, added to `build-ocaml.sh`'s `ALL_MODULES`).

Predecessors: the three semantic-refinement verticals —
[`2026-07-29-simple-entailment-refinement.md`](2026-07-29-simple-entailment-refinement.md),
[`2026-07-30-rdf-rdfs-entailment-refinement.md`](2026-07-30-rdf-rdfs-entailment-refinement.md),
[`2026-07-30-sparql-algebra-refinement.md`](2026-07-30-sparql-algebra-refinement.md).

---

## 0. 🔴 Read this first — the headline theorem of the RDFS vertical has no known instance

`RDF.Entailment.RDFS.ModelTheory.rdfs_closure_entails` — "the shipping
RDFS closure is RDFS-sound" — carries the hypothesis
`closure_chain_wf g`. **This commit could not discharge that hypothesis
for a single graph, including the empty one.** Two machine-checked
facts pin it down:

```fstar
// RDF.Semantics.HypothesisWitness.fst
val theorem_closure_chain_wf_n0_of_empty (_ : unit)
  : Lemma (ig_wf_sp (build_indexed (closure_iter [] 0)))

val theorem_closure_step_of_empty_is_nonempty (_ : unit)
  : Lemma (Cons? (rdfs_closure_step []) /\ Cons? (closure_iter [] 1))
```

The n = 0 conjunct holds for the empty graph, because `build_indexed []`
files nothing and `bucket_lookup` on an empty bucket serves nothing. The
chain does not stay there: `rdfs_rule_container_membership` emits its ten
`rdf:_1` … `rdf:_5` rows with no premise read from the data, so
`closure_iter [] 1` is a ten-triple graph with a populated sp-bucket, and
the n = 1 conjunct runs into §2's obstruction. `build_indexed` files
**every** triple into `ig_sp` (`bucket_key_sp t` is never `None`), so an
empty sp-bucket means an empty graph — and the empty graph leaves the
chain after one step. There is no third option.

⚠️ What this does and does not say. `closure_chain_wf` is satisfiable in
the mathematical sense — any graph whose IRIs and blank-node labels avoid
U+001F has a clean chain — so `rdfs_closure_sound` and
`rdfs_closure_entails` are **not vacuous**. What is missing is any
machine-checked instance, so neither theorem is *known in the tree* to
apply to any graph. That is a weaker defect than vacuity and a real one:
a theorem nobody can instantiate carries no assurance until someone can.

**The fix is named and scoped** — see §5, follow-up F-1.

---

## 1. Why this module exists

A theorem whose `requires` is unsatisfiable verifies cleanly and proves
nothing. This is not hypothetical. The first draft of `rdfs_closure_sound`
assumed

```fstar
(requires ... /\ (forall (h : rdf_graph). ig_wf_sp (build_indexed h)))
```

which is **false** — a blank-node label containing U+001F breaks `sp_key`
injectivity — and F\* reported "All verification conditions discharged
successfully". The landed form scopes the hypothesis to `closure_chain_wf`.
The story is §3 of the RDF/RDFS note.

Until this commit the guard against a repeat was a paragraph of prose. It
is now a module: for each hypothesis predicate a shipping-function
refinement theorem restricts on, a **satisfiability witness**, and where
the witness is degenerate or missing, that fact is itself a theorem or a
labelled gap.

📊 Scores: 22 new theorems and lemmas, 0 admits, 0 assumes. Single-module
verify **25.1 s** measured (`fstar.exe --z3version 4.13.3 --include .
--cache_checked_modules RDF.Semantics.HypothesisWitness.fst`, wall clock,
including a recheck of one stale dependency).

---

## 2. Part A — the interpretation-condition bundles are consistent

`rdfs_entails dd g1 g2` is `forall i. rdfs_conditions dd i ==>
satisfies i g1 ==> satisfies i g2`. `rdfs_conditions` is fifteen
conjuncts. If they were jointly unsatisfiable, `rdfs_entails` would be
the everything-relation and every soundness theorem in
`RDF.Entailment.RDFS.ModelTheory` would be vacuous. Nothing in the tree
proved they are jointly satisfiable.

```fstar
val theorem_rdf_conditions_satisfiable (_ : unit)
  : Lemma (exists (i : interp). rdf_conditions i)
val theorem_rdfs_conditions_satisfiable (dd : datatype_set)
  : Lemma (exists (i : interp). rdfs_conditions dd i)
val theorem_owl_rl_pilot_conditions_satisfiable (_ : unit)
  : Lemma (exists (i : interp). owl_rl_pilot_conditions i)
```

Witness for all three: the one-element interpretation.

```fstar
let trivial_interp : interp = {
  idom = unit; idom_wit = ();
  i_iri = (fun _ -> ()); i_lit = (fun _ -> ());
  i_tt = (fun _ _ _ -> ()); iext = (fun _ _ _ -> True);
}
```

Every `cond_*` is an implication whose conclusion is an `iext` atom, so
an all-true IEXT satisfies all of them. Each conjunct was checked, not
assumed. Two are worth naming:

* `cond_datatypes dd` constrains only `i_iri` (via `icext`), never
  `i_lit`, so the trivial model meets it for **every** `dd`, including
  the one that recognizes all IRIs.
* `cond_sameas_identity` is an **iff**, and its forward half forces
  `x == y` for every pair the all-true IEXT relates. This is why the
  domain has to be `unit` rather than an arbitrary nonempty type — the
  OWL pilot bundle would fail on a two-element domain.

---

## 3. Part A2 — and they are non-trivially satisfiable

An all-true IEXT satisfies **every** graph, so §2 proves consistency and
nothing more: it leaves open that `rdfs_entails` is the everything-relation
for a different reason. The sharper property is

```
exists (i : interp) (g : rdf_graph). rdfs_conditions dd i /\ ~(satisfies i g)
```

The task brief expected this to be out of reach. **It is not.** It holds,
and the corollary is the statement the soundness theorems actually need:

```fstar
val theorem_rdfs_conditions_nontrivially_satisfiable (dd : datatype_set)
  : Lemma (exists (i : interp) (g : rdf_graph).
             rdfs_conditions dd i /\ ~(satisfies i g))

val theorem_rdfs_entails_not_everything (dd : datatype_set)
  : Lemma (~(rdfs_entails dd [] unsat_graph))

val theorem_rdf_entails_not_everything (_ : unit)
  : Lemma (~(rdf_entails [] unsat_graph))

val theorem_pilot_entails_not_everything (_ : unit)
  : Lemma (~(pilot_entails [] owl_unsat_graph))
```

### 3.1 The three constructions that fail, and why

Recording these because they are the reason the working one looks odd.

| Attempt | Killed by |
|---|---|
| (a) Give one predicate an empty extension | `cond_subPropertyOf` concludes on an **arbitrary** property `q`: once `iext subPropertyOf r q` holds, IEXT(r) ⊆ IEXT(q). `cond_subPropertyOf_refl` and `cond_cmp_member` put enough pairs into IEXT(I(rdfs:subPropertyOf)) to make that bite |
| (b) Full extension for a set S of properties, empty otherwise | Same failure one level up: if I(rdfs:subPropertyOf) ∈ S its extension is everything, so IEXT(x) ⊆ IEXT(y) for **every** x and y, forcing S to be everything |
| (c) Exclude a triple by its **predicate** | Any element with an empty extension is killed by (b) again |

### 3.2 The construction that works — exclude by the OBJECT slot

```fstar
let sep_iext (p x y : bool) : prop = b2t (p && (y || not x))

let separating_interp : interp = {
  idom = bool; idom_wit = true;
  i_iri = (fun _ -> true);      // every IRI denotes the same resource
  i_lit = (fun _ -> false);     // every LITERAL denotes the other one
  i_tt  = (fun _ _ _ -> true);
  iext  = sep_iext;
}
```

Read as a relation: IEXT(`true`) is every pair **except** (`true`,
`false`); IEXT(`false`) is empty. The exclusion is invisible to
`cond_subPropertyOf` because the pairs that condition ranges over are
exactly (`true`,`true`), (`false`,`true`) and (`false`,`false`), and for
each of them the required containment already holds.

Consequence: a ground triple with an IRI subject and a **literal** object
is false in this model, and being ground, no blank-node assignment
rescues it.

```fstar
let unsat_triple : triple = { s = S_IRI ex_iri; p = ex_iri; o = T_Literal ex_lit }
```

The two axiomatic-triple conditions (`cond_rdf_axioms`,
`cond_rdfs_axioms`) are the only ones needing an argument: every RDF and
RDFS axiomatic triple has an **IRI object**, so its object denotes the
IRI-side resource and the excluded pair is never reached. That is checked
by `assert_norm (List.Tot.for_all obj_is_iri rdf_axiomatic_triples)` over
`RDF.Vocabulary.Axioms`' two transcribed lists — not asserted in prose.

### 3.3 The OWL pilot needs its own model

`separating_interp` fails `cond_sameas_identity`: `sep_iext true false true`
holds while `false == true` does not. The pilot bundle needs IEXT of the
`owl:sameAs` resource to be exactly the diagonal, which needs `owl:sameAs`
to denote something no other vocabulary IRI denotes:

```fstar
let owl_sep_iext (p x y : bool) : prop = if p then True else x == y

let owl_separating_interp : interp = {
  idom = bool; idom_wit = true;
  i_iri = (fun (a : wf_iri) -> a <> OwlC.owl_sameAs);
  i_lit = (fun _ -> true); i_tt = (fun _ _ _ -> true);
  iext  = owl_sep_iext;
}
```

That is the only place in the module where two IRIs have to be told apart.
The rejected graph is `[ ex owl:sameAs owl:sameAs ]`.

### 3.4 The witnesses do not prove False

An adversarial probe confirmed that chaining every theorem in the module
does **not** discharge `Lemma False` — the assertion fails, as it must. A
model that satisfies the conditions **and** rejects a graph would be worth
nothing if the underlying definitions were inconsistent.

---

## 4. Part B — the data-side restriction predicates

Every witness here is non-degenerate: a non-empty graph, a non-empty
binding, a non-empty solution mapping, and for `ptrm_exact` the
`PT_Literal` constructor — the only one of the five for which the
predicate says anything at all.

| Predicate | Defined at | Witness | Non-degeneracy also proved |
|---|---|---|---|
| `lit_exact`, `term_exact`, `triple_exact`, `graph_exact` | `RDF.Entailment.Simple.Spec.fst` | one-triple graph, `xsd:string` literal | `Cons? exact_graph`; plus `~(graph_exact inexact_graph)` for an `rdf:XMLLiteral` graph, so the fragment discriminates | 
| `binding_exact` | `RDF.Entailment.Simple.Refinement.fst:127` | `[("b0", T_IRI ex)]` | `Cons? exact_binding` |
| `leq_reflexive`, `leq_exact_identity` | `:147`, `:150` | the **shipping** `simple_leq`, via that module's own two lemmas | — |
| `bnd_total` | `:154` | the shipping `simple_bnd` | — |
| `smap_exact`, `seq_exact` | `SPARQL11.Algebra.Refinement.fst:121`, `:126` | two-entry `smap`, one-element sequence | `Cons?` on both |
| `ptrm_exact` | `:967` | `PT_Literal ex_lit` | `PT_Literal? exact_ptrm` |
| `ig_wf_pred` | `OWL.Semantics.fst:252` | hand-built index whose predicate bucket **serves a real triple** | `memP index_triple (bucket_lookup ... ex_iri)` |
| `ig_wf_sp` | `OWL.Semantics.fst:260` | 🔴 degenerate only — see §5 | — |
| `closure_chain_wf` | `RDF.Entailment.RDFS.ModelTheory.fst:594` | 🔴 none — see §0 | — |

The `leq_*` and `bnd_total` rows are deliberately witnessed by the
functions `simple_entails` actually passes to `entails_with`, not by
invented ones. Recording the existential in this module puts the witness
where a vacuity audit will look for it.

---

## 5. 🔴 The gap: `ig_wf_sp`, and `sp_key` is not injective

`ig_wf_sp ig` says the composite-key bucket serves up only triples with
exactly the queried subject and predicate. Two things are proved:

**It is a real restriction.** An index whose sp-bucket files a triple
under the composite key of a *different* subject falsifies it, so the
theorems that carry it are genuinely narrowed:

```fstar
val theorem_ig_wf_sp_not_universal (_ : unit) : Lemma (~(ig_wf_sp bad_sp_index))
```

**Its only available witness is degenerate.** The index below has a
non-empty graph and an *empty* sp-bucket, so the predicate holds because
the bucket serves nothing — exactly the shape this module exists to
reject, and labelled as such in the source:

```fstar
val theorem_ig_wf_sp_satisfiable_degenerately (_ : unit)
  : Lemma (ig_wf_sp degenerate_sp_index /\ Cons? degenerate_sp_index.ig_triples /\
           bucket_lookup degenerate_sp_index.ig_sp (sp_key (S_IRI ex_iri) ex_iri) == [])
```

### 5.1 The obstruction, sharpened

A non-degenerate witness needs `sp_key` **injectivity**, and `sp_key` is
not injective. The tree's finding F1 blames blank-node labels containing
U+001F. That is too narrow:

```fstar
val theorem_sp_key_not_injective (_ : unit)
  : Lemma (sp_key (S_IRI clash_iri_a) clash_iri_bc ==
           sp_key (S_IRI clash_iri_ab) clash_iri_c /\
           S_IRI clash_iri_a =!= S_IRI clash_iri_ab /\
           clash_iri_bc =!= clash_iri_c)
```

with `clash_iri_a = "a:"`, `clash_iri_ab = "a:<US>b:"`,
`clash_iri_bc = "b:<US>c:"`, `clash_iri_c = "c:"` (`<US>` = U+001F). Both
composite keys are `"I_a:" <US> "b:" <US> "c:"`. **No blank node is
involved.** `RDF.Term.is_iri` asks only for "non-empty and contains a
colon" (`RDF.Term.fsti:41`), so an IRI may itself contain U+001F, and two
different subject/predicate pairs — both with IRI subjects — collide.

### 5.2 Follow-ups

**F-1 (blocks §0).** Prove `sp_key` injective on U+001F-free keys, then
`ig_wf_sp (build_indexed g)` for a concrete non-empty `g`, then
`closure_chain_wf` for that `g`. The ingredients exist:
`FStar.String.list_of_concat` turns a concatenation into a `list char`
append, and `FStar.String.index_list_of_string` reads a position back
out. The missing piece is a "first occurrence of a separator splits
uniquely" lemma over `list char`. Estimated one commit; it unblocks the
whole RDFS closure-soundness chain.

**F-2.** Decide whether `is_iri` should reject control characters
(U+001F is forbidden in IRIs by RFC 3987 anyway — `RDF.Indexed.fsti`'s own
comment says so and then relies on it). Tightening `is_iri` would make
half of §5.1's counterexample unbuildable and shrink F-1's proof. This is
a change to a shipping predicate, so it is out of scope here.

**F-3.** Non-degenerate witnesses for the hypotheses of the OWL 2 RL
soundness proofs in `OWL.Semantics.Soundness.fst`, which were not
inventoried here.

---

## 6. The rule for the next vertical

Three sentences, to be copied into the next semantic-refinement note.

1. **A refinement theorem with a `requires` needs a satisfiability
   witness for its hypothesis, in
   `RDF.Semantics.HypothesisWitness.fst`.** A green checkmark on a
   theorem whose hypothesis is unsatisfiable is worth nothing, and F\*
   will not warn you.
2. **The witness must be non-degenerate.** Not the empty graph, not the
   empty binding, not the empty index. "The theorem holds of nothing" is
   the failure mode, so a witness that holds for the empty case has not
   ruled it out. If only a degenerate witness is reachable, say so in the
   module and open a follow-up — do not let it pass as a witness.
3. **For a condition bundle, prove two things, not one.** That the
   conjuncts are jointly satisfiable (consistency), *and* that some model
   of them rejects some graph (non-triviality). Consistency alone is
   satisfied by the all-true relation, which leaves the entailment
   relation possibly equal to everything.

A fourth, from §3.1: **when a construction fails, write down why.** The
three failed models in §3.1 are the whole reason the working one has the
shape it has, and a later reader would otherwise re-derive them.
