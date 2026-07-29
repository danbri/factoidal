# Formalizing the OWL 2 RDF-Based Semantics in F\* and proving the RL rule set sound — strategy + pilot report

Status: PILOT LANDED (2026-07-29). Four shipping rules proven sound,
end to end, machine-checked, no admits, no `--lax`.
Owner steer (2026-07-29, verbatim): "the most appealing is 'formalize
the RDF-Based semantics itself in F\* and prove the RL rule set sound
against it'".

Branch: `claude/owl-semantics-soundness-pilot-20260729`
(base: `claude/autoexec-scratchpad-assess-37oeok`).

## 1. What landed

| Module | Role | Status |
|---|---|---|
| `formal/fstar/OWL.Semantics.fst` | Interpretations, denotation, satisfaction, entailment, semantic sequences, the pilot condition bundle, index well-formedness hypotheses | ✅ verified |
| `formal/fstar/OWL.Semantics.MemLemmas.fst` | `fold_left_inv` + memP preservation through the shipping sort/group/bisect index pipeline; `build_indexed` bucket well-formedness | ✅ verified |
| `formal/fstar/OWL.Semantics.Soundness.fst` | The four rule soundness theorems + entailment corollaries | ✅ verified |
| `formal/fstar/OWL.Closure.fsti` | `owl_rule_cls_oneof` lambda-lifted (behaviour-identical; see finding F3) | ✅ re-verified |
| `formal/fstar/build-ocaml.sh` | Three new modules added to `ALL_MODULES` (extract loop = whole-tree verification vehicle) | ✅ |

Rules PROVEN sound (the exact shipping functions, by name):

| Shipping function | OWL 2 RL/RDF rule | Theorem | Entailment corollary |
|---|---|---|---|
| `RDFS.Closure.rdfs_rule_domain` | rdfs2 | `rdfs_rule_domain_sound` | unconditional vs `build_indexed` |
| `OWL.Closure.owl_rule_symmetric_property` | prp-symp | `owl_rule_symmetric_property_sound` | unconditional, any index |
| `OWL.Closure.owl_rule_sameAs_symmetry` | eq-sym | `owl_rule_sameAs_symmetry_sound` | unconditional vs `build_indexed` |
| `OWL.Closure.owl_rule_cls_oneof` | cls-oo | `owl_rule_cls_oneof_sound` | conditional on finding F1 (ig_sp key recovery) |

No pilot rule was found unsound under the formalized conditions.
Three structural findings (F1–F3, section 6) are the pilot's main
non-theorem output.

## 2. Literature grounding

- **Hayes / Patel-Schneider, RDF 1.1 Semantics (W3C Rec 2014-02-25)**
  — simple interpretations (IR, IEXT, IS, IL), truth of triples and
  graphs, existential blank-node semantics via "mapping A". Our
  `interp` / `denot_*` / `satisfies` transcribe section 5; the
  rdfs2/rdfs3 conditions come from the RDFS interpretation section.
- **OWL 2 RDF-Based Semantics (W3C Rec 2012-12-11, M. Schneider)** —
  the interpretation structure (IR/IP/IEXT/ICEXT, ICEXT derived from
  IEXT of `rdf:type`), the semantic-conditions tables (equality
  Table 5.2 for `owl:sameAs`, property characteristics Table 5.14
  for `owl:SymmetricProperty`, enumerations Table 5.9 for
  `owl:oneOf`), and the note that the **comprehension conditions of
  its appendix are informative** — load-bearing for the CONDITIONAL
  bucket in section 5: witness-minting rules cannot be sound w.r.t.
  the normative conditions alone.
- **ter Horst, JWS 2005** ("Completeness, decidability and complexity
  of entailment for RDF Schema and a semantic extension involving the
  OWL vocabulary") — the pD\* system: soundness and completeness
  analysis for exactly this style of if-semantics rule set, including
  the finite-model property. His per-rule soundness arguments
  ("if I satisfies the antecedent triples and the if-condition of the
  vocabulary holds, I satisfies the consequent") are the paper
  analogue of what `OWL.Semantics.Soundness.fst` mechanizes; the
  weakest-precondition style of our conditions (section 4.3) is his
  if-semantics discipline.
- **OWL 2 Profiles (W3C Rec), theorem PR1** — asserts the RL rule
  set's soundness w.r.t. the RDF-Based Semantics, with paper proof.
  Our program is the machine-checked counterpart, against the
  *executable* rules rather than the abstract rule table.
- **Prior mechanizations** — [CoqRDF](https://repositorio.uchile.cl/bitstream/handle/2250/197654/A-Coq-formalization-of-RDF-and-its-applications.pdf?sequence=1&isAllowed=y)
  (U. Chile, Coq + Mathematical Components) mechanizes RDF 1.1
  **abstract syntax** and graph isomorphism (κ-mapping), not the
  model theory; we found no accessible mechanization of the RDF or
  OWL 2 RDF-Based *satisfaction/entailment* relations, and none that
  proves an executable rule engine sound against them. That gap is
  the flagship claim this program builds toward.

## 3. The five design questions, answered by the pilot

### 3.1 Interpretation representation

`OWL.Semantics.interp` is a dependent record: `idom : Type0` (with a
witness inhabitant), total maps `i_iri : wf_iri -> idom`,
`i_lit : wf_literal -> idom`, a compositional triple-term constructor
`i_tt`, and IEXT as a curried ternary **prop**
`iext : idom -> idom -> idom -> prop`.

- **Infinite domains and datatype value spaces enter for free**: any
  F\* type may serve as `idom`; satisfaction is *definable* (a prop)
  without being *decidable*, and nothing ever needs to decide it —
  the theorems quantify over it.
- **Every deviation from the W3C structure enlarges the
  interpretation class** (IEXT totalized over IR instead of typed on
  IP; IL totalized; no datatype-map conformance; only the
  if-directions of iff table rows). A rule proven sound over the
  larger class is sound over every genuine OWL 2 RDF-Based
  interpretation. This one-way discipline is THE load-bearing shape
  decision: it makes the framework small without weakening any
  soundness claim. (It deliberately gives up completeness statements;
  those would need the missing conditions, and are out of scope.)

### 3.2 Satisfaction and entailment

Two levels, and the split is what makes the proofs mechanical:

- `holds_all i a g` — truth of every triple of `g` under a FIXED
  bnode assignment `a` (a total function `bnode_id -> idom`;
  totalizing is again class-enlarging).
- `satisfies i g = exists a. holds_all i a g` — Hayes' existential
  semantics; `entails_under conds g1 g2` quantifies over all
  interpretations satisfying the condition class.

Assignment threading: every pilot rule mints **no fresh blank
nodes**, so the assignment chosen for the input graph works verbatim
for the output graph — the main theorems live at the `holds_all`
level with `a` universally quantified, and the `satisfies`-level
corollaries just unpack/repack the existential. Rules that DO mint
bnodes need an assignment-extension construction (section 5, bucket
E) — the framework anticipates it but the pilot did not need it.

The index snapshot is a separate hypothesis: rules take `(g, ig)`
where `ig` is the step-input snapshot, so theorems carry
`holds_all i a ig.ig_triples` alongside `holds_all i a g` plus a
syntactic well-formedness hypothesis per bucket used (`ig_wf_pred`,
`ig_wf_sp`). At the driver level `ig = build_indexed g0` with
`ig_triples = g0` definitionally, so the corollaries discharge the
truth hypothesis for free and the bucket hypotheses via
`OWL.Semantics.MemLemmas` (fully for `ig_pred`; partially for
`ig_sp` — finding F1).

### 3.3 Which semantic conditions, and how attached

Conditions are **prop-valued predicates over `interp`**, one small
`cond_*` per table row, bundled by conjunction
(`owl_rl_pilot_conditions`); `entails_under` takes the bundle as a
parameter. No refinement types on `interp` — a plain prop parameter
composes (later waves grow the bundle without touching old
theorems), and hypotheses stay visible in every statement.

Pilot bundle: `cond_domain`, `cond_range` (RDFS conditions),
`cond_symmetric` (Table 5.14, if-direction), `cond_sameas_identity`
(Table 5.2, the full iff — both directions are what the table says
and the congruence family needs both), `cond_oneof` (Table 5.9,
superset half).

**The oneOf condition-form subtlety (F2, resolved in the sound
direction):** Table 5.9 reads "if ⟨c,l⟩ ∈ IEXT(I(owl:oneOf)) and l
is a sequence of a1…an over IR, then ICEXT(c) = {a1…an}". We encode
the sequence reading as a *premise* (`seq_is`, a recursive prop
transcribing the spec's sequence definition, nil-terminated), i.e.
the condition constrains EVERY sequence reading of `l`. Under the
alternative purely-existential reading ("there is some sequence…"),
cls-oo would additionally require functionality of rdf:first/rest to
be sound — which the RDF-Based semantics does not assert. The
hypothesis-form reading is the spec's grammatical form and the one
under which Profiles PR1 is provable; the proof of
`decode_iri_list_sound` shows the shipping decoder only ever
produces genuine nil-terminated readings, so the premise is
satisfied by construction. Any future condition transcription MUST
preserve this premise-form for list-shaped table rows.

### 3.4 The per-rule soundness statement

```fstar
val <rule>_sound (i : interp) (a : bnode_assignment i.idom)
                 (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires cond_<needed> i /\ holds_all i a g /\
                    holds_all i a ig.ig_triples /\ ig_wf_<buckets> ig)
          (ensures  holds_all i a (<shipping_rule> g ig))
```

plus a `pilot_entails g (<shipping_rule> g (build_indexed g))`
corollary. The `ensures` names the SHIPPING function — the proof
pins to it in one of two ways:

1. **assert_norm pinning** (rules 1–3): the proof restates the
   rule's fold with local let-bound copies, proves truth
   preservation via the generic `fold_left_inv`, and closes with
   `assert_norm (<rule> g ig == List.Tot.fold_left my_step ...)`,
   which the normalizer discharges by delta/zeta/alpha equality.
2. **Named-step shape** (rule 4): when a rule's emission lambda sits
   under match binders, the encoder blocks technique 1 (finding F3);
   the rule body itself is lambda-lifted to named top-level step
   functions, and the proof references those names — congruence does
   the rest, no assert_norm needed.

### 3.5 What the full program costs

Inventory: **79 `owl_rule_*`** in `OWL.Closure.fsti` + **7
`rdfs_rule_*`** in `RDFS.Closure.fsti`, plus `is_inconsistent` (10
clash checks), the fixpoint drivers, and `entailment_closure`.
Bucketed by pilot experience (times = one focused agent-session per
line unless noted):

- **A. Fold-and-emit, no index or ig_pred only** (~20 rules:
  eq-diff-sym, prp-inv1/2, cls-eqc/eqp pairs, scm-eqc2/eqp2,
  scm-dom2/rng2, rdfs3/5/7/9/11, container-membership,
  inverseOf-domain-range-flip, reflexive_property,
  xsd axiom emitters, …). Template-degree work after the pilot:
  2–5 rules per session. The axiom-emitter rules additionally need
  vocabulary-level conditions (their triples are tautologies of the
  condition class — new `cond_*` per vocabulary block).
- **B. ig_sp / ig_po consumers** (~25 rules: transitive_property,
  sameAs_transitivity, subClassOf via `find_objects_indexed`,
  functional/inverse-functional, prp-key join steps, …). Same
  template + the F1 hypothesis; 1–3 rules per session. Resolving F1
  once (see below) upgrades all of bucket B to unconditional.
- **C. List-walking** (~12 rules: cls-int1, cls-uni(+elim),
  oneof_set_equivalence, prp-key, property_chain_n, all_disjoint_*,
  allDifferent_*, …). `decode_iri_list_sound` is reusable as-is;
  each rule needs its lambda-lift refactor (F3) + one session.
  Chain/key rules add a per-element join argument: 1–2 sessions
  each.
- **D. sameAs congruence family** (eq-rep-s/p/o, functional-property
  sameAs emission): the identity condition makes these direct;
  the metapredicate-guard in eq-rep-p (skips `is_owl_metapredicate`)
  is skip-only (dropping emissions is always sound). 1 session for
  the family.
- **E. CONDITIONAL: witness/comprehension/narrow rules** (~15:
  `owl_rule_svf2_existential_witness`, `cls_hasself2_synth`,
  `cls_svf_thing_witness`, the `owl_rule_comp_*` comprehension
  family, `minc1_bridge`, `cls_maxqc1`-family anchors (#236),
  `fp_pinned_subproperty`, `singleton_nominal_functionality`,
  `named_equivClass_to_sameAs`, `pdw*_to_differentFrom`, …). Three
  sub-cases the framework must express distinctly:
  1. *Fresh-bnode witnesses*: need the assignment-extension lemma
     (`holds_all i a g ==> holds_all i a' (rule g ig)` for an `a'`
     agreeing with `a` on `g`'s bnodes — satisfaction-level soundness
     survives, `holds_all`-level does not). One framework session to
     build the extension combinator, then per-rule work.
  2. *Comprehension-dependent rules*: sound only under the
     RDF-Based appendix's **informative** comprehension conditions —
     state them as an explicitly separate `cond_comprehension_*`
     bundle so the theorem's weaker status is visible in its type.
  3. *Known-narrow rewrites* (#236 family): expected NOT to be sound
     as stated; the correct deliverable is a precise UNSOUNDNESS
     witness or a conditional theorem naming the narrowing
     hypothesis. Budget these as findings work, not proof work.
- **Drivers**: one session — soundness composes over sequential rule
  application and `graph_dedup_sort` (memP-preserving, lemmas
  already in `MemLemmas`), then fixpoint induction over fuel.
  `rdf_property_axiom_closure` and reflexivity harvesting join
  bucket A.

Rough total: ~30–45 focused sessions for the normative-soundness
surface (buckets A–D + drivers), parallelizable 3–4 wide after the
condition bundle for each wave is agreed (conditions are the shared
surface — merge conflicts concentrate in `OWL.Semantics.fst`, so
each wave should land its `cond_*` additions first, small and fast).

## 4. Proof-engineering assets (reuse these)

- `fold_left_inv` (`MemLemmas`) — the one induction every rule uses,
  with the step obligation established by an `introduce forall`
  block. Nested folds nest the pattern.
- `lemma_build_bucket_ok` → `lemma_build_indexed_wf_pred` /
  `_wf_sp_weak` — membership + key correctness through the shipping
  sortWith/partition/group/bisect pipeline (all memP-based; the
  stdlib's eqtype lemmas don't apply to `noeq` triples).
- `decode_iri_list_sound` — syntactic list decode ⇒ semantic
  sequence reading; the de-risking result for every list rule.
- `lemma_denot_subject_to_term` / `lemma_denot_term_to_subject` —
  the object↔subject round-trip every emission arm needs.
- `lemma_rdf_term_eq_iri` — boolean structural equality to
  propositional equality, extend per constructor as rules need.

## 5. Verification and build wiring

The three modules are **proof-layer**: their extraction erases to
inert `.ml` (verified empirically; `--codegen OCaml` succeeds).
Decision: added to `build-ocaml.sh`'s `ALL_MODULES` only — that list
is the whole-tree verification vehicle (`extract` checks every
module via `--cache_checked_modules`), so CI keeps the proofs green.
NOT added to `COMMON_MODULES` or any binary link list: nothing
consumes them at runtime, and keeping them out of the link keeps
every binary byte-identical. Measured single-module verify times
(warm `.checked` deps, container hardware): Semantics ~40 s,
MemLemmas ~50 s, Soundness ~3 min.

## 6. Findings

- **F1 (formal gap, pre-existing): `ig_sp` composite-key component
  recovery is unproven and unprovable as-is.** Rules that read
  `find_objects_indexed` assume a bucket entry under `sp_key s p`
  has subject `s` and predicate `p`. `MemLemmas` proves membership
  plus the key EQUATION (`sp_key t.s t.p == sp_key s p`); recovering
  the components needs `sp_key` injectivity, which fails if a
  blank-node label may contain U+001F (`RDF.Indexed`'s own comment
  asserts "never appears in our blank-node keys" — nothing enforces
  it; `bnode_id` is a bare `string`). Not an observed unsoundness
  (no parser emits such labels), but it is exactly the kind of
  unenforced representation invariant this program exists to
  surface. Fix options, in preference order: (a) refine `bnode_id`
  to exclude U+001F at the type level (touches parsers' bnode
  construction sites); (b) prove injectivity from a graph-level
  well-formedness predicate threaded through the closure drivers.
  Until fixed, ig_sp-consuming theorems carry `ig_wf_sp` as an
  explicit hypothesis — never assume it silently.
- **F2: the oneOf sequence-reading premise-form** (section 3.3) — a
  transcription rule for all future list-shaped semantic conditions.
- **F3 (proof-shape rule): inline emission lambdas under match
  binders are unprovable-about.** F\*'s SMT encoding gives each such
  lambda occurrence a closure symbol a separate proof term cannot
  re-reference (probed exhaustively: local/top-level copies, shared
  local bindings, ifuel bumps all fail; arms that don't mention
  pattern binders reduce fine). The fix is lambda-lifting the rule's
  step functions to named top-level definitions — behaviour-
  identical, extraction-clean, and congruence then closes every
  gap. `owl_rule_cls_oneof` is the worked example
  (`owl_cls_oneof_emit` / `owl_cls_oneof_step`); the remaining
  list-walking rules need the same one-time refactor as their
  proofs land, and NEW rules should be written in lifted shape from
  the start.

## 7. Rebase surface

- `OWL.Closure.fsti`: the cls_oneof lambda-lift (one function + two
  new names). Sibling agents (`-wt-datatype`, `-wt-rangeiff`) were
  running against the same base; whoever lands second resolves a
  small, mechanical conflict in that one region plus the three-line
  `build-ocaml.sh` ALL_MODULES addition.
- Proofs are pinned to the branch-base rule bodies. If a sibling
  changes a proven rule's body, the proof breaks LOUDLY at
  `assert_norm`/congruence — that is the designed behaviour (the
  theorem is about the exact executable text), and the fix is
  re-running the proof template against the new body.

## 8. The three hardest design decisions (and the options not taken)

1. **Weakest-conditions superset class vs full W3C fidelity.** Full
   fidelity (IP typing, datatype maps, iff conditions) would permit
   completeness work but multiplies every proof's obligations and
   adds nothing to soundness. Chose the superset class with the
   one-way guarantee stated once (section 3.1). Revisit only if
   completeness (ter Horst-style) becomes a goal.
2. **Index hypotheses vs reference-scan re-statement.** Restating
   rules against a naive scan and proving scan≡index would detach
   theorems from the shipping perf shapes (and quietly assume F1
   anyway). Chose explicit `ig_wf_*` hypotheses discharged against
   `build_indexed` — which is how F1 surfaced instead of hiding.
3. **Direct binding to shipping lambdas vs a verified model of the
   rules.** A parallel model is the anti-pattern the owner named
   ("rules proven correct", not "a model of the rules"). Direct
   binding cost real proof-engineering (F3's probe campaign, one
   lambda-lift refactor) but every theorem now names the function
   the engine runs. The price is codified as the F3 shape rule so
   later sessions pay it at write-time, not proof-time.
