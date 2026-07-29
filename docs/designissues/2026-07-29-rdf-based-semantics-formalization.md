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

## External review 2026-07-29 (owner-run, external model; phase-2 specification)

The owner ran the two foundation questions (superset soundness; bnode
existential faithfulness) past an external model. The response is
preserved verbatim below and is the phase-2 work order: the W3C
embedding/truth-preservation theorem, the i_tt / OWL-2 theorem-surface
separation, the per-deviation enlargement audit, the rename to
"sufficient per-rule semantic conditions", the bundle-composition
lemma, the total-vs-graph-local assignment equivalence, the generic
fresh-assignment extension lemma (freshness / agreement-where-preserved
/ one-assignment-per-output-graph), and the no_fresh_bnodes_sound /
fresh_bnodes_sound theorem split.

```text
1. "Weakest-conditions superset"

Yes, in principle. The logical direction is correct.

Let:

* W be the genuine W3C class of OWL 2 RDF-Based interpretations;
* F be the formalisation's weaker class;
* W ⊆ F.

If the mechanisation proves

  ∀ I ∈ F,  I ⊨ G ⟹ I ⊨ R(G),

then it follows immediately for every I ∈ W. Therefore G entails R(G) under the genuine OWL semantics.

The design note states exactly this intended inclusion: omitted semantic conditions and retained one-way conditions enlarge the admitted interpretation class, so soundness over that larger class implies soundness over the standard class. The W3C definition likewise makes OWL entailment universal over all genuine OWL 2 RDF-Based interpretations.

What must actually be proved

The phrase "every deviation enlarges the interpretation class" should not merely be asserted. The load-bearing theorem should be an explicit embedding or conservativity lemma:

For every W3C OWL 2 RDF-Based interpretation J,
there exists a formal interp I such that:
1. I satisfies the formal condition bundle;
2. denotation of every relevant RDF term agrees;
3. truth of every relevant RDF triple and graph agrees.

Without that bridge, "superset" is an architectural intention, not a machine-checked fact.

Several listed changes are plausibly safe:

* Omitting semantic conditions enlarges the class.
* Replacing an iff condition by only the implication needed by a rule enlarges the class.
* Totalising IEXT outside the formal analogue of IP is harmless provided the values outside IP are semantically ignored.
* A total blank-node assignment is equivalent to the W3C graph-local partial assignment because the interpretation domain is nonempty.

But not every representational simplification is automatically class-enlarging. A new datatype, constructor, equality principle, compositionality requirement, or fixed vocabulary discipline could accidentally restrict the structures that can be represented. The note's i_tt triple-term constructor particularly deserves separation from the OWL 2/RDF 1.1 theorem surface: OWL 2 RDF-Based Semantics is defined over the RDF semantics of its period, not RDF 1.2 triple terms.

What is lost

Nothing is lost for the narrow claim:

  This executable rule is sound with respect to OWL 2 RDF-Based semantics.

But several stronger results are lost:

* Completeness: failure to prove or derive a conclusion in the weak class says nothing about whether OWL entails it.
* Exact characterisation: entails_under weak_conditions is generally weaker than OWL entailment.
* Countermodels: a countermodel in the enlarged class need not be a legal OWL model, so it does not establish OWL non-entailment.
* Inconsistency detection: a graph satisfiable in the enlarged class may be inconsistent under the full semantics.
* Composition across changing bundles: the overall driver theorem must use a condition bundle sufficient for every constituent rule. Per-rule proofs against different weak classes do not automatically compose unless a common stronger bundle implies all their assumptions.

There is also a terminology issue. "Weakest conditions" is safe only if minimality has actually been established. What the pilot appears to use is better described as sufficient per-rule semantic conditions. They may be weak without being weakest.

Verdict on question 1

Sound, subject to one required addition: formalise and prove the W3C-to-interp embedding/truth-preservation theorem. The current direction of implication is right. What is intentionally surrendered is completeness, standard-valid countermodels, and exact equivalence with OWL entailment.

2. Blank-node existentials and assignment threading

The core definition is faithful:

  satisfies i g = exists a. holds_all i a g

Hayes' condition says that an interpretation satisfies a graph when there exists a mapping from the blank nodes of that graph into the interpretation domain that makes the graph true. Treating blank nodes as existentially quantified variables over the conjunction of graph triples is exactly the intended reading.

Using a total function

  bnode_id -> idom

rather than a function whose domain is precisely the graph's blank nodes is also faithful. Since idom is inhabited, any graph-local assignment can be extended arbitrarily to all blank-node identifiers; conversely, a total assignment can be restricted to the blank nodes occurring in the graph.

Reusing the input assignment

For a rule that introduces no fresh blank nodes, proving

  ∀ a,  holds(I,a,G) ⟹ holds(I,a,R(G))

is stronger than necessary but sound.

From ∃ a. holds(I,a,G) one chooses that witness a, applies the theorem, and repackages the same a as the existential witness for the output. The note's unpack/repack argument is therefore correct.

This does not incorrectly force the antecedent and consequent blank nodes to have a shared existential scope in the definition of entailment. It merely constructs a valid witness for the consequent from a witness for the antecedent. Consequent satisfaction still has its own existential quantifier.

Fresh blank nodes

The proposed shape is also correct:

  holds(I,a,G) ⟹ ∃ a'. a'|bnodes(G) = a|bnodes(G) ∧ holds(I,a',R(G)).

However, "assignment-extension construction" alone is not enough. For each minted blank node, the proof must obtain an appropriate semantic witness from the relevant OWL condition. The extension combinator only records those witnesses in an assignment.

Three conditions need to be explicit:

1. Freshness: minted identifiers must not collide with any blank node already in the input graph or with one another when distinct witnesses are required syntactically.
2. Agreement only where needed: agreement should be required on blank nodes whose occurrences are preserved from the input, not necessarily on every global identifier.
3. One output graph: all triples emitted in a single rule result share one existential assignment. Different locally constructed witnesses cannot be proved independently and then combined unless their assignments are shown compatible.

The W3C semantics warns that blank-node identity and scope depend on whether graphs are unioned, merged, or share nodes. The implementation appears to operate on a single accumulated graph, so threading one assignment through that accumulated graph is the correct model. If the formal API later handles collections of graphs independently, it will need an explicit union/merge policy; RDF 1.1 does not define entailment directly between arbitrary sets of graphs without first combining them.

A useful theorem split

I would encode two reusable lemmas:

  no_fresh_bnodes_sound:
    holds_all I a G ->
    holds_all I a (R G)

  fresh_bnodes_sound:
    holds_all I a G ->
    exists a'.
      agrees_on (bnodes G) a a' /\
      holds_all I a' (R G)

Then derive the satisfaction theorem uniformly. This makes the stronger no-fresh result visibly distinct from the genuinely existential fresh-witness case.

Verdict on question 2

Yes. The existential satisfaction definition and same-assignment threading for no-fresh-blank-node rules are faithful to Hayes. For witness-producing rules, the proposed assignment-extension shape is also right, provided freshness, compatibility, and the semantic source of each witness are proved explicitly.

Bottom line

The design is viable. I would not commit the full programme without adding these two formal obligations near the foundation:

1. W3C embedding/truth preservation: every genuine relevant OWL interpretation induces a formal interp satisfying the chosen conditions, with graph truth preserved.
2. Blank-node assignment equivalence: total assignments are equivalent to Hayes' graph-local mappings, plus a generic fresh-assignment extension lemma.

Those lemmas turn the two most consequential informal arguments in the note into checked infrastructure rather than recurring proof assumptions.
```

### Review addendum (same day, follow-up)

Verbatim: "The semantic baseline needs to be pinned down. The design
note says it transcribes RDF 1.1 Semantics, while claiming soundness
against OWL 2 RDF-Based Semantics. But the normative OWL 2
specification from 2012 explicitly builds on the 2004 RDF Semantics,
not RDF 1.1, which appeared in 2014." (Owner adds: RDF 1.2 muddies the
waters further.) Phase-2 obligation added: pin the theorem surface to
OWL 2 (2012) over its normative 2004 RDF basis; audit every
RDF-1.1-flavored representation choice (literal typing / rdf:langString
vs 2004 plain literals, IRIs vs RDF URI references, datatype-map
framing) as enlarging/neutral/restricting relative to 2004-based
interpretations, with a delta table; quarantine all RDF 1.2 constructs
from the theorem surface alongside i_tt.
