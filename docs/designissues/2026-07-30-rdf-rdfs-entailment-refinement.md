# RDF and RDFS entailment: the semantic-refinement pattern, applied twice more

Status: LANDED 2026-07-30 on `claude/rdfs-refinement-20260730`. Sound
at both rungs, model-theoretically grounded, findings machine-checked.
No admits, no `--lax`, no `--admit_smt_queries`, z3 4.13.3. No shipping
module edited.

Predecessor: [`2026-07-29-simple-entailment-refinement.md`](2026-07-29-simple-entailment-refinement.md)
— rung one of Hayes' ladder. This note is rungs two and three: RDF
entailment and RDFS entailment. Its §7 reusable-pattern list is the
method followed here; §8 below records what transferred, what did not,
and what the next rung needs.

## 0. 🔴 Read this first — finding RS-1, an unsoundness in shipping code

`RDFS.Closure.rdfs_reflexivity_axioms` is **unsound at the RDFS rung**,
with a machine-checked witness.

```fstar
// RDF.Entailment.RDFS.Refinement.fst
val reflexivity_axioms_not_rdfs_sound (c : wf_iri)
  : Lemma (memP (owl_class_refl_triple c)
                (rdfs_reflexivity_axioms (owl_class_graph c)) /\
           ~(rdfs_licensed d_minimal (owl_class_graph c) (owl_class_refl_triple c)))
```

where `owl_class_graph c = [ c rdf:type owl:Class ]` and
`owl_class_refl_triple c = c rdfs:subClassOf c`.

In words: on a one-triple graph, the shipping function emits
`c rdfs:subClassOf c`, and **no row of the RDF or RDFS entailment rule
table licenses that triple**, and it is not an axiomatic triple of
either vocabulary. No hypothesis on `c` is needed — the emitted triple
is a self-loop, and every axiomatic `rdfs:subClassOf` row has distinct
endpoints.

**Cause.** `collect_classes` treats an IRI as a class if it is the
subject or IRI-object of `rdfs:subClassOf`, **or** the subject of
`rdf:type rdfs:Class`, **or** the subject of `rdf:type owl:Class`.
`collect_properties` is the dual and additionally accepts
`owl:ObjectProperty` and `owl:DatatypeProperty`. The first three
sources are licensed by RDF 1.1 Semantics §9 (subject and object of a
`subClassOf` triple are in IC; ICEXT(I(rdfs:Class)) **is** IC; rdfs10
emits exactly this triple from `rdf:type rdfs:Class`). The OWL sources
are not: `owl:Class` is an ordinary IRI to an RDFS interpretation.

**⚠️ The contrast that makes this interesting.** The same code is
**sound** in the OWL-RL regime: OWL 2 RDF-Based Semantics Table 5.3
identifies ICEXT(I(owl:Class)) with IC. `entailment_closure` dispatches
`"RDFS"` and `"OWL-RL"` to code that shares this function, so one
regime's licence is being spent in the other. This is the RDFS-rung
analogue of the simple rung's finding SE-1 (`literal_eq`'s XMLLiteral
canonicalisation, unlicensed at the simple rung and **licensed** at the
RDF rung — see §5's delta table row D2). Both are the same shape:
a D-or-OWL-level behaviour leaking down a rung.

**Practical impact.** One-directional (the closure gets larger), so no
test expecting an entailment can fail because of it. It can make a
`NegativeEntailmentTest` wrongly pass, and it can make an inconsistency
check wrongly fire — which is exactly the mechanism already recorded
in `RDFS.Closure.fsti`'s `rdfs_closure_with_reflexivity` banner for the
reverted axiom seeding (OWL 2 profile-RL `New-Feature-ObjectQCR-002`,
76 pass 0 fail → 75 pass 1 fail).

**Fix, if wanted.** Split the harvest: an RDFS-regime `collect_classes`
that reads only `rdfs:subClassOf` positions and `rdf:type rdfs:Class`,
and an OWL-regime one that additionally reads the OWL typing IRIs.
Structurally trivial; it is a behaviour change to a shipping function,
so it is out of scope here. Consequence for this vertical:
`rdfs_closure_with_reflexivity` is **deliberately not proven sound**.
Weakening the specification until that proof closes is precisely what
this pattern exists to prevent.

The model-theoretic half is
`RDF.Entailment.RDFS.ModelTheory.reflexivity_needs_rdfs_Class`: the
only premise-free route the RDFS conditions offer to a `subClassOf`
self-loop is membership in IC.

## 1. What landed

| Module | Role | Lines | Status |
|---|---|---|---|
| `formal/fstar/RDF.Entailment.RDF.Spec.fst` | RDF rung, declarative. RDF 1.1 Semantics §8: rdfD1 / rdfD2, the recognized-datatype set D, the axiomatic triples, `rdf_closed` | 209 | ✅ |
| `formal/fstar/RDF.Entailment.RDFS.Spec.fst` | RDFS rung, declarative. RDF 1.1 Semantics §9: the complete rdfs1–rdfs13 table quoted row by row, the axiomatic triples, `rdfs_closed`, the rho-df fragment | 380 | ✅ |
| `formal/fstar/RDF.Entailment.RDFS.Refinement.fst` | The shipping rules against those tables; findings RS-1 … RS-4 | 788 | ✅ |
| `formal/fstar/RDF.Entailment.RDFS.ModelTheory.fst` | RDF/RDFS interpretation conditions, rule-table soundness, closure soundness | 724 | ✅ |
| `formal/fstar/build-ocaml.sh` | four `ALL_MODULES` entries (whole-tree verification vehicle) | — | ✅ |

Neither Spec module opens `RDFS.Closure`, `OWL.Closure`,
`RDF.Graph.Executable` or `RDF.Entailment.Regime`, so each can be
diffed against the W3C text on its own. Both reuse
`RDF.Vocabulary.Axioms`' already-verified, per-row-cited axiomatic
tables rather than making a second copy.

### The theorems, by name and statement

```fstar
// RDF.Entailment.RDFS.Refinement.fst — transcription fidelity.
// "Every triple the shipping rule emits is in the seed graph, or is
//  derived from the SOURCE graph by one application of the rule row
//  it claims to implement."

val rdf_property_axiom_closure_licensed (g : rdf_graph)                       // rdfD2
  : Lemma (forall t. memP t (rdf_property_axiom_closure g) ==>
                     (memP t g \/ rdfD2_derives g t))

val rdfs_rule_domain_licensed (g) (ig)                                        // rdfs2
  : Lemma (requires ig_wf_pred ig)
          (ensures licensed_by2 rdfs2_derives ig.ig_triples g (rdfs_rule_domain g ig))

val rdfs_rule_range_licensed (g) (ig)                                         // rdfs3
val rdfs_rule_subPropertyOf_licensed (g) (ig)                                 // rdfs7
val rdfs_rule_subClassOf_licensed (g) (ig)                                    // rdfs9
val rdfs_rule_subClassOf_trans_licensed (g) (ig)                              // rdfs11
val rdfs_rule_subPropertyOf_trans_licensed (g) (ig)                           // rdfs5
val rdfs_rule_container_membership_licensed (g) (ig)                          // RDFS axioms
  : Lemma (forall t. memP t (rdfs_rule_container_membership g ig) ==>
                     (memP t g \/ rdfs_axiomatic t \/ rdfs_member_subproperty t))

// the unsoundness witness
val reflexivity_axioms_not_rdfs_sound (c : wf_iri)                            // RS-1
```

```fstar
// RDF.Entailment.RDFS.ModelTheory.fst — semantic justification.

// every row of the RDF/RDFS rule tables is truth-preserving.
// No engine function appears in this statement.
val rdfs_licensed_true (dd) (i : interp) (a) (g) (t)
  : Lemma (requires rdfs_conditions dd i /\ holds_all i a g /\ rdfs_licensed dd g t)
          (ensures  triple_holds i a t)

// one shipping closure step, then the whole fixed-point driver
val rdfs_closure_step_sound (dd) (i) (a) (g)
  : Lemma (requires rdfs_conditions dd i /\ holds_all i a g /\
                    ig_wf_sp (build_indexed g))
          (ensures  holds_all i a (rdfs_closure_step g))

val rdfs_closure_sound (dd) (i) (a) (g) (fuel : nat)
  : Lemma (requires rdfs_conditions dd i /\ holds_all i a g /\ closure_chain_wf g)
          (ensures  holds_all i a (rdfs_closure g fuel))

// THE HEADLINE
val rdfs_closure_entails (dd) (g) (fuel : nat)
  : Lemma (requires closure_chain_wf g)
          (ensures  rdfs_entails dd g (rdfs_closure g fuel))

val rdf_property_axiom_closure_entails (g)
  : Lemma (rdf_entails g (rdf_property_axiom_closure g))
```

`rdfs_entails dd g1 g2` is
`forall (i : interp). rdfs_conditions dd i ==> satisfies i g1 ==> satisfies i g2`
— RDF 1.1 Semantics §9's definition, on `OWL.Semantics`' interpretations.

Per-row soundness lemmas (`rdfD2_true`, `rdfs1_true` … `rdfs13_true`,
`rdfs_member_subproperty_true`) each name **exactly the one condition**
the row needs. That is itself a machine-checked statement of which
rule belongs to which regime — see finding RS-5.

## 2. The three-part soundness argument, and why it is split that way

A closure rule is a graph transformer, not a decision procedure, so
"sound" has to be assembled:

1. **Transcription fidelity** (Refinement). Every emitted triple is
   licensed by a named row of the W3C table, applied to a named source
   graph. Checkable against the spec text by a reader who knows no
   model theory.
2. **Rule-table soundness** (ModelTheory §3). Every row is
   truth-preserving under the §8/§9 interpretation conditions. Names
   no engine function; checkable by a reader who has never seen this
   codebase.
3. **Composition** (ModelTheory §4). 1 + 2, chained through
   `rdfs_closure_step`'s seven-rule pipeline and then through the
   fuel-bounded fixed point.

Splitting 1 from 2 is what makes each half auditable in isolation. It
also localises the findings: RS-1 is a failure of (1) with no (2) to
appeal to; RS-5 is a mismatch between which (2) a regime is entitled to.

### The shape decision that made step 3 possible

`rdfs_closure_step` builds **one** index snapshot from the step's input
and then chains seven rules through a growing accumulator. The first
rule sees `ig.ig_triples == g`; the sixth does not. A per-rule theorem
phrased over a single graph therefore does not compose. The fix is
`licensed_by2 r src seed out` — source graph (where premises are read)
decoupled from seed graph (what the rule was handed):

```fstar
let licensed_by2 (r : list triple -> triple -> prop) (src seed acc : list triple) : prop =
  forall (t : triple). memP t acc ==> (memP t seed \/ r src t)
```

and, for the three rules that read one premise from the accumulator and
one from the snapshot (rdfs9, rdfs11, rdfs5), a two-source form of the
derivation relation (`rdfs9_derives2 gd gs`), with the W3C table's
single-graph form as its diagonal. **Generalise for the snapshot before
writing the per-rule proof, not after.**

## 3. The index hypothesis, and how a headline theorem nearly became vacuous

`ig_wf_sp (build_indexed g)` — "the composite-key bucket serves up only
triples with that exact subject and predicate" — is not provable. It
needs `sp_key` injectivity, which needs "U+001F never occurs in a
blank-node label", which nothing in the tree enforces. That is the OWL
pilot's finding F1, inherited unchanged, because rdfs9 / rdfs11 / rdfs5
are the index-driven rules.

The first draft of `rdfs_closure_sound` assumed it for **every** graph:

```fstar
(requires ... /\ (forall (h : rdf_graph). ig_wf_sp (build_indexed h)))
```

That hypothesis is **false** — a blank-node label containing U+001F
makes it so — and the theorem was therefore vacuous. It verified
cleanly. ⚠️ A universally quantified index hypothesis is a vacuity
hazard, and F\* will not warn you.

The landed form scopes it to the graphs the driver actually indexes:

```fstar
let rec closure_iter (g : rdf_graph) (n : nat) : Tot rdf_graph (decreases n) =
  if n = 0 then g else closure_iter (rdfs_closure_step g) (n - 1)
let closure_chain_wf (g : rdf_graph) : prop =
  forall (n : nat). ig_wf_sp (build_indexed (closure_iter g n))
```

Satisfiable, and satisfied by every graph with clean labels, because
closure rules never mint blank-node labels. The recursion needs one
shift lemma (`closure_iter (step g) n == closure_iter g (n+1)`, which
is definitional).

**Rule for the next vertical: before shipping a theorem whose
hypothesis is a `forall` over an unproven predicate, ask whether the
predicate is actually true of everything. If not, the theorem is
vacuous, however green the checkmark.**

⚠️ **Follow-up, 2026-07-30.** The landed `closure_chain_wf` form is
satisfiable, but the satisfiability pass could not discharge it for a
**single graph, including the empty one** — `rdfs_rule_container_membership`
emits ten rows with no premise, so the chain leaves `[]` at n = 1 and
runs into `sp_key` non-injectivity. `rdfs_closure_sound` and
`rdfs_closure_entails` are therefore not vacuous but have no
machine-checked instance. The root cause is also wider than finding F1
records: `sp_key` is non-injective on **IRI subjects alone**, because
`is_iri` admits U+001F. Tracked as
[#338](https://github.com/danbri/factoidal/issues/338); see
[`2026-07-30-hypothesis-satisfiability.md`](2026-07-30-hypothesis-satisfiability.md).

## 4. Findings

### RS-1 — `rdfs_reflexivity_axioms` is unsound at the RDFS rung

See §0. Machine-checked.

### RS-2 — six rule rows have no implementation

`rdfs1`, `rdfs4a`, `rdfs4b`, `rdfs8`, `rdfs13` and `rdfD1` are not
implemented anywhere in the tree, and the axiomatic triples are not
seeded (the seeding attempt was made and reverted; the measured
regression is recorded in `RDFS.Closure.fsti`). Incompleteness, not
unsoundness. It is why no unrestricted completeness theorem about the
shipping closure can be true — see §6.

The finite `rdf:_1 … rdf:_5` slice of the infinite `rdf:_n` family is
the same kind of gap.

### RS-3 — `rdfs_rule_range` drops literal objects, exactly as the spec forces

`rdfs3`'s conclusion moves the object into subject position. RDF 1.1
Semantics states the rules over **generalized RDF**, where a literal
may be a subject; `RDF.Term.subject` is IRI-or-bnode only, so the
conclusion is unbuildable and the rule does not fire. The declarative
`rdfs3_derives` carries the same premise, so the refinement is **exact**
— the incompleteness is in the tree's term algebra, not in the proof.
Same for `rdfs4b`, and for the `yyy` position of `rdfs5` / `rdfs11`.

### RS-4 — the rdf12 manifests' "RDFS" regime runs none of rdfs1–rdfs13

`RDF.Entailment.Regime.fst` opens `RDF.Graph.Executable` (which
`include`s `RDFS.Closure`) and then defines its **own** one-argument
`rdfs_closure`, shadowing the two-argument RDFS rule driver:

```fstar
// RDF.Entailment.Regime.fst
let rdfs_closure (ts : list triple) : list triple =
  ts @ collect reifies_prop_triples ts        // rdf:reifies range only
let entails_rdfs (a b : list triple) : bool =
  entails_with dt_value_leq bnd_rdf (rdfs_closure a) b
```

`bin/w3c-runner/w3c_runner.ml` (≈ line 3152) dispatches
`"RDFS" -> RDF_Entailment_Regime.entails_rdfs` for
`PositiveEntailmentTest` / `NegativeEntailmentTest`. So on that path
"RDFS entailment" means one rule: `X rdf:reifies Y ⊢ Y rdf:type
rdfs:Proposition`.

The **other** path — `apply_entailment_regime` (≈ line 2442) and the
SPARQL entailment-regime closure (≈ line 1128) — does reach
`RDFS.Closure`, i.e. the functions this vertical proves about. So the
theorems here do cover running code; they cover the SPARQL-entailment
and rdf-mt paths, not the rdf12-entailment path.

Nothing is proven about the shadowed function because there is nothing
RDFS-shaped in it. 🧭 The naming is the hazard: two functions called
`rdfs_closure`, one of which is not an RDFS closure.

### RS-5 — the "RDF" regime runs the RDFS rule set

```fstar
// OWL.Closure.fsti, entailment_closure
else if regime = regime_rdf then rdfs_closure g fuel
```

and, in the runner, `"RDF" -> rdfs_closure_with_reflexivity … then
rdf_property_axiom_closure`. Both apply rdfs2 / rdfs3 / rdfs5 / rdfs7 /
rdfs9 / rdfs11 under the **RDF** regime.

This vertical makes the mismatch precise rather than rhetorical: each
row's soundness lemma names exactly the condition it needs, and
`rdfs9_true` needs `cond_subClassOf`, which is a §9 (RDFS) condition
and is **not** in `rdf_conditions`. An RDF interpretation may read
`rdfs:subClassOf` as an arbitrary property. Adding RDFS consequences to
the antecedent of an RDF-regime entailment check makes it accept
non-RDF-entailments — one-directional, like RS-1.

Not machine-checked as a non-entailment (that needs a constructed
countermodel; see §6). The evidence is the hypothesis list of
`rdfs9_true`, which **is** machine-checked.

## 5. Baseline pinning and the delta table

**Primary baseline: RDF 1.1 Semantics, W3C Rec 25 February 2014**
(`https://www.w3.org/TR/rdf11-mt/`) — §8 (RDF interpretations, the RDF
axiomatic triples, rules rdfD1/rdfD2), §9 (RDFS interpretations, the
RDFS axiomatic triples, rules rdfs1–rdfs13).

**Cross-checked against Hayes, RDF Semantics, W3C Rec 10 February
2004** (`REC-rdf-mt-20040210`) §3 and §4 — the baseline the normative
OWL 2 (2012) specifications build on.

| # | Divergence | RDF 2004 | RDF 1.1 (2014) | Handling here |
|---|---|---|---|---|
| D1 | Literal structure | plain literals (± language tag) and typed literals are two abstract-syntax shapes | one shape; every literal carries a datatype IRI, `rdf:langString` for language-tagged strings (Concepts §3.3) | `RDF.Term.literal` is the 1.1 shape; specs written against 1.1, the 2004 reading recovered by reading a plain literal as `xsd:string` / `rdf:langString` |
| D2 | `rdf:XMLLiteral` | a **required** recognized datatype of every rdf-interpretation (§3.1) | **non-normative** (Concepts §5.3); recognizing it is optional | ⚠️ **Contrast with the simple rung.** XMLLiteral canonicalisation in `literal_eq` is *unlicensed* at the simple rung (finding SE-1) but **licensed at the RDF rung** under the 2004 baseline, and under 1.1 for an interpretation recognizing it. Same code, different verdict per rung. `datatype_set` is a parameter here precisely so this is stateable |
| D3 | Language-tag case | abstract-syntax tag normalized to lower case (Concepts §6.5), so `@EN` does not occur | tag kept verbatim in the term; the *value* of a language-tagged string uses the lowercased tag (§8's `IL` condition) | Same contrast as D2: case-insensitive matching is an RDF-rung (D-entailment) behaviour, not a simple-rung one. Confirms SE-1's diagnosis from above |
| D4 | IRIs vs URI references | "URI reference" | "IRI" | No semantic content; `wf_iri` covers both |
| D5 | Generalized RDF | rules carry explicit "is a URIref or bnode" side conditions | rules stated over generalized RDF, with a note that closures may leave ordinary syntax | Every affected rule carries an explicit subject-recovery premise; finding RS-3 |
| D6 | RDF 1.2 triple terms | absent | absent | Handled syntactically; **quarantined** from the model theory by reusing the simple rung's `graph_tt_free` |
| D7 | `rdfs1` | "uuu aaa lll (lll a plain literal) ⊢ uuu aaa _:nnn . _:nnn rdf:type rdfs:Literal" — bnode-minting | "any IRI aaa in D ⊢ aaa rdf:type rdfs:Datatype" | **Two different rules under one number.** The 1.1 reading is `rdfs1_derives`; the 2004 reading is kept as `rdfs1_2004_derives` so the divergence is explicit |
| D8 | `rdfs4a` / `rdfs4b` | the only route to `rdfs:Resource` membership | the condition ICEXT(I(rdfs:Resource)) = IR does the same work | No delta in the rule; presentational delta in the condition. `cond_resource` is stated |
| D9 | `rdfs6` / `rdfs10` | rules **and** conditions | rules **and** conditions | The tree implements a harvesting approximation (`rdfs_reflexivity_axioms`) wider than either rule licenses — finding RS-1 |

## 6. Completeness: attempted, not landed, and here is exactly what blocks it

The brief expected completeness to be reachable, citing Muñoz, Pérez &
Gutiérrez ("Simple and Efficient Minimal RDFS", *J. Web Semantics* 7(3)
2009; ESWC 2007), whose theorem is that six rules are sound **and
complete** for RDFS entailment restricted to the **rho-df** fragment —
the sub-vocabulary {`rdfs:subPropertyOf`, `rdfs:subClassOf`,
`rdfs:domain`, `rdfs:range`, `rdf:type`}. Those six rules are, triple
for triple, rdfs5 / rdfs7 / rdfs11 / rdfs9 / rdfs2 / rdfs3 — **exactly
the shipping rule set**. That coincidence is real and is why the
fragment is named as a first-class predicate (`rho_df_graph`,
`rho_df_triple`, `is_rho_df_iri`) in the Spec module.

It did not land. Three separate obligations block it, and none is
proof-engineering slack:

1. **The converse of the licence theorems is not proved.** Soundness
   says "everything emitted is derivable"; completeness needs
   "everything derivable is emitted". That requires an index property
   the tree does not have a lemma for: `ig_wf_pred` says every triple
   the bucket *serves* has that predicate; completeness needs every
   triple of the graph *with* that predicate to be *in* the bucket.
   `OWL.Semantics.MemLemmas` proves only the soundness direction
   (`lemma_build_indexed_wf_pred`). A `lemma_build_indexed_complete_pred`
   is the missing first step, and it is not hard — `build_bucket`'s
   group-by walk visits every element.
2. **The fixed point must be shown to be reached.** `rdfs_closure` is
   fuel-bounded and returns early on `graph_len g' = graph_len g`.
   Completeness needs "at the returned graph, no rule derives anything
   new", which needs both a sufficient-fuel argument and the fact that
   the length test is a faithful fixed-point test — it is not, since
   `rdfs_closure_step` ends in `graph_dedup_sort` and the comparison is
   on **length**, so a step that adds a triple and removes a duplicate
   would compare equal. That is a second finding waiting to be made
   precise.
3. **The canonical model.** The rho-df completeness proof exhibits an
   interpretation built from the closure. `OWL.Semantics.interp` is the
   OWL pilot's **superset** class; for soundness the inclusion runs the
   right way (and every theorem above is thereby stronger), for
   completeness it runs the wrong way. Transferring a countermodel to
   the genuine RDFS class is the pilot's phase-2 embedding obligation —
   the same one the simple rung recorded, now with a third customer.

Obligation 1 is a commit. Obligation 2 is a commit plus a finding.
Obligation 3 is shared with the whole programme. Sequenced that way,
rho-df completeness is two commits away, and this note's estimate is
that it lands.

Note also that unrestricted completeness of the shipping closure is
**false**, not merely unproven: RS-2's six missing rules and the
unseeded axiomatic triples each break it. Any completeness claim must
name a fragment.

## 7. What is not proved

* **Completeness.** §6.
* **`rdfs_closure_with_reflexivity`.** Deliberately absent — RS-1.
* **The genuine RDFS-interpretation class.** `interp` is the pilot's
  superset. Soundness is thereby stronger; completeness would need the
  embedding.
* **`ig_wf_sp`.** Explicit hypothesis wherever the index-driven rules
  appear (rdfs9 / rdfs11 / rdfs5). Pilot finding F1; not this
  vertical's to discharge.
* **RS-5 as a non-entailment.** Argued from the hypothesis lists, not
  from a constructed countermodel.
* **The parsers.** Untouched at these rungs; the simple rung's
  `Boundary` module has no analogue here because RDF/RDFS entailment
  adds no new parser surface.

## 8. The pattern, second application

### 8.1 What transferred unchanged

* **Four-module split** (`Spec` / `Refinement` / `ModelTheory`, plus
  `Boundary` where there is a parser surface). Held. The `Spec`
  modules open nothing from the engine, so "the spec is independent of
  the algorithm" stayed a *checkable* claim.
* **State the spec relationally** (§7.2 of the predecessor). Held, and
  paid off again: the generalized-RDF cases (D5) fail to relate instead
  of needing an `option`.
* **Hunt for the fragment hypothesis, then witness its necessity**
  (§7.7). Held — RS-1 is the witness, and it is *hypothesis-free*,
  which is stronger than the simple rung's SE-1 witness.
* **Prove at the parameterised level** (§7.6). Held in a new form: the
  recognized-datatype set `D` is a parameter (`datatype_set`), exactly
  as the W3C text parameterises "RDFS entailment recognizing D". That
  is what lets delta D2's XMLLiteral question be *stated*.
* **Reuse `OWL.Semantics`** rather than starting a second framework.
  Held. `cond_domain` / `cond_range` were already there with a
  refinement theorem for rdfs2; this vertical grew the condition table
  around them.

### 8.2 What needed new machinery

* **The snapshot/seed split** (§2). New. Any rule pipeline that builds
  an index once and chains rules needs it, and needs it in the
  *statement*, not the proof.
* **The vacuity check on index hypotheses** (§3). New, and the most
  transferable lesson here.
* **A new F\* trap: an inner lambda closing over a PATTERN-BOUND
  variable.** The `fold_left_inv` pattern discharges six of the seven
  rules directly. It fails on rdfs7, whose emission lambda closes over
  `q`, bound by the rule's own `match decl.s, decl.o with | S_IRI p,
  T_IRI q ->`. The proof's copy of that lambda and the one inside the
  shipping function get **unrelated closure symbols** in the SMT
  encoding — the OWL pilot's finding F3 in higher-order form. The
  predecessor's `unfold let` answer (§7.5) does **not** apply, because
  the lambda is inside a match arm rather than an argument of the
  shipping call. Minimal reproduction and fix were established
  separately; the working recipe is:

  > rebuild the scrutinee as a **record literal** so the match
  > iota-reduces, `assert_norm` the reduced form, then transport along
  > the equality by congruence. Both steps are needed: the record
  > literal alone does not make the SMT query go through, and
  > `assert_norm` alone cannot see that `decl.s` is `S_IRI p`.

  Diagnostic that isolates it in one minute: check whether the inner
  lambda's free variables are all bound *outside* the shipping
  function's own `match`. If any is pattern-bound, expect this.
* **Fuel for list-literal membership.** `memP cmp
  container_membership_properties` needs five cons unfoldings; default
  fuel is 2. `--fuel 8` plus an `assert_norm` of the list literal.

### 8.3 Cost

Measured, this session, on warm `.checked` dependencies:

| Module | Lines | Single-module verify |
|---|---|---|
| `RDF.Spec` | 209 | < 1 s |
| `RDFS.Spec` | 380 | 1 s |
| `RDFS.Refinement` | 788 | 36 s |
| `RDFS.ModelTheory` | 724 | 13 s |

As at the simple rung, the dominant cost was **deciding what the
specification should say** — here, which of the two `rdfs1` rules to
transcribe (D7), and whether the OWL typing IRIs in `collect_classes`
were licensed (RS-1). Both are spec-reading problems. The proofs that
took longest (rdfs7, the container rule) took long for
proof-engineering reasons that are now written down.

## 9. Follow-ups

* 🔴 Split `collect_classes` / `collect_properties` by regime (RS-1) —
  the only shipping-code change this vertical asks for.
* 🧭 Rename `RDF.Entailment.Regime.rdfs_closure` (RS-4). Two functions
  with that name, one of which is not an RDFS closure, is a trap for
  the next reader.
* Decide what the `"RDF"` regime should run (RS-5) — plausibly
  `rdf_property_axiom_closure` alone, with the RDFS rules removed.
* `lemma_build_indexed_complete_pred` (§6 obligation 1) — the
  completeness direction of the index.
* The `graph_len` fixed-point test in `rdfs_closure` (§6 obligation 2)
  — confirm or refute that a step can add and dedup to the same length.
* rho-df completeness, once 1 and 2 land.
* Implement the missing rows (RS-2), starting with rdfs4a/4b/rdfs8/
  rdfs13, which need no bnode minting.
* The genuine-interpretation embedding — shared with the OWL programme
  and the simple rung.
