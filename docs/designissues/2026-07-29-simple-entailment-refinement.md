# RDF simple entailment: a completed semantic-refinement vertical

Status: LANDED 2026-07-29. Sound, complete, model-theoretically
grounded, parser boundary stated. No admits, no `--lax`, z3 4.13.3.

Issue: [#318](https://github.com/danbri/factoidal/issues/318) — gate 5
of the external-review epic
[#313](https://github.com/danbri/factoidal/issues/313). The review
picked this vertical itself:

> "One completed semantic-refinement vertical: RDF simple entailment is
> an appropriate first candidate. Define the declarative relation
> independently, prove the executable search sound and complete, and
> prove the parser-to-abstract-graph boundary. That would establish a
> reusable pattern before attempting the larger RDF/OWL programme."

and named the defect precisely:

> "There is no separate declarative homomorphism relation followed by
> theorems … The comments describe the algorithm as the semantics, and
> F\* proves that the algorithm is total. That does not independently
> establish that the implementation exactly captures Hayes' definition."

## 1. What landed

| Module | Role | Status |
|---|---|---|
| `formal/fstar/RDF.Entailment.Simple.Spec.fst` | The declarative specification, transcribed from spec text, mentioning no function of the engine | ✅ verified |
| `formal/fstar/RDF.Entailment.Simple.Refinement.fst` | Soundness + completeness of the shipping search; the unsoundness witness | ✅ verified |
| `formal/fstar/RDF.Entailment.Simple.ModelTheory.fst` | The interpolation lemma — syntactic characterisation ⟺ model theory — on the pilot's `OWL.Semantics` machinery | ✅ verified |
| `formal/fstar/RDF.Entailment.Simple.Boundary.fst` | Blank-node label independence + the document-level composition theorem | ✅ verified |
| `formal/fstar/build-ocaml.sh` | four `ALL_MODULES` entries (whole-tree verification vehicle) | ✅ |

Zero change to any shipping module. `RDF.Entailment.Simple.fst` is
untouched — unlike the OWL pilot, no lambda-lifting was needed, because
`entails_with`'s matchers are already top-level named functions with
their predicate arguments passed as plain values.

### The theorems, by name and statement

Verify-only proof layer; every theorem names a **shipping** function.

```fstar
// RDF.Entailment.Simple.Refinement.fst

val simple_entails_complete (a b : list triple)
  : Lemma (requires simple_entailment_spec a b)
          (ensures  simple_entails a b == true)

val simple_entails_sound (a b : list triple)
  : Lemma (requires simple_entails a b == true /\ graph_exact a /\ graph_exact b)
          (ensures  simple_entailment_spec a b)

val simple_entails_iff_spec (a b : list triple)
  : Lemma (requires graph_exact a /\ graph_exact b)
          (ensures  (simple_entails a b == true) <==> simple_entailment_spec a b)

val simple_entails_not_sound_unconditionally
      (s p : wf_iri) (tag1 tag2 : string)
  : Lemma (requires String.lowercase tag1 == String.lowercase tag2 /\ tag1 =!= tag2)
          (ensures  simple_entails ga gb == true /\ ~(simple_entailment_spec ga gb))

// the same refinement at the PARAMETERIZED engine
val entails_with_complete (leq) (bnd) (a b : list triple)
  : Lemma (requires leq_reflexive leq /\ bnd_total bnd /\ simple_entailment_spec a b)
          (ensures  entails_with leq bnd a b == true)

val entails_with_sound (leq) (bnd) (a b : list triple)
  : Lemma (requires leq_exact_identity leq /\ graph_exact a /\ graph_exact b /\
                    entails_with leq bnd a b == true)
          (ensures  simple_entailment_spec a b)
```

```fstar
// RDF.Entailment.Simple.ModelTheory.fst

val interpolation_sound (a b : list triple)          // all graphs
  : Lemma (requires simple_entailment_spec a b) (ensures simple_entails_mt a b)

val interpolation_complete (a b : list triple)       // triple-term-free
  : Lemma (requires simple_entails_mt a b /\ graph_tt_free a /\ graph_tt_free b)
          (ensures  simple_entailment_spec a b)

val interpolation_lemma (a b : list triple)
  : Lemma (requires graph_tt_free a /\ graph_tt_free b)
          (ensures  simple_entailment_spec a b <==> simple_entails_mt a b)

val simple_entails_iff_model_theory (a b : list triple)
  : Lemma (requires graph_exact a /\ graph_exact b /\
                    graph_tt_free a /\ graph_tt_free b)
          (ensures  (simple_entails a b == true) <==> simple_entails_mt a b)
```

```fstar
// RDF.Entailment.Simple.Boundary.fst

val spec_rename_specialises (f : bnode_id -> bnode_id) (a b : list triple)
  : Lemma (requires simple_entailment_spec a (rename_graph f b))
          (ensures  simple_entailment_spec a b)          // no injectivity needed

val spec_rename_generalises (r : relabelling) (a b : list triple)
  : Lemma (requires simple_entailment_spec a b)
          (ensures  simple_entailment_spec a (rename_graph r.rl_fwd b))

val simple_entails_rename_invariant (r : relabelling) (a b : list triple)
  : Lemma (requires graph_exact a /\ graph_exact b)
          (ensures  simple_entails a b == simple_entails a (rename_graph r.rl_fwd b))

val entails_ntriples_boundary (doc_a doc_b : string) (ga gb : list triple)
  : Lemma (requires parse_ntriples_strict doc_a == Some ga /\
                    parse_ntriples_strict doc_b == Some gb /\
                    graph_exact ga /\ graph_exact gb)
          (ensures  (entails_ntriples_documents doc_a doc_b == Some true) <==>
                    simple_entailment_spec ga gb)
```

`simple_entails_mt a b` is `forall (i : interp). satisfies i a ==> satisfies i b` —
RDF 1.1 Semantics §5.2's definition, on `OWL.Semantics`' interpretations.

## 2. Completeness landed — and here is why it was reachable

Completeness is the half the OWL programme explicitly surrendered
(design doc `2026-07-29-rdf-based-semantics-formalization.md` §8.1:
"Chose the superset class … Revisit only if completeness … becomes a
goal"). It landed here, **unconditionally**, for three reasons that a
future vertical should check for before promising completeness:

1. **The specification is a finite syntactic condition.** The
   interpolation lemma converts the ∀-over-all-interpretations
   definition into ∃-a-substitution. Nothing has to be decided about an
   infinite domain.
2. **The algorithm is an exhaustive search over that same finite
   space.** Completeness is then a search-doesn't-miss argument, not a
   model construction.
3. **The engine's literal test is *coarser* than the spec's, never
   finer.** A coarser test accepts everything the spec demands. Had it
   been finer in any place, completeness would have needed the same
   fragment hypothesis soundness needs.

The proof shape is one invariant plus two mutually recursive lemmas
mirroring the two mutually recursive search functions:

> **`binding_compat m bd`** — the partial binding built so far never
> contradicts the specification's witnessing substitution `M`.

Under that invariant the "right" candidate (the `M`-image of the
current pattern triple) always matches, so the alternatives loop cannot
exhaust before reaching it. `lemma_try_alts_complete` case-splits the
`memP` of the right candidate into head/tail and, in the tail case,
uses that **every** branch of `try_alts` falls back to
`try_alts … more` — so the recursive call's `true` propagates
regardless of what the head candidate does. That is the whole
backtracking argument, in four lines of F\*.

The lemmas carry the same lexicographic measure as the code
(`%[length bs; length cand]` / `%[length bs; 1 + length a]`) — copying
the shipping measure verbatim is what makes the mutual recursion
accepted without any new termination reasoning.

## 3. Soundness landed with a side condition — and the side condition is real

`simple_entails_sound` requires `graph_exact` on both graphs. That is
not proof-engineering slack; the unconditional statement is **false**,
and `simple_entails_not_sound_unconditionally` is the machine-checked
witness.

### Finding SE-1 — `literal_eq` is coarser than RDF literal term equality

`RDF.Term.literal_eq` diverges from term equality in exactly two
places, both of which make the engine accept non-entailments:

| Divergence | What `literal_eq` does | What simple entailment says |
|---|---|---|
| Language tag case | `lang_tag_eq t1 t2 = lowercase t1 = lowercase t2` — `"x"@en` matches `"x"@EN` | RDF 1.1 Concepts §3.3: literal term equality is "character by character"; the two are different terms with the same value. Value equality of language-tagged strings is an **RDF-interpretation** condition, not a simple one |
| `rdf:XMLLiteral` | two XMLLiteral-typed literals compare by exclusive canonical XML | RDF 2004 Semantics §3.1 puts the XMLLiteral value space on **rdf-interpretations**; RDF 1.1 Concepts §5.3 (where XMLLiteral lives) is marked **non-normative** |

Both are D-entailment behaviours leaking into the simple-regime
matcher. Neither is licensed by simple entailment under either
baseline.

**Practical impact: none observed.** The divergence is one-directional
(accepts more), so no test expecting entailment can fail because of it,
and the RDF 1.2 entailment suite carries no language-tag-case or
XMLLiteral negative fixture. **This is not a bug report, it is a claim
boundary**: the honest description of `simple_entails` today is "a
homomorphism search whose literal test is D-flavoured", and
`graph_exact` names the fragment where that stops mattering.

**Fix, if wanted:** `entails_with` is already parameterized by the
literal test. Passing strict term identity for the simple regime and
keeping `literal_eq` for the D-regime removes the side condition
outright, with no structural change. Not done here: it is a behaviour
change to a shipping function, outside this issue.

### Finding SE-2 — the side condition is reachable from concrete syntax

`Parser.NTriples.parse_ntriples_strict` copies a literal's language tag
and datatype IRI out of the document verbatim. It does **not**
lowercase language tags. So a legal N-Triples document can produce a
graph outside `graph_exact`, and SE-1's divergence is live end-to-end,
not merely constructible in F\*.

RDF 1.1 Concepts §3.3 explicitly permits normalising at parse time
("Lexical representations of language tags **MAY** be converted to
lower case"); RDF 2004 Concepts §6.5 **required** it ("normalized to
lowercase"). Doing it in the parser would discharge half of
`graph_exact` for every parsed graph, for free. Also a behaviour
change, also out of scope here — filed as a follow-up.

### Finding SE-3 — no W3C suite currently runs `simple_entails`

The review's target function is not on any test path.
`bin/w3c-runner/w3c_runner.ml` dispatches entailment tests two ways:

* rdf12 / rdf-mt entailment manifests (line ~3174) →
  `RDF_Entailment_Regime.entails_rdf` for **every** regime including
  `"simple"` — i.e. `entails_with dt_value_leq bnd_rdf`, not
  `simple_entails`;
* the older `PositiveEntailmentTest` path (line ~2800) → a
  **hand-written OCaml** `simple_entails_regime` in the runner itself,
  a pre-existing rule #15 duplicate of the F\* logic.

So "the RDF 1.2 entailment tests support it", which the review offered
as the current evidence for `simple_entails`, is not even true of that
function. This does **not** weaken the theorems (they are about the
function the module exports), but it means the vertical's *coverage* of
running code comes from `entails_with_sound` / `entails_with_complete`
— stated at the parameterized engine, which every regime does use —
rather than from the `simple_entails` corollaries. Discharging
`leq_reflexive dt_value_leq` and `bnd_total bnd_rdf` for the regime
instantiations is the obvious next commit; note in advance that
**neither hypothesis holds as stated**: `bnd_rdf` deliberately refuses
malformed recognized-datatype literals, and `dt_value_leq` routes
`xsd:double` through IEEE-754 equality, where `NaN` is not reflexive.
Both will need explicit fragment hypotheses of their own.

## 4. What is proved about the parser boundary, exactly

**Not** proved: that `parse_ntriples_strict` implements the N-Triples
grammar. That needs a declarative grammar semantics ("document D
denotes graph G") which this tree does not have. The boundary module
says so in its banner and does not pretend otherwise.

Proved, in two parts:

1. **Composition** (`entails_ntriples_boundary`). The whole
   document-in/verdict-out path equals the declarative relation on
   whatever graphs the parser produced. This isolates the parser as the
   single remaining unproven link and names it.
2. **Label independence** (`simple_entails_rename_invariant`) — the
   part with content. A parser's abstract graph is determined only up
   to its choice of blank-node labels (RDF 1.1 Concepts §3.4: "blank
   node identifiers are local to a concrete syntax or implementation").
   If the verdict could depend on those labels, no theorem about
   abstract graphs would transfer to documents at all. It cannot:
   relabelling the entailed graph by any **injective** map leaves
   `simple_entails` unchanged.

   Injectivity is load-bearing and the asymmetry is proved, not
   assumed: `spec_rename_specialises` (arbitrary map — merging blank
   nodes only makes the pattern harder) needs no inverse, while
   `spec_rename_generalises` does. A `relabelling` carries its own left
   inverse rather than an injectivity hypothesis, so the transported
   substitution is constructed explicitly and no choice principle is
   needed.

## 5. Baseline pinning

Per the pilot's phase-2 obligation, restated for this vertical.

**Primary baseline: RDF 1.1 Semantics, W3C Rec 25 February 2014**
(`https://www.w3.org/TR/rdf11-mt/`) — §4 (instance), §5 (simple
interpretations), §5.2 (simple entailment), §5.3 (interpolation
lemma). Cross-checked against **Hayes, RDF Semantics, W3C Rec 10
February 2004** (`REC-rdf-mt-20040210`) §0.3 and §2, the baseline the
2012 OWL 2 specifications normatively build on.

The two texts agree on every definition this vertical transcribes, up
to the rename of "URI reference" to "IRI". Simple entailment is the
stable part across baselines, as expected. The three places the
versions would diverge, and how each is handled:

| Divergence | RDF 2004 | RDF 1.1 (2014) | Handling here |
|---|---|---|---|
| Language tag case | abstract syntax tag is "normalized to lowercase" (Concepts §6.5), so `@EN` is not well-formed | term equality is character-by-character; `@EN` is legal and distinct from `@en` (Concepts §3.3) | Spec uses term identity — correct under **both**. Divergence is in the engine, not the baselines: finding SE-1 |
| `rdf:XMLLiteral` | value space is an **rdf-interpretation** condition (§3.1), not a simple one | datatype is **non-normative** (Concepts §5.3) | Spec uses term identity — correct under both. Finding SE-1 |
| RDF 1.2 triple terms | absent | absent | Handled by the **syntactic** spec and refinement (the engine handles them, so the spec must be able to talk about the same graphs); **quarantined** from the model-theoretic surface by an explicit `graph_tt_free` hypothesis |

## 6. What is not proved

Stated plainly so no later document has to reconstruct it.

* **The parser.** See §4. The largest remaining gap in this vertical.
* **`instance_subgraph_form ==> simple_entailment_spec` only.** The
  spec text's own shape ("a subgraph of A is an **instance** of B",
  naming the intermediate instance graph) is defined in the Spec module
  and proved to **imply** the collapsed relational form
  (`lemma_spec_is_instance_subgraph`), which is the direction that
  shows the collapsed form is not *stronger* than the text. The
  converse needs a choice-based construction of the image graph
  (`FStar.IndefiniteDescription` inside a ghost fold over B) and was
  not built. Cheap follow-up; nothing depends on it.
* **The genuine-simple-interpretation class.** `interpolation_complete`
  quantifies over `OWL.Semantics.interp`, the pilot's **superset**
  class. For the easy direction the inclusion runs the right way and
  the theorem is thereby stronger. For the hard direction it runs the
  wrong way, so transferring it to the W3C class needs `herbrand a` to
  be a genuine simple interpretation — which it is, by a ten-line
  argument about the W3C text recorded in the module banner, but that
  argument is not machine-checked. It is the pilot's phase-2
  embedding obligation, unchanged and now with a concrete second
  customer.
* **Triple terms in the model theory.** Quarantined; `graph_tt_free`
  on both graphs for `interpolation_complete`. The Herbrand
  construction cannot reconstruct a triple term from an arbitrary
  assignment's images, because a blank node may be assigned a literal,
  which is not a legal triple-term subject. A real restriction, not a
  formality.
* **The regime instantiations.** See finding SE-3.

## 7. The reusable pattern

What a next vertical should copy. Ordered by how much time each step
saved or cost here.

### 7.1 Four modules, not one

`Spec` (no engine names) → `Refinement` (engine names, no model theory)
→ `ModelTheory` (model theory, no engine) → `Boundary` (composition).
The separation is what makes "the spec is independent of the algorithm"
a *checkable* claim rather than an assertion: `Spec.fst` does not
`open` the engine module, so a reader can diff it against the W3C text
alone. Keep it that way even when it costs a bridging lemma
(`lemma_subj_terms_agree` here — nine lines to relate two spellings of
"a subject viewed as a term" rather than share one).

### 7.2 State the spec RELATIONALLY when the syntax is partial

The spec text applies a substitution to a graph and gets a graph. In
F\* that is not total: a triple's subject cannot be a literal, so
"replace blank node b by literal L" has no result when b is a subject.
Making substitution `option`-valued infects every later statement with
a `Some`. Writing the instance condition as a **relation** between a
pattern triple and a ground triple makes the ill-typed cases simply
fail to relate — which is the intended reading — and keeps every
downstream statement clean. State the spec-text shape separately
(`instance_subgraph_form`) and prove the collapse, so the presentation
choice is checked rather than argued.

### 7.3 The soundness statement needs the extension-stability conjunct

The single most important shape decision. A search that threads a
growing binding cannot have per-step lemmas of the form "the match
produces a binding explaining this triple", because the substitution
that finally explains everything is read off the **final** binding,
built long after that step. The statement that makes the induction go
through is:

```fstar
(ensures (let bd1 = Some?.v (match_… bd pat g) in
          binding_extends bd1 bd /\ binding_exact bd1 /\
          (forall (bd2 : binding). binding_extends bd2 bd1 ==>
             term_inst (bsubst bd2) pat g)))
```

— the ∀-over-later-extensions conjunct. With it, every match lemma is
provable in isolation and the top-level chaining is three `assert`s.
Without it there is no correct per-step statement at all. Expect to
need the analogous conjunct in any search-with-accumulator refinement.

### 7.4 Mirror the code's control flow AND its termination measure

Each proof lemma is written as a `match` over the same scrutinee the
shipping function matches on, with the same lexicographic `decreases`.
F\* then relates the lemma's case analysis to the function's unfolding
without any normalisation hints. Zero `assert_norm` was needed in the
recursion.

### 7.5 `unfold let` for the shipping instantiation's lambda arguments

`simple_entails` passes inline lambdas to `entails_with`. Naming them
with a plain `let` and trying to pin the connection with `assert_norm`
**fails** (the OWL pilot's finding F3, same trap): the SMT encoding
gives the named symbol and the inline lambda unrelated closure symbols.
Declaring the copies `unfold let` makes them melt away at
typechecking and the connection becomes definitional —

```fstar
unfold let simple_leq : bool -> literal -> literal -> bool = fun _ l m -> literal_eq l m
unfold let simple_bnd : rdf_term -> bool = fun _ -> true
let lemma_simple_entails_unfold (a b : list triple)
  : Lemma (simple_entails a b == try_match simple_leq simple_bnd b [] a) = ()
```

This is a **cheaper** answer to F3 than the pilot's lambda-lift refactor
whenever the lambdas are function *arguments* rather than emission
lambdas under match binders. Try `unfold` first; refactor only if the
lambda is buried in a `match` arm.

### 7.6 Prove the spec at the PARAMETERIZED function, instantiate after

Every core lemma here is stated over `leq` / `bnd` with the three
hypotheses `leq_reflexive` / `leq_exact_identity` / `bnd_total`, and
the `simple_entails` theorems are one-line instantiations. That is what
lets finding SE-3 be a follow-up commit rather than a rewrite: the
regime instantiations inherit the whole development by discharging
three hypotheses. **Look for the shipping function's parameterization
and prove at that level.** It costs nothing and multiplies the result.

### 7.7 Hunt for the fragment hypothesis, then WITNESS its necessity

When soundness needs a side condition, the reflex is to widen the proof
until it goes away. Better: pin down the exact fragment
(`lit_exact` / `graph_exact` here), then prove that the unconditional
statement is **false** with an explicit witness lemma. That converts an
apparent proof weakness into a finding with a fix, and stops a later
session from burning a day trying to remove a condition that cannot be
removed.

Making the witness provable is worth a moment's design: here,
`String.lowercase` does not reduce on string constants under
`assert_norm`, so the counterexample is stated with the tag pair as a
**hypothesis** (`lowercase t1 == lowercase t2 /\ t1 =!= t2`) rather
than at literal strings. That keeps it fully machine-checked while
sidestepping a primitive the normaliser will not evaluate.

### 7.8 Prove the "obvious" bridge lemma instead of citing it

The interpolation lemma is textbook, appears in the spec as an
informative section, and would have been entirely reasonable to cite.
Proving it cost about eighty lines (the Herbrand model is ten of them)
and it is what turns "the search matches the syntactic characterisation"
into "the search decides the model-theoretic definition". For any
vertical where the spec offers a syntactic characterisation of a
semantic notion, **that bridge is the deliverable**, not a preliminary.

### 7.9 The label-independence theorem is the cheap parser boundary

A full grammar semantics is out of reach for a single vertical. The
substantive property that is in reach — and that is actually what a
"parser boundary" needs to mean for anything blank-node-shaped — is
that the verdict does not depend on the parser's arbitrary label
choices. It costs one substitution-composition lemma
(`term_inst (m o f) pat g <==> term_inst m (rename f pat) g`), which
needs no injectivity, plus a `relabelling` record carrying its own left
inverse for the direction that does.

### 7.10 Cost

Measured, this session, on warm `.checked` dependencies:

| Module | Lines | Single-module verify |
|---|---|---|
| `Spec` | 281 | ~1 s |
| `Refinement` | 653 | ~9 s |
| `ModelTheory` | 363 | ~7 s |
| `Boundary` | 332 | ~11 s |

One session, four modules, three findings. The dominant cost was
**deciding what the specification should say** (the literal-equality
question in §3 is a spec-reading problem, not a proof problem), not
discharging proof obligations. Budget future verticals accordingly:
read the W3C text against the shipping code *first*, and expect the
divergences to be where the money is.

## 8. Follow-ups

* Discharge `entails_with_*` for `RDF.Entailment.Regime`'s
  instantiations, with their own fragment hypotheses (SE-3).
* Retire the hand-written OCaml `simple_entails_regime` in
  `w3c_runner.ml` in favour of the F\* engine (SE-3, rule #15).
* Lowercase language tags in the parsers (SE-2) — discharges half of
  `graph_exact` for every parsed graph.
* Give `entails_with` a strict-term-identity literal test for the
  simple regime (SE-1) — removes the soundness side condition.
* The `instance_subgraph_form` converse (§6).
* The genuine-simple-interpretation embedding (§6) — shared with the
  OWL programme's phase-2 obligation.
