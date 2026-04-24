# Closure rules: prp-rfl + scm-cls (Agent Iota — 2026-04-24)

Single-commit goal: add two OWL 2 RL closure rules to
`formal/fstar/RDF.Graph.Executable.fst`, unblocking two PositiveEntailment
tests from Zeta's triage
(`docs/designissues/2026-04-24-owl-rl-posent-triage.md`).

## Coordination with Agent Theta

Theta is editing the same file (`scm-eqc2`, `scm-eqp2`, `eq-diff-sym`).
Theta has already committed (`69420d4`) and added `owl_differentFrom`
near line 1224. To avoid merge conflict:

- **Iota writes its IRI constant (`owl_ReflexiveProperty`) just before
  its new rule definitions** (after `owl_rule_cls_avf1`, around line 2108).
- **Iota appends the two new rules at the end of the OWL-RL Datalog
  rule block**, immediately before `owl_rl_closure_step` (line 2114).
- **Iota wires `g20`/`g21` into `owl_rl_closure_step` at the bottom**
  of the let-chain (after `g19 = owl_rule_cls_avf1 g18`).

Theta's likely insertion points (cls-eqc1/2 → scm-eqc2 mirror, prp-eqp1/2
→ scm-eqp2 mirror, sameAs_symmetry → diff-sym mirror) are all in the
range 1250 – 1490, well above Iota's edits.

## Rule 1 — `prp-rfl`

OWL 2 RL/RDF rule:
`(P rdf:type owl:ReflexiveProperty) → (x P x)` for every individual `x`.

The "individual" set is approximated by `owl_thing_subject_iris` (line
2180), which is already used by Group E to emit `i rdf:type owl:Thing`.
That over-approximation is sound under OWL-RL (every IRI that appears
as subject or IRI object is treated as an individual).

Implementation:

```fstar
let owl_ReflexiveProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#ReflexiveProperty");
  "http://www.w3.org/2002/07/owl#ReflexiveProperty"

let owl_rule_reflexive_property (g : rdf_graph) : rdf_graph =
  // Collect reflexive predicates first.
  let refl_props : list wf_iri =
    List.Tot.fold_left
      (fun (acc : list wf_iri) (t : triple) ->
        if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_ReflexiveProperty) then
          match t.s with
          | S_IRI p_iri -> cons_if_new_iri p_iri acc
          | _ -> acc
        else acc)
      []
      g
  in
  // For each reflexive property P and each individual x, emit (x P x).
  let indivs : list wf_iri = owl_thing_subject_iris g in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (p_iri : wf_iri) ->
      List.Tot.fold_left
        (fun (acc2 : rdf_graph) (x : wf_iri) ->
          let t : triple = { s = S_IRI x; p = p_iri; o = T_IRI x } in
          add_triple_if_new acc2 t)
        acc
        indivs)
    g
    refl_props
```

Target test: `New-Feature-ReflexiveProperty-001`.

## Rule 2 — `scm-cls` (Restriction → Class)

OWL 2 RL/RDF rule (subset): `(C rdf:type owl:Restriction) → (C rdf:type owl:Class)`.

```fstar
let owl_rule_scm_cls_restriction (g : rdf_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_Restriction_iri) then
        let new_t : triple = { s = t.s; p = rdf_type; o = T_IRI owl_Class } in
        add_triple_if_new acc new_t
      else acc)
    g
    g
```

Target test: `WebOnt-I5.5-005`.

## Wiring

In `owl_rl_closure_step` (line 2114), append:

```fstar
let g20 = owl_rule_reflexive_property g19 in
let g21 = owl_rule_scm_cls_restriction g20 in
g21
```

## Verification

- F\* verify only (no extract / compile per agent rules):
  `make -C formal/fstar verify` or `fstar.exe RDF.Graph.Executable.fst`.
- No `--lax`. Pre-existing warning 361 in `SPARQL11.Algebra.fst` is safe.

## Expected test deltas

- `New-Feature-ReflexiveProperty-001` — should flip to PASS.
- `WebOnt-I5.5-005` — should flip to PASS.

OWL-RL runner score: 3 / 30 → 5 / 30 expected (when combined with the
remainder of Theta's tier-1 rules: 8 / 30).
