# Tier-2 OWL-RL closure rules — Agent Kappa scratch (2026-04-24)

Single-commit goal: add the Tier-2 rules called out by Zeta's triage
(`docs/designissues/2026-04-24-owl-rl-posent-triage.md`) so that the
OWL 2 RL PositiveEntailment score moves from 8/30 (after Theta+Iota
landed Tier-1) toward ~11/30.

## Target tests

| Test | Mode | Rule needed |
|---|---|---|
| `chain2trans1` | (a) | scm-trans-from-chain: `P propertyChainAxiom (P P) → P a owl:TransitiveProperty` |
| `New-Feature-ObjectPropertyChain-001` | (a) | prp-spo2 (n=2): chain composition produces `(x P z)` |
| `New-Feature-ObjectPropertyChain-BJP-003` | (a) | same prp-spo2 |
| `WebOnt-I4.6-003` | (d) | named `sameAs → equivalentClass` (both sides IRI + `a owl:Class`) |
| `WebOnt-I4.6-005-Direct` | (d) | falls out from the same rule + existing eq-rep-s |

## Rules to add

In `formal/fstar/RDF.Graph.Executable.fst`, after the existing
`owl_rule_scm_cls_restriction` (~line 2273) and before
`owl_rl_closure_step`:

1. **Constants**: `rdf_first`, `rdf_rest`, `rdf_nil`,
   `owl_propertyChainAxiom`.
2. **Helper `decode_chain_pair`**: given a graph and a list head
   subject, attempt to read a 2-element RDF collection and return
   `Some (p1, p2)` if both elements are IRI properties and the rest
   is `rdf:nil`. Returns `None` for any other shape (n=1, n≥3,
   non-IRI elements, malformed list).
3. **`owl_rule_property_chain_2`**: for each
   `(P owl:propertyChainAxiom L)` with `L` decoding to `(P1, P2)`,
   for each `(x P1 y)` and `(y P2 z)`, emit `(x P z)`.
4. **`owl_rule_chain_to_transitive`**: for each
   `(P owl:propertyChainAxiom L)` with `L = (Q1, Q2)` and
   `Q1 = Q2 = P`, emit `(P rdf:type owl:TransitiveProperty)`.
   Sound but not in the standard OWL-RL/RDF table — flagged in
   Zeta's "surprises" section.
5. **`owl_rule_named_sameAs_to_equivClass`**: for each
   `(C owl:sameAs D)` where C and D are IRIs and both already carry
   `rdf:type owl:Class`, emit `(C owl:equivalentClass D)` and
   `(D owl:equivalentClass C)`. Bnode-guarded to avoid the
   class-expression pollution that bites
   `owl_rule_equivalent_class`.

Wire all of them into `owl_rl_closure_step` after
`owl_rule_scm_cls_restriction`.

## Constraints

- F\* only. No OCaml, no patches, no rewriter changes.
- Stack-safe (`List.Tot.fold_left` throughout). No list reversal.
- No `--lax`. Verify with
  `fstar.exe --include . --cache_dir .cache RDF.Graph.Executable.fst`.
- Cap: ≤150 new F\* lines, ≤60 min wall-clock.
- Stay south of line 1100 (Lambda owns `graph_add_unchecked` near 200–300).

## Expected delta

+3 OWL-RL PosEnt tests flipping FAIL→PASS (#7, #9, #25). #12 / #13
may flip too if existing eq-rep-s already propagates predicates
through equivalentClass via the cls-eqc1/2 expansion path; if not,
they stay FAIL but are no worse off.

## Notes / risk

- We only handle n=2 chains. Generalising to n≥3 needs a recursive
  walker; not required for the three target chain tests (all n=2).
- The chain decoder must be careful not to follow corrupt collections
  (cycles, missing rest); we use a fuel-bounded `find_objects` walk
  but only for two hops, so termination is trivial.
