# rdf-mt-generated: executable tests for proved closure rules

Adoption item **A2** from
[`docs/designissues/2026-08-05-semantics-proposal-adoption.md`](../../docs/designissues/2026-08-05-semantics-proposal-adoption.md):
"generated property tests + soundness boundary tests" per proved rule.

**What this checks that the F\* proofs do not:** the theorem registry
(`docs/theorem-registry.md`) proves each rule sound against an
independent F\* model. It does NOT check that the *extracted, compiled,
shipping* `factoidal` binary actually behaves that way on a concrete
graph. This suite runs small premise graphs through the **committed
native binary** (`factoidal entail --data FILE --regime RDFS|OWL-RL`)
and asserts the conclusion triple the registry says is proved.

**Scope (pilot, not exhaustive):** the four RDFS milestone rules —
rdfs2 (domain), rdfs3 (range), rdfs7 (subPropertyOf), rdfs9
(subClassOf) — plus the three functional-property OWL rules proved
2026-08-05: prp-fp, prp-ifp, prp-key.

## Files

- `generate.sh` — writes every fixture `.ttl` into `fixtures/`.
  Idempotent; `run.sh` calls it before testing so fixtures are always
  fresh.
- `fixtures/*.ttl` — the generated premise graphs (18 files, one per
  test variant below).
- `run.sh` — runs the binary against each fixture, checks the closure,
  prints `N pass, M fail (out of T)`, exits nonzero on any failure.
- `WIRING.md` — the one-line hook for wiring this into the orchestrator
  (`w3c-tests.sh` or CI), NOT applied here per the task brief.

## What each test pins, and its registry row

| Test name | Registry row (`docs/theorem-registry.md`) | Pins |
|---|---|---|
| `rdfs2-domain-template` | line 196: rdfs2 / `rdfs2_derives` / `rdfs_rule_domain` / PROVED+PROVED | Premise `p rdfs:domain C`, `x p y` → conclusion `x rdf:type C` appears in the shipping closure. |
| `rdfs2-order-independent` | same row | Swapping the two premise triples' order in the input file produces a byte-identical sorted closure. |
| `rdfs2-duplicate-premises-set-equivalent` | same row | Repeating the `x p y` premise triple produces a byte-identical sorted closure (no duplicate conclusion lines — set semantics, not multiset). |
| `rdfs3-range-template` | line 197: rdfs3 / `rdfs3_derives` / `rdfs_rule_range` / PROVED+PROVED, finding RS-3 | Premise `p rdfs:range C`, `x p y` (y an IRI) → conclusion `y rdf:type C` appears. |
| `rdfs3-order-independent` | same row | Same order-swap check as rdfs2. |
| `rdfs3-literal-boundary-iri-branch-fires` | same row, RS-3 | In a mixed fixture (one IRI-object premise, one literal-object premise on the same property), the IRI branch still derives its conclusion. |
| `rdfs3-literal-boundary-literal-does-not-become-subject` | same row, RS-3 | **Soundness boundary.** The literal-object premise (`x2 p "literal value"`) must NOT derive `"literal value" rdf:type C` — a literal can never be an N-Triples subject. Asserted by counting all `rdf:type C` conclusions in the mixed fixture and requiring exactly 1 (the IRI branch only). This is the shipping counterpart of registry finding RS-3 ("silently drops the literal/triple-term-object case"). |
| `rdfs7-subPropertyOf-template` | line 202: rdfs7 / `rdfs7_derives` / `rdfs_rule_subPropertyOf` / PROVED+PROVED | Premise `p rdfs:subPropertyOf q`, `x p y` → conclusion `x q y` appears. |
| `rdfs7-order-independent` | same row | Order-swap check. |
| `rdfs7-duplicate-premises-set-equivalent` | same row | Duplicate-premise check. |
| `rdfs9-subClassOf-template` | line 204: rdfs9 / `rdfs9_derives` (`rdfs9_derives2`) / `rdfs_rule_subClassOf` / PROVED+PROVED | Premise `C rdfs:subClassOf D`, `x rdf:type C` → conclusion `x rdf:type D` appears. |
| `rdfs9-order-independent` | same row | Order-swap check. |
| `rdfs9-duplicate-premises-set-equivalent` | same row | Duplicate-premise check. |
| `prp-fp-functional-template-fwd` / `-rev` | line 102: prp-fp / `prp_fp_derives` / `functional` / PROVED (licensing), UNATTEMPTED (truth) | Premise `p a owl:FunctionalProperty`, `x p y1`, `x p y2` → `y1 owl:sameAs y2` AND `y2 owl:sameAs y1` both appear (the engine composes prp-fp with eq-sym). |
| `prp-fp-duplicate-premises-set-equivalent` | same row | Duplicating one of the two object-premises produces a byte-identical sorted closure. |
| `prp-ifp-inverse-functional-template` | line 103: prp-ifp / `prp_ifp_derives` / `inverse_functional` / PROVED (licensing), UNATTEMPTED (truth) | Premise `p a owl:InverseFunctionalProperty`, `x1 p y`, `x2 p y` (shared literal object `"123"`) → `x1 owl:sameAs x2` appears. |
| `prp-key-weakened-row-unifies-case-differing-lang-tags` | line 140: prp-key / `prp_key_derives` (row) / `prp_key_derives_approx` (proved against) / `prp_key` / PROVED, **WEAKENED ROW**, commit `c600646` | **Pins actual shipping behavior, not an absence.** Premise: `Person owl:hasKey (name)`, `p1 a Person; name "Alice"@en`, `p2 a Person; name "Alice"@EN`. The row's `shares_key_values` uses plain `==` (would NOT unify these — different lang tag case); the engine's `agree_on_property` uses `rdf_term_eq` (RDF-1.1 value equality, case-insensitive lang tags, #337) — an over-approximation. This test asserts `p1 owl:sameAs p2` DOES appear, matching the registry's own machine-checked counterexample. If this test ever starts failing, either the engine's `agree_on_property` semantics changed (update the registry note) or the weakening was tightened to match the literal row (update this test's expectation and the registry cell). |

## Running

```sh
tests/rdf-mt-generated/run.sh
```

Resolves the binary the same way `tests/local/*.sh` scripts do:
`formal/fstar/ocaml-output/factoidal` (the current-platform symlink)
first, falling back to `bin/linux-x86_64/factoidal`. Regenerates
fixtures on every run via `generate.sh`, then checks each fixture's
closure via `check_present` / `check_absent` / `check_count` /
`check_same_closure` helpers defined in `run.sh` itself. Prints a
labelled `N pass, M fail (out of T)` summary (anti-pattern #25) and
exits nonzero on any failure (anti-pattern #14 — no swallowed exit
codes).

## What this does NOT cover (by pilot scope, not oversight)

- The other 10 RDFS rows and 80+ OWL 2 RL/RDF rows in the registry —
  future extension of this same pattern, one fixture pair per row.
- SPARQL entailment regimes over these same rules (queued in the
  adoption doc as "extraction boundary already has the hash-witness
  pattern").
- Negative/inconsistency tests (e.g. `cls-maxqc1` clash detection) —
  a different assertion shape (`ASK` inconsistency, not a derived
  triple) than the `_derives` template this suite covers.
