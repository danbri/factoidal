# W3C OWL 2 Test Cases (vendored)

**Source:** <https://www.w3.org/2009/11/owl-test/>
**Fetched:** 2026-04-24
**Refresh:** see `Makefile` (or re-run the `curl` loop in the commit that
introduced this directory)

## What this is

The W3C OWL 2 Test Cases, as published by the OWL Working Group on
2009-11-18 and still the reference corpus for OWL 2 conformance. Each
file is a single RDF/XML catalog containing `test:TestCase` entries
with input ontologies, expected results, and profile annotations.

Unlike the W3C SPARQL 1.1 suite (a living repository at
`github.com/w3c/rdf-tests`, pulled in here as
`third_party/testing/w3c/` via a git submodule), the OWL 2 test set
was published as a *static drop* — there is no canonical upstream git
repo. We therefore vendor the files directly.

## Files

| File | Size | Purpose |
|---|---:|---|
| `all.rdf` | 3.0 MB | Full catalog of all test cases |
| `semantics-direct.rdf` | 3.0 MB | Direct-semantics (DL) conformance tests |
| `syntax-dl.rdf` | 2.5 MB | OWL 2 DL syntax tests |
| `type-consistency.rdf` | 2.4 MB | Tests where the ontology must be consistent |
| `type-positive-entailment.rdf` | 1.5 MB | Tests where a premise ontology entails a conclusion |
| `type-inconsistency.rdf` | 616 KB | Tests where the ontology must be inconsistent |
| `profile-RL.rdf` | 260 KB | OWL 2 RL profile-identification tests |
| `profile-EL.rdf` | 244 KB | OWL 2 EL profile-identification tests |
| `profile-QL.rdf` | 181 KB | OWL 2 QL profile-identification tests |
| `type-negative-entailment.rdf` | 166 KB | Tests where a premise does NOT entail the conclusion |
| `RL-RDF-rules-tests.rdf` | 725 B | RL-specific rule tests |
| `Makefile` | 201 B | Upstream's own fetch script (`make sync`) |

## Relationship to the SPARQL entailment suite

The SPARQL 1.1 `entailment` suite under
`third_party/testing/w3c/sparql/sparql11/entailment/` tests
*query-bearing* entailment — SPARQL queries annotated with regime
hints (RDFS, OWL-RL, OWL-Direct). It's the right thing to run for
regressions in `SPARQL11.Algebra.fst`.

These OWL 2 Test Cases test *raw* OWL 2 reasoning — consistency,
entailment, profile membership — independent of SPARQL. They're the
right thing to run against `Tableau.fst` (for DL) and whatever we
wire up for OWL 2 RL entailment (per
`docs/designissues/2026-04-23-entailment-plan.md`).

Neither runs yet against these files. Wiring a runner that reads
`test:TestCase` entries is a follow-up.

## Licence

The W3C OWL 2 Test Cases are published under the **W3C Document
Licence** (3-clause BSD-style, with attribution):
<https://www.w3.org/Consortium/Legal/2015/doc-license>.

We redistribute unchanged. When these files are later consumed by
tooling, retain the test-case identifiers exactly as they appear
(e.g. `http://owl.semanticweb.org/id/Chain2trans`) so provenance is
preserved in any downstream report.

## Re-syncing

The upstream directory is at
<https://www.w3.org/2009/11/owl-test/>. To refresh:

```bash
cd third_party/testing/owl
for f in Makefile RL-RDF-rules-tests.rdf all.rdf \
         profile-EL.rdf profile-QL.rdf profile-RL.rdf \
         semantics-direct.rdf syntax-dl.rdf \
         type-consistency.rdf type-inconsistency.rdf \
         type-negative-entailment.rdf type-positive-entailment.rdf; do
  curl -sSfL "https://www.w3.org/2009/11/owl-test/$f" -o "$f"
done
```

If upstream ever moves to a git repo, this directory should convert to
a submodule following the pattern used for `third_party/testing/w3c/`.
