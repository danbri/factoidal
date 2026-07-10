# 2026-07-10 — QUDT scoping

## Status

Research + scoping only (owner directive 2026-07-09: "scoping out a
QUDT implementation"). Written to answer: what does "implementing
QUDT" mean for an engine like ours, what is measurable, and what is
the F\* shape.

## What QUDT is

QUDT (Quantities, Units, Dimensions and data Types,
[qudt.org](https://qudt.org/)) is an ontology suite — not a W3C
Recommendation with a conformance suite, but the de-facto RDF
vocabulary for units of measure. Current release **v3.4.0**
(2026-06-25, [github.com/qudt/qudt-public-repo](https://github.com/qudt/qudt-public-repo)).
The distribution ships two all-in-one Turtle files
(`QUDT-all-in-one-SHACL.ttl`, `QUDT-all-in-one-OWL.ttl`) carrying the
schema plus the unit / quantity-kind / dimension-vector vocabularies,
and two SHACL rulesets (a user-facing one flagging deprecated
instances, and a contributor-facing one validating the integrity of
the QUDT ontologies themselves).

The three ideas that matter for an implementation:

1. **Units carry conversion data**: `qudt:conversionMultiplier` (and
   `qudt:conversionOffset` for affine units like °C/°F) relating each
   unit to the SI coherent base unit of its kind.
2. **Quantity kinds carry dimension vectors**: every
   `qudt:QuantityKind` has a `qudt:hasDimensionVector` — an 8-basis
   exponent vector (length, mass, time, electric current,
   temperature, amount, luminous intensity, dimensionless) that makes
   dimensional analysis a vector-arithmetic problem.
3. **Quantities are (value, unit) pairs** (`qudt:Quantity` /
   `qudt:QuantityValue`), so datasets can carry measurements whose
   comparability is decidable from the ontology.

## What "implementing QUDT" means for us — three candidate layers

**Layer A — validation (cheapest, reuses the most).** Load the QUDT
distribution and user data with our engine; run the shipped SHACL
rulesets with our verified SHACL validator (core 98/0,
sparql-constraints 22/0). Deliverable: a `qudt` suite row = our
validator's verdicts over (a) the QUDT contributor shapes against the
QUDT distribution itself, (b) a small fixture set of deliberately
broken quantity data against the user shapes. This is measurable on
day one and exercises SHACL at real-ontology scale (the all-in-one
file is large — also a natural perf-program corpus). Size: **S**
(runner + fixtures; no new F\* semantics).

**Layer B — unit conversion + dimensional analysis in F\* (the real
win).** New module family (e.g. `QUDT.Dimension.fst`,
`QUDT.Convert.fst`):
- dimension vectors as records of 8 `int` exponents; multiplication/
  division/power of quantities = exponent add/subtract/scale;
  commensurability = vector equality. All trivially `Tot`, and the
  algebraic laws (associativity, inverse, identity) are provable —
  this is the rare feature where we can prove the SEMANTIC core, not
  just termination.
- conversion over **exact rationals** (`Math.*` — the CAS work):
  `conversionMultiplier` values are decimal literals (e.g. exactly
  `0.3048` m/ft), so rational arithmetic is EXACT for the affine
  map `si = value * multiplier + offset`; round-trips
  (`convert u1 u2 >> convert u2 u1`) are provably identity over ℚ,
  which floating-point implementations cannot claim. That proof is a
  differentiator worth a hub post on its own.
- the ontology data (unit → multiplier/offset/dimension-vector table)
  is DATA, not code: loaded from the vendored QUDT Turtle at runtime
  by consumers, parsed with our own Turtle parser (rule #6 — real
  files), handed to the pure F\* functions as an argument. No
  vocabulary baked into the verified core.
Size: **M** (the F\* algebra is small; the plumbing — vendoring,
lookup, CLI/npm surface — is the bulk).

**Layer C — SPARQL surface.** A `qudt:` function library in the
geof:-style extension-function pattern
(e.g. `qudtf:convert(?value, ?fromUnit, ?toUnit)`,
`qudtf:commensurable(?u1, ?u2)`), letting FILTERs and BINDs do
unit-aware comparison over real datasets. Reuses the existing
extension-function dispatch the GeoSPARQL work built. Size: **S**
on top of Layer B.

## Measured targets (no W3C suite exists — define ours honestly)

Dashboard-row shaped, per rule #25:
1. **qudt-shacl**: X pass / Y fail — our SHACL validator over the
   QUDT contributor ruleset + distribution (verify our verdict
   matches the ruleset's intent on a spot-checked subset; any
   disagreement with a reference validator like pySHACL on the same
   input is a bug to chase, per the Jena-probe policy in
   test-suites).
2. **qudt-convert**: derived test set — for every unit pair sharing a
   dimension vector in a chosen subset (start: length, mass, time,
   temperature — the affine case), assert exact round-trip identity
   and assert conversion against a handful of externally-known
   constants (ft→m, lb→kg, °F→°C). Counted, committed as fixtures
   with provenance.
3. **qudt-dimension**: algebraic law checks (also provable in F\* —
   the runner then just witnesses extraction correctness).

## Risks / honesty notes

- **Scale**: the all-in-one Turtle is large; parse+SHACL over it is a
  perf test as much as a correctness test. If it trips runtime caps,
  that is a finding for the perf program, not a reason to shrink the
  fixture silently (anti-pattern #16/#25).
- **Non-rational multipliers**: a few units have multipliers that are
  themselves rounded decimals of irrational definitions. We are exact
  w.r.t. the ONTOLOGY'S published multiplier — state that boundary in
  the module banner; do not claim exactness w.r.t. physics.
- **Licence**: record LICENSE.md terms in PROVENANCE.md at vendoring
  time (CC-BY-family expected; verify then).
- RDF 1.1 datatype interplay (`qudt:numericValue` as xsd:decimal vs
  double) hits anti-pattern #8's double-aware parsing — reuse the
  existing promoted-type discipline.

## Recommendation & sequencing

Layer A is a cheap, honest new suite row and a real SHACL/perf
corpus — good early. Layer B is the substantive contribution and a
showpiece for exact-rational verification (provable round-trip
identity); it depends only on Math.\* and the Turtle parser, both
stable. Layer C rounds it into user-facing SPARQL. Sequence AFTER the
current ledger burn-down (CSVW/JSON-LD/XML) since QUDT opens a new
row rather than closing an existing failure — same sequencing logic
as the OpenPGP scoping (2026-07-10-openpgp-signing-scoping.md).
