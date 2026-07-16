# OWL 2 DL per-node algebraic tableau: successor-partition Farkas systems, and why dl-909 resists at this altitude too

Date: 2026-07-16. Status: ANALYSIS + DESIGN (no change to `Tableau.Refute.fst`
or `Tableau.CountingOracle.fst`). Tracks #299 (per-node algebraic tableau
re-pointing), extends the 2026-07-15 Wave-C refutation note.

## TL;DR

🧭 **Decision needed.** The #299 re-pointing (owner, 2026-07-15) set the next
OWL tinc wave as relocating the verified Farkas checker from *global class
sizes* to *per-node successor-partition arithmetic*, on the premise that
"a node's own successor arithmetic is anchored by the node existing (the thing
dl-909 lacks globally)." That premise is correct in general and is the right
architecture for qualified-cardinality clashes — but it does **not** reach
`WebOnt-description-logic-909`. This note proves why, with the per-node systems
written out and an explicit finite model.

- ⚠️ **dl-909 is consistent.** There is a one-element model (domain `= {d}`,
  every counting class empty). No sound tableau — global or per-node — can
  refute it. Flipping it to `inconsistent` would be an unsound verdict and
  would break the soundness gate (ZERO `unexpected-inconsistency`).
- The per-node grounding the re-pointing counts on anchors exactly one node in
  909 — the nominal `d` — whose successor system is `0 ≤ n_invF ≤ 10⁹`,
  trivially feasible. The nodes that carry the `2·3 ≠ 5` multiplication
  (`finite`, `cardinality-N`, `cardinality-N-times-M`) are **never forced to
  exist**, so their per-node systems are never instantiated.
- 📊 No verified flip is available. Per the #299 escape path (Wave-C
  precedent), this lands as an analysis note, not a zero-movement engine
  scaffold. `dl-909` stays out-of-fragment, exactly as `current-state.md`
  line 13 already records.
- ✅ Contrast confirmed: `dl-910` and `one=two` are reachable and are already
  decided by the landed global class-size Farkas checker
  (`Tableau.CountingOracle.class_size_unsat`) — their multiplication is
  grounded by a nominal that itself carries the cardinality (910) or by an
  `oneOf` nominal joined through IFP bijections (one=two).

The decision to surface: **retarget the per-node wave** at the clash class it
actually wins (single grounded node, multi-role / qualified-cell contradiction
that the current C3/C4 local rules miss), and keep `dl-909` labelled consistent
/ out-of-fragment. Details in §5–§6.

## 1. The per-node algebraic framework (the design the re-pointing asks for)

Prior art: Haarslev & Möller's algebraic tableau (Racer); Farsiniamarj &
Haarslev 2010, *hybrid ABox calculus for SHQ* (doi 10.3233/AIC-2010-0456);
Faddoul & Haarslev's SHOIQ extension (nominals + inverses). The arithmetic core
they bolt on with an unverified LP/ILP solver is, in our tree, the
already-proven Farkas validator in `Tableau.CountingOracle.fst`
(`farkas_check` + `farkas_sound`, §8a). The wave is a re-mounting of that
validator at a new altitude, not a new solver.

**Atomic decomposition at a node.** For a tableau node `x` with concept label
`L(x)`, fix the finite set of role/filler atoms relevant at `x` (the roles
mentioned by cardinality or `someValuesFrom` restrictions in `L(x)`, plus their
sub/super-roles and inverses; the named fillers of those restrictions). Partition
the (implied) successors of `x` into disjoint **cells** — one cell per
`(role, Boolean-combination-of-filler-atoms)` that can co-occur. Introduce one
`nat` variable `n_cell` per cell. Emit a linear system over the cell variables:

| source | constraint |
|--------|------------|
| `someValuesFrom r.C` / `minCard 1 r` | `Σ {n_cell : cell over r, cell ⊆ C} ≥ 1` |
| `minCardinality m r` (qual. `C`) | `Σ {n_cell : r, ⊆ C} ≥ m` |
| `maxCardinality n r` (qual. `C`) | `Σ {n_cell : r, ⊆ C} ≤ n` |
| `cardinality k r` (qual. `C`) | both of the above with `m = n = k` |
| role hierarchy `r ⊑ s` | every `r`-cell also summed into the `s` bounds |
| `FunctionalProperty r` | `Σ {n_cell : r} ≤ 1` |
| `InverseFunctionalProperty r` | dual `≤ 1` on `r⁻`-preimage cells |
| `differentFrom` over named successors | named-successor cell lower bound `≥` distinct count |
| **node existence** | the node contributes `+1` to the relevant inverse-role count at its predecessor (the grounding term) |

The node is **grounded**: because `x` exists, any successor obligation on `x`
must actually be met, so the system is not vacuously satisfiable by "make the
class empty" — which is exactly what the global class-size system permits.
Feeding `(N_cells, eqs, bounds)` into the existing `find_lin_cert` +
`farkas_check` gives a verified verdict; an accepted certificate is a proof that
**no** cell assignment satisfies the node's obligations, so `x` cannot exist in
any model — a sound clash.

Model-theoretic soundness comment (the one the wave would carry in
`Tableau.Refute.fst`): *a node whose successor-partition system is Farkas-refuted
has no successor multiset meeting its own labelled obligations; by the standard
successor-generation semantics of the `≤`/`≥`/`∃` rules, no element of any model
can carry `L(x)`, hence the branch that produced `x` clashes.*

## 2. dl-909 verbatim (from `type-inconsistency.rdf`, TestCase-…-909)

Object properties (all `owl:FunctionalProperty`, each with a named inverse):

```
p-N-to-1  : domain cardinality-N          range finite    inverse invP-1-to-N
q-M-to-1  : domain cardinality-N-times-M   range cardinality-N  inverse invQ-1-to-M
r-N-times-M-to-1 : domain cardinality-N-times-M range finite inverse invR-N-times-M-to-1
f-K-to-1  : domain finite                  range only-d    inverse invF-1-to-K
```

Classes:

```
only-d ≡ oneOf( d )                       ≡ (invF-1-to-K   maxCardinality 1000000000)
finite ≡ (invP-1-to-N          cardinality 2)
       ≡ (invR-N-times-M-to-1  cardinality 5)
       ≡ (f-K-to-1             someValuesFrom only-d)
cardinality-N          ≡ (p-N-to-1  someValuesFrom finite)
                       ≡ (invQ-1-to-M cardinality 3)
cardinality-N-times-M  ≡ (q-M-to-1  someValuesFrom cardinality-N)
                       ≡ (r-N-times-M-to-1 someValuesFrom finite)
```

The only named individual is `d : owl:Thing`, `d ∈ only-d` via `oneOf`. This is
a pure TBox plus one nominal — there is **no** ABox assertion typing any
individual into `finite`, `cardinality-N`, or `cardinality-N-times-M`.

The intended contradiction is "integer multiplication": with `N=2`, `M=3`,
`|cardinality-N| = 2·|finite|`, `|cardinality-N-times-M| = 3·|cardinality-N| =
6·|finite|`, and separately `|cardinality-N-times-M| = 5·|finite|`, so
`6·|finite| = 5·|finite|`, i.e. `|finite| = 0`. The multiplication only *bites*
once `|finite| ≥ 1`.

## 3. The per-node systems for dl-909 (the actual inequalities)

There is exactly one **grounded** node: `d`.

**Node `d` (`d ∈ only-d`).** The only restriction touching `d`'s successors is
`only-d ≡ (invF maxCardinality 10⁹)`. Cell: `n_invF` = number of `invF`-
successors of `d` (finite-nodes `b` with `f(b,d)`). `oneOf(d)` gives no successor
obligation; `only-d` carries no `someValuesFrom`/`minCardinality`. System:

```
n_invF ≥ 0
n_invF ≤ 1000000000
```

Feasible (`n_invF = 0`). No Farkas certificate exists. **No clash at `d`.**

**Hypothetical node `x ∈ finite`** (shown to demonstrate the multiplication is
not local — but note `x` is never forced to exist, §4). `finite`'s three
equivalent definitions put obligations on three *distinct* roles:

```
invP cells (preimages under p, in cardinality-N)       :  n_invP = 2
invR cells (preimages under r, in cardinality-N-times-M):  n_invR = 5
f    cell  (image under f, in only-d), f functional     :  1 ≤ n_f ≤ 1  ⇒ n_f = 1
n_invP, n_invR, n_f ≥ 0
```

`invP`, `invR`, `f` are unrelated roles (no role hierarchy links them), so the
system is block-diagonal and trivially **feasible** (`n_invP=2, n_invR=5,
n_f=1`). **No clash at `x`.** The `6 = 5` contradiction is a relation between the
*sizes* of `finite`, `cardinality-N`, `cardinality-N-times-M`, obtained by
summing per-node fibers across *all* such nodes — precisely the global
class-size system, not any one node's partition.

Likewise the hypothetical nodes in `cardinality-N` (`n_p = 1` via functional
`p`-`someValuesFrom finite`, `n_invQ = 3`) and `cardinality-N-times-M`
(`n_q = 1`, `n_r = 1`) are each block-diagonal and feasible. Every per-node
system in 909 is feasible.

## 4. Why per-node grounding does not reach dl-909: an explicit model

The re-pointing's premise is that node existence supplies the `|finite| ≥ 1`
the global system lacks. It does not, because **no node of `finite` (or of
`cardinality-N`, `cardinality-N-times-M`) is ever forced to exist.** The single
grounded node is `d`, and `d`'s system (§3) is feasible with no successors.

Concretely, here is a model of dl-909, which is therefore **consistent**:

```
Δ = { d }                      (one element)
only-d^I               = { d }
finite^I               = ∅
cardinality-N^I        = ∅
cardinality-N-times-M^I = ∅
p^I = q^I = r^I = f^I   = ∅     (no role edges)
```

Check every axiom:

- `p,q,r,f` functional: vacuous (no edges). ✅
- `rdfs:domain` / `rdfs:range`: vacuous (no edges). ✅
- `only-d ≡ oneOf(d)`: `only-d^I = {d}`. ✅
- `only-d ≡ (invF maxCard 10⁹)`: `d` has `0 ≤ 10⁹` `invF`-successors; and every
  element with `≤ 10⁹` `invF`-successors is `d` (there is only `d`). So
  `{x : |invF(x)| ≤ 10⁹} = {d} = only-d^I`. ✅
- `finite ≡ (invP card 2)`: `d` has `0` `invP`-successors `≠ 2`, so
  `{x : |invP(x)| = 2} = ∅ = finite^I`. ✅
- `finite ≡ (invR card 5)`: analogously `∅`. ✅
- `finite ≡ (f some only-d)`: `d` has no `f`-successor (`f^I = ∅`), so
  `{x : ∃f.only-d} = ∅ = finite^I`. ✅ (`someValuesFrom` constrains members of
  `finite`; the minimal model puts nothing in `finite`, so no `f`-edge is owed.)
- `cardinality-N ≡ (p some finite)`: `= ∅`. ✅ `≡ (invQ card 3)`: `∅`. ✅
- `cardinality-N-times-M ≡ (q some cardinality-N)`: `= ∅`. ✅
  `≡ (r some finite)`: `= ∅`. ✅

All axioms hold, so dl-909 has a model. It is **not** inconsistent. Any engine
reporting it inconsistent is unsound on this input.

Note the `maxCardinality 10⁹` "spy-point" trick genuinely forces the domain to
be `{d}` in any model of size `≤ 10⁹` (every element with `≤ 10⁹` `invF`-
successors must equal `d`; and any element mapping into `only-d` under `f`
collapses onto `d` by functionality). But collapsing the domain to `{d}` does
not populate `finite` — it makes `finite` provably *empty* (`d` cannot have the
`2` distinct `invP`-predecessors `finite` demands inside a one-element domain).
Either way, empty `finite`, consistent.

This is the same conclusion three independent analyses reached: the
`Tableau.CountingOracle.fst` §8 header ("dl-909's class-size system is genuinely
satisfiable … deriving `|finite| ≥ 1` would need an UNSOUND nonemptiness rule"),
the 2026-07-15 Wave-C note, and this per-node re-derivation.

## 5. Why dl-910 and one=two ARE reachable (grounding difference)

The reachable siblings differ from 909 in exactly one respect: **the nominal
carries the multiplication**, so `|nominal| ≥ 1` grounds it.

- **dl-910.** Here `only-d ≡ {d} ≡ (invP card 20) ≡ (invR card 601)`. The
  cardinalities sit on `only-d` *itself*. `oneOf(d)` gives `|only-d| ≥ 1`, so
  `|cardinality-N| = 20`, `|cardinality-N-times-M| = 601` and `= 30·20 = 600`;
  `601 ≠ 600` with the anchor active. Grounded, refutable. The global
  class-size Farkas checker (`ONEOF`-nonemptiness `|only-d| ≥ 1` plus the FIBER
  equalities) already decides it — `current-state.md` line 11–12, zero
  oracle-assisted.
- **one=two.** `a ≡ oneOf(i,j,k)` with `AllDifferent` gives `|a| = 3` grounded;
  eight `FunctionalProperty` + `InverseFunctionalProperty` roles wire 1-1
  bijections forcing `|a| = 2·|a|`. Grounded by the `oneOf` nominal and closed
  by BIJECTION/DISJOINT-UNION; decided by the same global checker.

909's cardinalities sit on `finite`, an *unnamed, unpopulated* class — no
nominal, no `minCardinality`/`someValuesFrom` from a grounded class points into
it — so nothing plays the role `oneOf(d)` plays in 910 / `oneOf(i,j,k)` plays in
one=two. That is the whole difference, and it is a property of the ontology, not
of the reasoning altitude. Moving to per-node arithmetic changes where the
system is *assembled*, not whether `finite` is *inhabited*.

## 6. Where the per-node wave DOES win (forward value)

Per-node atomic decomposition is strictly stronger than the current local clash
rules `Tableau.Refute.fst` C3 (one property `≥m`/`≤n`, `m>n`) and C4 (`≤k` with
`k+1` provably-distinct successors) for a **single grounded node** whose
contradiction spans:

- multiple qualified cells under one role (e.g. `≥3 r.C ⊓ ≤1 r.D ⊓ ≤1 r.(¬D)`
  with `C ⊑ D ⊔ ¬D`), which C3/C4 cannot combine;
- a role-hierarchy sum (`≥2 r ⊓ ≤1 s` with `r ⊑ s`);
- `differentFrom` lower bounds crossing cells;
- FP/IFP `≤1` interacting with a qualified `≥2`.

These are the Racer/Farsiniamarj target patterns. **None of the 14 current tinc
residuals is of this shape** (they are: complementOf/oneOf search — dl-026/027,
dl-502, Thing-005; datatype/concrete-domain — dl-626/627, I5.8-001/003,
Rational-002, the float/pattern/disjoint-dataproperty singletons; and the three
finite-model counting tests, of which 910 + one=two are already decided and 909
is consistent). So the per-node wave, mounted soundly, flips **zero** of the
current corpus. Its value is architectural (correct mechanism for future
qualified-cardinality inputs and for absorbing FP/IFP merges), not a score move
today.

Recommendation: if the wave is dispatched, gate it on *soundness held +
wall-clock ≤ +10% + zero regressions*, and measure its win on a purpose-built
qualified-cardinality fixture rather than on 909. Do **not** gate it on flipping
909; 909 has no sound flip.

## 7. The corrected premise (surfaced per CLAUDE.md "Reading owner steers" §3)

Quoting the #299 re-pointing (owner, 2026-07-15): *"the tableau node grounds
nonemptiness (the thing dl-909 lacks globally — its class-size system is
satisfiable by all-empty, but a node's own successor arithmetic is anchored by
the node existing). Subsumes dl-909 …"*

The load-bearing half — *node existence grounds successor arithmetic* — is
correct and is the reason per-node beats the global altitude on qualified-cell
clashes. The implication *"subsumes dl-909"* does not follow: the node whose
existence 909 grounds is `d`, and `d`'s successor system is feasible; the nodes
whose arithmetic would clash (`finite` et al.) are the ones 909 never grounds.
909 is consistent (§4), so it is not a completeness gap to close — there is
nothing to refute.

Question for the owner: accept `dl-909` as **consistent / out-of-fragment**
(as `current-state.md` line 13 already frames it, and retire it as a flip
target), and retarget the per-node algebraic wave at the qualified-cardinality
clash class of §6 — measured on a dedicated fixture — rather than at 909?

## 8. Gate / floor status for this landing

Doc-only. No `.fst`, no `owl_runner.ml`, no build-list, no extracted `.ml`
touched — so every suite is unchanged by construction:

- ✅ DL type-inconsistency: unchanged (114 pass, 14 fail of 128, zero
  oracle-assisted per `current-state.md`; dl-909 remains consistent /
  out-of-fragment — correctly, not a regression). Observed on the worktree's
  committed binary: raw InconsistencyTest 34 pass / 94 fail (of 128) +2
  oracle-assisted, the report-layer/DL-aggregation reconciliation described in
  the Wave-C note §"Gate evidence"; the binary predates the merged class-size
  reasoner sources and is not rebuilt by this doc-only branch.
- ✅ Soundness: no new `unexpected-inconsistency` — no verdict path changed.
- ✅ tcon 352/0, PE 123/81, NE 22/1, RDF six-suite 1031/0, sparql11-query
  338/0, csvw 251/19: unchanged (no engine file touched).
- ✅ Wall-clock: unchanged (no engine change). InconsistencyTest-only pass
  measured at 4.37 s on this binary for reference.
- ✅ No `experimental_ocaml_glue` additions; no hand-edited extracted `.ml`.

Landing follows the #299 escape path and the Wave-C precedent: a rigorous
analysis note, not a zero-movement engine scaffold.
