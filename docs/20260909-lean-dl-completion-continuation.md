# Lean DL completion continuation, 2026-09-09

This continues the [8 September worknote](20260908-lean-dl-completion-and-scale.md)
under the owner's priority for [OWL DL completion](https://github.com/danbri/factoidal/issues/651)
and useful dataset scale. Raw inputs, commands, binary hashes and logs remain
in [the shared evidence JSON](20260908-lean-dl-scale-evidence.json).

## Integrated and checked

- Untyped assertion subjects now receive tableau nodes, so functional data
  properties also constrain their assertions. The six public QUDT-derived
  probes return false for both contradictions and true for all four controls.
- A generated required successor now violates a maximum of zero, including
  through a superproperty. Public same-role and superproperty contradictions
  return false; maximum-one and reversed-subproperty controls return true.
  Qualified-zero guards retain the known-filler condition. General witness
  distinctness remains unfinished.
- The SPARQL parser delta passes all 199 legacy syntax cases. Its two
  downstream tokenizer proofs are repaired without weakening the theorem
  statements. The root totals are 466/15 of 481 for SPARQL 1.0, 631/0 of 631
  for 1.1, and 254/0 of 254 for the ten 1.2 leaf manifests. Additional equality
  work is not included in those totals.

The full Lean build passes 1198 jobs. The hygiene audit scans 671 files and
962 axiom reports, finds no prohibited mechanisms, and retains 171 partial
functions. All 128 native API checks pass. These checks do not certify a
fresh Wasm artifact or close the [graph-to-tableau proof gap](https://github.com/danbri/factoidal/issues/586).

The last complete three-catalog DL score, before the two latest correctness
repairs, is 1048 pass / 66 fail / 1 skip / 8 unsupported of 1123 judgments,
covering 482 distinct IDs. It took 376.1 seconds with eight hard refuter
timeouts. A full rerun with subject seeding and zero-bound repair is underway.

## Measured scale

After subject seeding, schema.org plus 1000 added individuals completes in
9.447 seconds for the control and 4.994 for the contradiction. At 4000 added
individuals it takes 25.395 and 11.574 seconds, respectively. These are fresh
copied-binary runs with concurrent agent work recorded; all four verdicts are
unchanged. The earlier dispatch-only 4000 runs took 21.574 and 8.282 seconds,
so the new correctness work adds cost that further indexing must address.
The larger population pairs use the same copied binary and an external
90-second cap:

| Added individuals | Input triples, control | Control | Contradiction | Peak RSS across pair |
| ---: | ---: | ---: | ---: | ---: |
| 8000 | 49956 | true, 55.349 s | false, 18.079 s | 389 MB |
| 16000 | 81956 | no verdict, stopped at 90.022 s | false, 72.928 s | 640 MB |

The contradiction graph has one additional triple. The 16000 control has
no completed result; the cap is not a throughput measurement. The roughly
fourfold contradiction cost from 8000 to 16000 individuals exposes the
remaining superlinear work. Concurrent catalog and agent work is recorded.
Further optimization must preserve the source-licensed contradiction and
all controls, rather than hiding work behind the search budget.

A fresh QUDT comparison confirms that closure fuel 100 and the public closure
bound both produce the same ordered 638,420 triples. Both initialized states
clash on current source. The old phase harness's false-clash result is not
reproduced; the cause is unestablished. This corrects earlier speculative
explanations based on materialization or closure fuel.

## Work still in progress

Forced nominal merges are being profiled and batched to reduce repeated
passes and recover the description-logic-206 timeout regression. Literal
property entailment goals are being added separately. General minimum-witness
distinctness, blocking, finite-count constraint licensing and full executable
soundness remain open. No corpus score establishes complete OWL DL coverage.


## Latest catalog and phase results

With subject seeding and the zero-bound repair, the complete three-catalog
run is **1050 pass / 64 fail / 1 skip / 8 unsupported of 1123 judgments**.
The rows are 118/9/1/0, 381/27/0/4 and 551/28/0/4. The additional resolved
case is `WebOnt-I5.24-004`, counted in both positive-entailment catalogs.
The run takes 452.151 seconds, with 442.447 CPU seconds and ten refuter
timeouts. The previous integrated run was 376.060 seconds with eight
timeouts. Correctness improved while cost increased. Concurrent population
measurement and agent work are recorded for this comparison.

A 4000-individual first-pass phase probe visits 53824 labels across 9193
nodes, with 8591 TBox axioms and 112790 closure triples. It measures 5312 ms
for the pass: axiom application 3127, edge axioms 923, conjunction axioms 722,
globals 306, label lookup 198, label rules 3, and named index construction 8.
Functional injection measures below one millisecond. Therefore functional
injection is not the material phase in this population. The axiom phase
still includes complete-TBox fallback for nonnamed labels and state updates;
a further timing split is needed before assigning its cost to either.
