# RDFC-1.0 Phase 3 — Investigation of remaining 23 eval fails

**Agent:** Nun  **Date:** 2026-04-25  **HEAD:** 554e134

## Context

After Bet2's Phase 2 (HNDQ — two-level neighbour-hash refinement) the
RDFC-1.0 eval suite stands at **41 pass / 23 fail / 22 stub (Map) out of 86**.

This doc classifies the 23 remaining `[Eval]` fails and identifies which
are tractable inside the F\* `RDF.Canonical.fst` module without
permutation enumeration (W3C §4.9 strict).

## Classification of the 23 fails

| Test ids | Name | Class | Phase 3 deeper recursion fixes? |
| --- | --- | --- | --- |
| 024–029 (×6) | double circle of 3 (next/prev cycle) | (b) **true automorphism** | No — all 3 bnodes structurally indistinguishable at every depth; needs §4.9 permutation enumeration with cloned issuer |
| 033, 034 | disjoint identical subgraphs | (b) **2 isomorphic components** | No — true automorphism between the two pairs; permutation enumeration required |
| 035, 036 | reordered w/strings | (b) **2 isomorphic chains** | No — same as 033 |
| 040 | reordered 6 bnodes | (b) **2 isomorphic 3-chains** | No — same as 033 |
| 044, 045, 046 | poison – evil (1/2/3) | (b) **highly symmetric K3,3-like graph** | No — full §4.9 |
| 047, 048 | deep diff | (a) **chain depth 2-3 distinguished by literal** | **POSSIBLY** — Phase 3 (3-level neighbour) might propagate the literal distinction deeper |
| 054 | t-graph (16-node chain w/branch) | (a)/(b) **long chain, partial symmetry** | Maybe at depth ≥ 4 |
| 058 | unnamed graph with bnode-graph objects | (b) **graph-slot bnode ordering** | No — issuer ordering question |
| 059 | n-quads parsing (multi bnode-graph) | (b) **multi disjoint isomorphic graphs** | No |
| 060 | n-quads escaping | (d) **serialiser bug** — `escape_lit_char` lacks `\uXXXX`/`\UXXXXXXXX` escaping for `< 0x20` codepoints, IRI escapes too | Out of scope — needs N-Triples §4 escaping in `canon_term`/`escape_lit_char` |
| 075 | blank node — diamond (uses **SHA-384**) | (e) **wrong hash algorithm** — manifest sets `rdfc:hashAlgorithm "SHA384"` but our `hash_sha256` is hardcoded | Out of scope — hash dispatch by manifest |
| 076 | duplicate ground triple | (e) **set semantics — dedup** required | **QUICK WIN** ≤ 30 LoC F\* |
| 077 | duplicate bnode triple | (e) **set semantics — dedup** required | **QUICK WIN** same |

## Counts

- **Class (a) tractable now via Phase 3 (3-level nbr hash)**: 047, 048, possibly 054 → **2-3 wins**
- **Class (b) needs §4.9 permutation enumeration** (out of scope this session): 024–029, 033, 034, 035, 036, 040, 044, 045, 046, 058, 059 → **15 fails**
- **Class (d) parser/serialiser**: 060 → **1**
- **Class (e) other**:
  - 076, 077 dedup → **2 quick wins**
  - 075 SHA-384 dispatch → **1, defer**

## What this session lands

1. **Quick win — RDF set semantics dedup** for 076, 077 (~20 LoC F\* in
   `RDF.Canonical.fst`).
2. **Phase 3 — `compute_all_nbr3`** mirroring `compute_all_nbr2` (~25
   LoC); extends `bn_full_key` with `bk_nbr3`. Wires in 047/048 if
   they're truly depth-3 distinguishable.

Out-of-scope (documented for follow-up):
- §4.9 permutation enumeration — 15 fails. Substantial work; will need
  `hash_n_degree_quads` with cloned issuer, `permutations` over related
  bnodes within each collision class. Tracks separately.
- SHA-384 dispatch (test075).
- N-Triples §4 unicode escape (test060).

## Expected delta

If Phase 3 catches 047 + 048: **41 → 43 pass** (and 076/077 → +2 → 45 pass).
Worst case (Phase 3 helps neither 047 nor 048): 41 → 43 (just from dedup).

## F\* scope

- File: `formal/fstar/RDF.Canonical.fst` only.
- Edits: ≤ 100 LoC.
- No extract / compile (Yod3 has the F\* lock on Parquet).
- F\*-verify locally only.

## Validation plan

`make verify` on `RDF.Canonical.fst`. Verbose runner re-run is deferred
until Yod3 releases the lock and a fresh extract/compile cycle.
