# Block engine Tuesday OKRs — 2026-09-01

## Objective

Turn the optimized persistent three-pattern query path from a working,
regression-tested implementation into a proof-connected and reproducibly
measured Lean 4 storage-engine slice.

Both sides of each refinement are Lean 4.  The **reference Lean evaluator** is
the simple executable SPARQL semantics.  The **optimized Lean physical-plan
algorithm** uses predicate blocks, subject indexes, and direct binding
construction.  “Pure” is reserved for deterministic in-memory code without
file-I/O, Merkle, or harness effects; it does not distinguish Lean from
non-Lean code.

## Key results

1. **Close the two immediate semantic gaps.**
   - Exact fast-`DISTINCT` list refinement is landed at `a32358688`.
   - First-driver three-predicate shared-subject refinement is landed at
     `99ebdb337`: exact rows, duplicates, and order against `evalBgp`.
   - Complete the production HashMap bucket-order and alternate-smallest-driver
     bag-refinement theorem.

2. **Advance the verified persistence bridge.**
   - Give the executable HashMap finisher a small reusable Lean core boundary,
     rather than leaving proof-relevant code private inside an I/O harness.
   - Prove that its per-subject buckets retain every object occurrence.
   - State and, if tractable today, prove the next agreement theorem from
     Merkle-verified SRI2-selected rows to logical predicate fragments.
   - Admit no `sorry`, custom `axiom`, `partial def`, or `native_decide` shortcut.

3. **Broaden evidence without a costly corpus download.**
   - Fable owns one deterministic heterogeneous fixture covering shared terms,
     predicate skew, language and typed literals, absent lookups, and
     update → compaction → activation → re-query.
   - Add explicit-only corpus retrieval/profile tooling with URL, timestamp,
     licence/provenance, SHA-256, bytes, parser-measured statement count, and
     workload metadata.
   - Do not treat the unprovenanced local UK Parliament copy as reproducible,
     and do not download a corpus over 100 MiB today without a pinned source
     and disk estimate.

4. **Make performance claims measurable.**
   - Re-run focused persistent regressions and the selected official SPARQL
     test cases exercised through the persisted path after runtime changes.
   - Record corpus, query, execution mode, cold/warm state, logical bytes,
     fetched Merkle-chunk bytes, rows, and elapsed time together.
   - Drive at least one evidenced cost downward if a semantics-preserving,
     benchmarkable change is identified; otherwise record the measured bound
     and the next experiment rather than claiming an optimization.

5. **Leave a durable handoff.**
   - Commit and push coherent verified increments without staging unrelated
     worktree changes.
   - Record decisions and measurements in dated worknotes, and update a skill
     only when a reusable operational or Lean-proof lesson has emerged.
   - Obtain Fable's independent review of the DISTINCT proof and terminology,
     and integrate or explicitly disposition every material finding.

## Guardrails and stretch result

PostgreSQL and TiKV remain optional hosts, not today's critical path; local
immutable files and existing Lean tooling are enough for this assurance rung.
Use subagents only for sharply bounded checks with clear payoff.  Preserve
unrelated FoafMixer and user work.  Do not turn “passes current tests” into a
standards or SOTA claim.

The stretch result is an end-to-end theorem chain for the admitted query shape:

```text
Merkle-verified IBK3/SRI2 rows
        → predicate fragments
        → optimized Lean physical-plan solutions
        → reference Lean evalBgp solutions
```

Order-sensitive modifiers remain on the reference route until their physical
ordering contract is stated explicitly.

## Alpha format-readiness decision

The main current family is suitable for an explicitly experimental MVP/alpha,
but it is not yet a fully specified or long-term-stable storage standard.  The
current writable generation is:

```text
SBM6 manifest
  -> predicate-local IBK3 block
       -> embedded PTD1 local-ID-to-RDF-term dictionary
  -> SRI2 subject-ID-to-row-offset sidecar
  -> TLI1 RDF-term-to-local-ID sidecar
  -> OLI2 object-ID-to-row-offset sidecar

DLOG (DLB1 batches of DLE1 operations) + CEP1 compacted epoch
CURRENT -> one admitted immutable generation
```

This is strong enough for alpha code because the bytes are versioned, writers
and strict decoders exist in Lean, malformed framing and checksums are
rejected, artifacts are bound by SHA-256 and fixed-chunk Merkle commitments,
activation checks the sidecar relations against their target IBK3 block, and
the publish/update/compact/reopen/query lifecycle has repeatable executable
regressions.  Local IDs are intentionally scoped to one IBK3 artifact; TLI1
is the translation boundary.

The alpha compatibility rule is: do not silently reinterpret bytes under an
existing magic/version.  A byte-layout or denotation change gets a new format
version.  Earlier versions may remain readable while useful, but there is no
installed base that requires preserving every prototype writer.

It is not yet honest to call the family fully specified because:

- IBK3, PTD1, SRI2, TLI1/OLI2, SBM6, and the Merkle range layer do not yet
  have general `decode (encode x)` or denotation-preservation theorems.  Their
  current assurance is chiefly strict executable admission, fixtures,
  corruption tests, and cross-artifact activation checks.  BLK0 has
  conditional scan-to-SPARQL theorems, IBK2 has several open/range soundness
  theorems, and DLOG/CEP1 plus merge-on-read have materially stronger theorem
  coverage; proof depth is therefore uneven.
- The inherited term codec still refuses RDF 1.2 triple terms and directional
  literals, and physical IDs/row counts are currently bounded by 32-bit wire
  fields.  Those are explicit alpha limits, not accidental support claims.
- There is not yet one standalone normative byte-format document with portable
  golden vectors, a compatibility/migration policy, and an independent-reader
  test across native Lean, WASM, PostgreSQL, and TiKV hosts.
- OLI2 deliberately reuses SRI2's generic `(local ID, row offset)` codec; its
  object role is supplied and checked by SBM6 activation.  That role contract
  should receive an explicit theorem before a beta freeze.

The practical beta gate is therefore: prove the current codecs' round-trip or
denotation properties, connect verified selected ranges to SPARQL denotation,
publish portable golden vectors and the normative layout, settle the RDF 1.2
term encoding, and demonstrate the same bytes in at least two host paths.

## “W3C” terminology

“W3C” is an origin or evidence qualifier here, never a synonym for
“Factoidal”, “verified”, or “certified”.  Use these phrases precisely:

- **W3C-defined semantics** or **W3C Recommendation/Working Draft**: a Lean
  definition is intended to model a cited standards clause.
- **official W3C test case/corpus**: the input and expected result come from a
  vendored W3C test suite.  Where the manifest records a formal approval
  status, say **manifest-marked Approved** rather than merely “approved”.
- **selected official SPARQL test cases through the persisted path**: the
  existing Shardborough smoke packs selected official Turtle fixtures into
  IBK3/SBM6 and runs their original query text against those files.  This is
  useful cross-layer regression evidence, not a complete conformance run.
- **W3C suite result**: reserve this for a manifest-driven suite execution with
  the suite's comparison rules and an explicit pass/fail/skip/unsupported
  census.  It is still not W3C certification.

Avoid the recent shorthand “W3C disk gate”: it can sound like a W3C storage
format or certification.  The storage formats are Factoidal/Shardborough
formats; W3C material is being used as standards-derived test data and expected
query results.

## Umbrella specification and semantic scope

The repository previously had no single specification for the complete active
format family. Architecture parts, dated implementation notes, the Lean codec
modules, and storage skills each held part of the contract. The new alpha
umbrella draft is `docs/shardborough-storage-spec.md`; it registers the
IBK/PTD/index/SBM/Merkle and durable-update formats and states which Lean
definitions currently own their executable layouts.

The audit also found a semantic-control-plane gap. IBK3 row bytes are usefully
vocabulary-neutral, but SBM6 records no named-graph scope, asserted/derived
role, entailment profile, schema/rules identity, or trust policy. Its physical
planner selects exact predicate IRIs only. Existing Lean RDFS/OWL code defines
and proves `rdfs:subPropertyOf` rules, but no persisted Shardborough index uses
those relationships to select subordinate predicate blocks.

The umbrella draft therefore requires an open, content-addressed semantic
context rather than a closed enumeration of favoured standards. It specifies a
future predicate-entailment map bound to source, schema/rules, regime, graph
scope, and trust identities. Superproperty scans must deduplicate identical
inferred triples before exposing SPARQL bag multiplicity. Absence or mismatch
of the map means complete fallback, never a false-negative shortcut. The
implementation and proof work is tracked in
[issue #636](https://github.com/danbri/factoidal/issues/636).

## Browsable specification

`docs/shardborough-storage-spec.md` remains the source document. Alpha draft
0.2 begins with the system's purpose, publication/query/update lifecycle,
deployment profiles, adoption scope, and current implementation limits. The
semantic index proposals are explicitly optional extensions. Eleventy renders
the Markdown with `docs/_includes/spec.njk` as a responsive technical
specification page at `/factoidal/shardborough-storage-spec/`. The page has
stable heading links, a generated table of contents, source and issue links,
print styling, and an explicit statement that it is a Factoidal draft rather
than a W3C publication.

The specification also records an optional endpoint-type summary for early
block rejection. Bloom-filter keys can distinguish subject/object roles and
quantized prevalence claims such as `at_least_1`, `at_least_half`, and `all`.
Negative results provide safe bounds when construction and context are
verified; positive results remain probabilistic. Materialized supertypes are
permitted only under a named graph, schema/rules, entailment, and trust
context.
