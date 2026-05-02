# Where LLMs and deep learning could (and shouldn't) live in Factoidal

**Status:** brainstorm, 2026-05-02
**Trigger:** user prompt — "think about whether the query planner has scope
for LLM to play any role, or deep learning a role in compressing the
on-disk storage"
**Constraint:** Factoidal's product is the F\*-verified spec. Any ML role
must keep the verified core verified. Anything that affects *what answer
the user gets* must remain provably correct; anything that affects *which
correct path we took to compute it* is fair game.

## The split that makes this tractable

A SPARQL engine has two kinds of decisions:

- **Soundness-affecting**: parse, algebra, BGP matching, joins, aggregates,
  RDF semantics. Wrong = wrong answer. Stays in F\*.
- **Performance-affecting**: which order to join in, which index to consult
  first, how aggressively to cache, how to lay bytes on disk. Wrong =
  slower answer. **An ML oracle that lies here costs latency, never
  correctness.**

That split is also where ML earns its keep in classical query planners
(Microsoft Neo, MIT Bao, Postgres-pglearn). The verified spec acts as a
guardrail: an ML cost-model that hallucinates an estimate of 0 still has
to walk the tuples to *prove* that claim against the F\*-verified search
function. The worst case is "we picked a bad order and ran slowly", not
"we returned 3 wrong rows."

This is unusually good ground for "AI used responsibly" — the exposure
surface is bounded by construction.

## Where LLMs could play in the planner

Five candidate slots, ranked by leverage / risk:

### 1. Cardinality estimation hints from natural-language schema (HIGH leverage, LOW risk)

The bucket-build cost in the lifesci demo (135s, see
`2026-05-01-perf-fast-path-vs-load.md`) is upstream of the planner —
ML can't fix that. But once we have a fast in-memory store, the
planner needs cardinality estimates for join ordering. Today the
estimate is `cottas_ondisk_estimate` walking presence bitmaps; for
in-memory it'll be even more crude.

An LLM with the schema vocabulary in context (e.g. "this is the UK
Parliament KG, properties include `:hasMember`, `:hasConstituency`,
`:isMemberOf`...") can produce surprisingly good order-of-magnitude
guesses for `?x :hasMember ?y` selectivity — better than `count(*)`
divided by `count(distinct predicates)`, often by 10×. This is the
classical "LLM as cheap world-model" play.

**Plumbing**: a side oracle called once at planner-init time per
schema. Cache the estimates as a JSON sidecar. The planner consults
it the way it consults presence bitmaps — read-only structured data.
No LLM call per query.

**Risk**: low. The estimate flows into the cost model only;
correctness is the F\*-verified search.

### 2. Query rewrites / equivalence (MEDIUM leverage, MEDIUM risk)

OWL.QueryRewrite already does Datalog-sound rewrites in F\*. Some
rewrites are heuristic — should `?x rdfs:subClassOf+ owl:Thing` be
expanded eagerly or via the closure path? — and an LLM can suggest
candidates ("for THIS query shape against THIS schema, expanding is
cheaper because owl:Thing has no children in this KG").

Critically, every LLM-suggested rewrite must be **verified equivalent
by the F\* algebra** before adoption — exactly the guardrail pattern
above. The LLM proposes; the verifier disposes. Cost-of-LLM-being-
wrong = wasted compile time, not wrong rows.

**Risk**: medium because verification of arbitrary rewrites is
non-trivial. Probably restrict the LLM to picking among a fixed set
of F\*-verified equivalence laws.

### 3. Natural-language → SPARQL (HIGH leverage, but a separate product surface)

Obvious frontier model use. Already exists in the wild (text2sparql,
LLM-augmented endpoints). For Factoidal it would slot in as a
*preprocessor*, not a planner — translate "MPs from Bristol" into
SPARQL and hand the SPARQL to the verified engine. The LLM never
sees the data, only the schema. Same guardrail.

**Risk**: low for soundness, high for confusion (user thinks the
NL→SPARQL was right when it wasn't). Mitigate by always showing the
generated SPARQL.

### 4. Adaptive operator scheduling (LOW leverage at current scale)

Bao-style "pick the operator implementation at runtime based on
incoming row counts" is a real win at TB scale; at 50k–10M-triple
scale our F\*-verified operators are simple enough that the win is
small relative to the engineering cost.

**Verdict**: not now.

### 5. LLM as the planner itself (NO)

Letting an LLM generate the join order from scratch loses the
verifiable cost model. Use it as an oracle that *suggests a candidate
order* which the F\*-verified cost model then validates against an
estimator floor. Direct planner-replacement is wrong on this codebase.

## Where deep learning could play on the storage

The COTTAS on-disk format is parquet-derived: dictionary-encoded
columns, presence bitmaps, compound (p,o) bitmap, page cache.
"Compress the on-disk store" can mean two very different things:

### A. Lossless byte-level codec (LOW novelty, REAL win)

Parquet today: RLE_DICTIONARY, ZSTD on data pages. Modern
ML-derived codecs:
- **Learned entropy coding** (BPE-like for IRIs): IRIs in a KG
  follow a Zipfian distribution and share long namespace prefixes.
  A small trained dictionary (per-corpus, ~10k entries) can squeeze
  the term dictionary 2-3× tighter than the current RLE
  approach. Reader path: identical (still byte→string lookup).

  This is the most boring and most useful place for ML on storage.

- **Neural compressors** (NNCP, TRACE) for the data pages: 5-15%
  better than ZSTD on RDF, but at the cost of ML inference on
  every page read. Not worth it — we're I/O-light, latency is in
  index walks.

### B. Learned indexes (HIGHER novelty, more interesting)

The classical "RMI" (recursive model index, Kraska 2018): replace a
B-tree with a small neural model that predicts where a key lives,
then a bounded local search confirms. For RDF:

- The S/P/O/G dictionaries are sorted strings. A learned index over
  IRIs can give O(1) average-case lookup vs O(log n) binary search,
  AND the model is small enough to keep in RAM.
- Same for the predicate-presence bitmaps: a tiny model "given a
  predicate IRI, predict which row groups contain it" is
  literally what the bitmap does today; a learned variant can be
  10-100× smaller for sparse predicates.

The verifiability story holds: the ML predicts a *position*, the
F\*-verified search function reads the byte at that position and
verifies it matches the query key. Wrong prediction = retry with
binary search. Cost = latency, never correctness.

### C. Latent-space embeddings (NO, for this codebase)

"Embed every triple as a 128-dim vector and do similarity search"
is a different product (vector DB, GraphML). It doesn't compress
the underlying RDF; it replaces it. Out of scope for a verified
SPARQL engine.

### D. Auto-encoder for triple sets (RESEARCH)

Train a small auto-encoder per named graph; store the latent
representation; reconstruct triples on read. Promising for write-
once / read-rarely archive graphs. Hard to verify the
reconstruction is exact (the whole point is lossy in latent
space). Only viable for "approximately correct" use cases — which
is *not* SPARQL semantics. Skip.

## Concrete next-step prototypes (in priority order)

Each scoped to one agent-run, each measurable.

### P1. Schema-aware cardinality oracle (LLM, sidecar)

- Input: COTTAS store + RDF schema files.
- Prompt the model with schema vocabulary, ask for selectivity
  estimates per (predicate, position) pair.
- Write a JSON sidecar `<store>.cardinality.json`.
- Wire the planner's `cottas_ondisk_estimate` to consult the sidecar
  as a low-priority hint (override only when presence-bitmap is
  unavailable).
- Measure: planner picks correct join order on Q03 (the
  geo:wktLiteral rdf:type case from `pe5-explain-mode.md`) without
  needing the slow Mem5 walk.

### P2. Learned IRI dictionary codec (DL, on-disk)

- Train a tiny BPE-style tokeniser over the IRI dictionary of a
  representative corpus (UK Parliament + DBpedia + lifesci).
- Add a new dictionary-page encoding alongside RLE_DICTIONARY:
  `LEARNED_IRI`. Reader is F\*-verified (token stream → string is
  pure functional).
- Measure: total bytes on disk, decode latency.

### P3. RMI for predicate dictionary (DL, in-memory)

- Replace the binary search inside `cottas_ondisk_lookup_predicate`
  with a small two-level RMI. Bounded fallback if the model
  mispredicts.
- F\* spec stays the same (the function still returns the same
  string); only the *implementation* gains the model.
- Measure: per-query overhead at planner time.

### P4. NL→SPARQL surface (LLM, product feature)

- Standalone web demo widget. Users type English; box shows
  generated SPARQL; they edit / accept; verified engine runs it.
- Decoupled from the engine — purely a UX upgrade.

## What this enables for "no black box"

If the cardinality oracle (P1) writes a JSON sidecar, and the
planner emits a `chosen_estimate_source` per pattern (one of:
presence-bitmap, mem5-fastpath, llm-sidecar, default-1), then the
`--explain` output and the timing trace can show *which oracle
the planner trusted* on every triple pattern. That's the inverse
of the worry — making ML's role transparent rather than opaque.

The same goes for the RMI: if a lookup falls back to binary search,
the trace says so, with the predicted-vs-actual gap. Every ML
contribution to a query's path becomes inspectable.

## Open questions

1. **Eval harness**: how do we measure "planner picked a better
   order" without a ground-truth join-order benchmark? Probably
   hand-curated golden plans for ~30 representative queries.
2. **Where does the LLM run?** For P1 a one-shot at corpus-load
   time is fine (offline). For P4 it has to be online; user runs
   their own model or talks to a hosted endpoint they trust.
3. **Verification story for learned indexes**: the F\* spec describes
   *what the function returns*. The RMI is an implementation choice;
   the spec doesn't care. But the *runtime guarantee* "model + binary
   search fallback always returns the same string as plain binary
   search" needs to be testable, ideally as an F\* refinement.

## Recommendation

Start with **P1 (LLM cardinality sidecar)** as the lowest-risk highest-
leverage experiment. It's offline, verifiable-by-falsification (we can
diff the LLM estimate against the actual count once the query runs and
adjust), and it slots cleanly into the existing observability
infrastructure planned for tonight (the per-stage timing will tell us
immediately whether the join order changed).

P2 (learned IRI codec) is a credible second experiment — concrete
bytes-on-disk win, no impact on query semantics.

Skip P3 and P4 until P1 has been measured.
