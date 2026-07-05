# Fulltext SPARQL extensions, Solr/Lucene-adjacent — design

**Date:** 2026-07-05.
**Status:** design only. No F\* module, no OCaml glue, no test files
land in this slice. Owner priority: "some fulltext sparql extensions
close to solr."

## 0. What "Solr-like" means here

Solr/Lucene fulltext search over RDF literals is a property-function
extension: a magic predicate embedded in a BGP triple pattern that
means "search," not "match this exact triple." All three connectors
in §1 converge on that shape despite different vocabularies. The
question is not "should we add an index" — COTTAS already has sidecar
precedent
([`graph-bloom-sidecars.md`](graph-bloom-sidecars.md),
[`2026-04-26-nun4-compound-po-bitmap-design.md`](2026-04-26-nun4-compound-po-bitmap-design.md))
— it is what predicate vocabulary users write, and where F\* draws
the line between match semantics (verified) and index mechanics
(host).

## 1. Precedents

**Jena-text** wires a Lucene/Solr index behind a magic predicate in
`http://jena.apache.org/text#`:

```sparql
PREFIX text: <http://jena.apache.org/text#>
SELECT ?s ?score ?literal WHERE {
  (?s ?score ?literal) text:query (rdfs:label "solar panel" 10) .
}
```

The 4-arity form binds subject, score, and matched literal in one
call; a 2-arity form (`?s text:query "term"`) skips score/literal
capture. The object argument is a bare string (default field) or a
`(property "query" limit)` tuple. Per-field indexes are declared in
assembler config, not the query; analysis (tokenizer/stemmer/
stopwords) is a Lucene `Analyzer` chosen per field at index-build
time, invisible to the query language. `text:score` is not a separate
predicate — it is a positional binding inside `text:query`.

**Virtuoso `bif:contains`** takes a single string in a small boolean
mini-language (`'solar' AND 'panel'`, `NEAR`, quoted phrases); ranking
needs a second triple, `?s bif:score ?sc`. Also exposes narrower verbs
(`bif:starts_with`, `bif:xcontains`) instead of one verb with
structured arguments.

**GraphDB / Lucene connectors** are the most Solr-native precedent by
name but architecturally the furthest from a query-time property
function: index definition is a SPARQL Update side effect against a
control graph (triggers an out-of-band build), and query is a
`graphdb:query` vocabulary against a named connector instance —
declare-then-query, not jena-text's assembler-config model.

**SPARQL 1.2** has not adopted a standard fulltext vocabulary; every
engine (Jena, Virtuoso, GraphDB, Stardog, Blazegraph) has its own
namespace. No W3C recommendation, no W3C test manifest — why §5
proposes a local suite instead of a W3C import (rule #6 applies only
when W3C files exist).

**Recommendation: mimic jena-text's vocabulary.** Adopt the `text:`
namespace and `text:query`'s argument shape. Reasons: (1) it is the
vocabulary most Apache-ecosystem SPARQL users already know, and
`tools/jena_arq_*_probe.sh` already differentially tests against Jena
(§5), so a vocabulary-identical probe is possible, not just a
results-identical one; (2) one verb with a structured argument scales
to per-field search and score/limit without new predicates
(`text:score`, `text:limit`), keeping the F\* AST to one case; (3) the
argument tuple maps directly onto an F\* record (§2.2). Reject
Virtuoso's boolean mini-language as the only surface — a
config-free `AND`/`OR`/`NEAR` parser is extra spec surface on top of
tokenization — but keep the idea as a slice-3 addition inside the
`text:query` object argument (§6), not a competing vocabulary. Reject
GraphDB's declare-then-query model for v1: it needs an Update-side
control vocabulary before any query lands; revisit only if factoidal
needs multiple simultaneous named indexes per predicate.

## 2. Fit with the iron rules

### 2.1 Backend concern vs. F\* concern

Per rule #11 and the `ocaml-boundary` taxonomy, the **index structure
and tokenizer/analyzer implementation** are ASSUME-HOST — same class
as `assume val regex_match` at
`formal/fstar/SPARQL11.Algebra.fst:1093`
([`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md)
§"Regex"). Building an inverted index, running Porter/Snowball
stemming, and doing ranking arithmetic over a corpus-scale postings
list are not things F\* needs to own byte-for-byte: "verifying it
ourselves is not just hard but wrong," because tokenization rules are
externally defined per-language linguistics, not RDF/SPARQL semantics.

What **must** live in F\* so results are testable:

- **The `text:query` AST** — triple-pattern shape, object-argument
  grammar (string vs. tuple), composition with joins/FILTER/OPTIONAL.
- **The match predicate over an abstract token index** — given two
  already-tokenized token lists (query, candidate literal), whether
  they match under a declared mode (all-tokens / any-token / phrase).
  A pure function over token lists — the property-test surface.
- **The tokenization contract**, not necessarily the algorithm: a
  tokenizer of type `string -> list string` must be deterministic,
  total, and case-folding must be declared rather than silent. A
  default tokenizer (whitespace/punctuation split + lowercase) lives
  entirely in F\* for slice 1; a Lucene-grade analyzer is a different
  realisation of the same contract, wired through an ASSUME-HOST seam
  in slice 3.
- **Scoring monotonicity** — score is a pure `Tot` function of
  `(term frequency, document frequency, document length)` once index
  statistics are passed in as data. The property to test is
  monotonicity (more matching tokens never lowers score; the BM25
  length-normalization property), not bit-exact parity with Lucene's
  float arithmetic.
- **Ranking tie-break determinism** — equal scores must resolve via a
  deterministic total order (subject IRI lexicographic), so regression
  output is stable rather than dependent on host postings order.

### 2.2 Proposed module split

**`SPARQL.FullText.fst`** (new, spec side — mirrors
`RDF.CottasStore.PresenceBitmap.fst`'s "header/layout/`Tot`
functions, verified separately from the writer" pattern):

```fstar
module SPARQL.FullText

// text:query argument tuple. ftq_field = None is jena-text's bare-string form.
noeq type fulltext_query = {
  ftq_field : option wf_iri;
  ftq_terms : string;           // tokenized per §2.1
  ftq_limit : option nat;
}

// Abstract token-index seam a backend realises; F* requires it be a
// pure function of its inputs (Tot), not that it be efficient.
noeq type token_index_lookup = {
  til_candidates :
    option wf_iri -> list string -> list (subject & rdf_term & nat & nat)
    // (subject, matched literal, term_frequency, doc_length)
}

let default_tokenizer (s : string) : Tot (list string) = (* whitespace/punct split + lowercase *)
let match_tokens (query_tokens candidate_tokens : list string) : Tot bool = (* all-tokens mode, slice 1 *)
let score_bm25 (tf doc_len avg_doc_len df n_docs : nat) : Tot int = (* monotonicity is the tested property *)
let rank_results (rows : list (subject & rdf_term & int)) : Tot (list (subject & rdf_term & int)) =
  (* score desc, subject IRI asc tie-break *)
```

**`bin/`-side index build** (consumer, not verified library):
recommend a pure-F\* default tokenizer for slice 1 (zero new `assume
val`s, zero new glue-audit surface) and one ASSUME-HOST seam for
slice-3 analyzers — `assume val analyze_text : wf_iri -> string ->
list string -> ML (list string)` (field IRI selects the registered
analyzer), glue patch under
`minimal_regrettable_glue_code_each_with_an_open_issue/` per Iron Rule
#3, same class as `regex_match`. Rejected: a pure-F\* stemmer — would
require formalising per-language morphology, out of scope, and still
needs per-language data tables no different in kind from a host
call-out. The postings-list storage itself (whatever backs
`til_candidates`) is `bin/`-side per rule #11's consumer-tools clause
— a companion file next to a COTTAS chunk (§4), same status as
`tools/corpus_pipeline.py`'s sidecar writers; its byte layout, if ever
memory-mapped directly, follows the Option-B hash-witness pattern
([`2026-05-09-large-writer-byte-format-options.md`](2026-05-09-large-writer-byte-format-options.md))
like every other COTTAS sidecar — a slice-2-or-later concern.

## 3. Property-function dispatch point

Two BGP-evaluation paths exist today and both need the same hook:

- **In-memory path:** `eval_single_tp_store`
  ([`formal/fstar/SPARQL11.Algebra.fst:1768`](../../formal/fstar/SPARQL11.Algebra.fst)),
  called from `eval_bgp_store_from_mu_fuel` (`:1801`), called from
  `eval_pattern_store`'s `GP_BGP bgp -> eval_bgp_store bgp gs` arm
  (`:2119`).
- **Backend-neutral path** (COTTAS-on-disk/HDT/indexed — what the
  CLI/HTTP binaries actually exercise): `eval_single_tp_backend`
  ([`formal/fstar/SPARQL11.Store.fst:305`](../../formal/fstar/SPARQL11.Store.fst)),
  called from `eval_bgp_backend_from_mu_fuel` (`:387`), called from
  `eval_pattern_backend`'s `GP_BGP bgp -> eval_bgp_backend bgp gb` arm
  (`:629`).

Both have the same shape today:

```fstar
let eval_single_tp_backend (tp : triple_pattern) (gb : graph_backend) (mu : solution_mapping)
  : solution_sequence =
  let bound = { bs = ...; bp = ...; bo = ... } in
  let candidates = backend_search gb bound in
  list_filter_map (fun t -> tp_match tp t mu) candidates
```

`text:query` hooks in **before** `backend_search`/`tp_match` in each
function: if `tp.tp_p` is `PT_IRI` equal to the `text:query` constant,
parse the pattern's subject/object shape into a `fulltext_query`
(§2.2) and dispatch to `SPARQL.FullText`'s match/score/rank functions
against a `token_index_lookup` threaded alongside the backend (either
a new field, or a wrapping constructor `GB_WithFullTextIndex of
graph_backend * token_index_lookup` — open decision 2); otherwise fall
through to today's path unchanged. This mirrors how `GP_Service`/
`GP_ServiceVar` are recognised structurally before ordinary BGP
evaluation (`SPARQL11.Store.fst:683`–`690`), except `text:query` stays
a triple pattern (not a distinct `group_graph_pattern` constructor) so
it composes with joins/filters like jena-text's does.

`pattern_predicate_hint` (`SPARQL11.Store.fst:342`) and the cost
estimator `estimate_tp_backend_mu` (`SPARQL11.Store.fst:316`) both
need a `text:query`-aware arm so the planner estimates fulltext
selectivity instead of treating it as an unbound-pattern scan — a
slice-2 refinement (§6); slice 1 can hardcode source-order evaluation
and stay correct, just not planner-optimal.

## 4. Storage

COTTAS-on-Parquet is the only on-disk quadstore backend today
(`GB_CottasOnDisk`, `SPARQL11.Store.fst:33`); the fulltext index is a
**sibling artifact next to a COTTAS chunk**, not a change to the
four-column `s,p,o,g` contract
([`docs/cottas-format-v1.md`](../cottas-format-v1.md)) — same posture
as the presence bitmaps and Bloom sidecars already living alongside
`.cottas` files: `data.fulltext.<field>.idx` per indexed predicate,
built by a producer-side pass (analogous to
`tools/graph_bloom_rollup.py`) that reads the literal objects, tokenizes,
and writes postings.

**Durable-update plan.** COTTAS files are write-once today (produced
by `tools/corpus_pipeline.py`), and
[`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
§2.2 flags update-heavy workloads as the weak point of any index
layered on it — a fulltext postings index shares CS-clustering's
failure mode: inserting a literal must append to or invalidate
postings, and full-rebuild-per-update does not scale. Ranked options:
(1) **rebuild-on-batch** (recommended for slice 1/2) — treat the
index like the Bloom/presence sidecars, rebuilt whenever the pipeline
reprocesses a chunk; matches today's write-once posture, no new
durability machinery; (2) **incremental append log** (slice 3+, only
if live-update fulltext is actually needed) — a per-chunk delta of
`(subject, literal, op)` merged against base postings at query time,
the OSTRICH/COBRA idea for versioned RDF (storage doc §3.1); adds a
merge step per query, so do not build until slice 1/2 prove demand —
none of the storage doc's own E1/E2/E3 experiments address update
latency, suggesting read-path selectivity is the current bottleneck.

**Where RDFC-1.0 canonical hashes help.** Per the storage-strategies
doc §3.1, a per-graph canonical hash survives blank-node relabelling
and is a cache key. Applied here: `(canonical dataset hash, field
IRI, tokenizer version)` keys the fulltext-index rebuild decision the
same way it keys the proposed query-result cache — a corpus reload
that re-serialises the same graph under different blank-node labels
should not force a postings rebuild. Reuses the storage doc's E3
sidecar (`graph.c14n.sha256`) rather than a second hashing scheme, and
inherits E3's caveat: no hash, no skip-rebuild decision, when an HFDQ
tie is detected, since HNDQ is not yet implemented in
[`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst).

## 5. Test strategy

No W3C manifest exists for fulltext SPARQL (§1), so this is a local
suite following the `tests/local/*_regressions.sh` +
`tests/local/data/` convention (e.g.
[`tests/local/cottas_corpus_regressions.sh`](../../tests/local/cottas_corpus_regressions.sh)):

- **`fulltext_exact_match_regressions.sh`** — small N-Quads fixture
  (`tests/local/data/fulltext_sample.nq`, `cottas_sample.nq`-sized),
  single-token and multi-token-AND queries, expected subject sets
  diffed against a checked-in oracle.
- **`fulltext_stemming_off_baseline_regressions.sh`** — confirms the
  default tokenizer does **not** stem (`"panels"` misses a query for
  `"panel"`), so slice 3's analyzer upgrade has a documented
  before/after rather than a silent behavior change.
- **`fulltext_scoring_order_regressions.sh`** — literals engineered
  with known term-frequency/length differences; asserts `rank_results`
  order and that ties break by subject IRI, not arrival order.
- **`fulltext_lang_tag_regressions.sh`** — `@en`/`@fr`/untagged
  literals; slice 1/2 assert tag-blind matching, with an explicit case
  for what a language-scoped query does (open decision 5).

**Differential probe against Jena.** Following
`tools/jena_arq_basic_probe.sh`/`jena_arq_graph_probe.sh`'s pattern
(reuse a local Jena/ARQ install, run the same query against the same
data, diff results): a new `tools/jena_text_probe.sh` builds a small
Jena TDB2 dataset with `jena-text` Lucene indexing on one predicate,
runs identical `text:query` queries against both engines over the
same fixture, and diffs subject sets separately from score order —
bit-exact BM25 parity is not a goal (§2.1), subject-set parity is.
Informative only because the vocabulary was copied verbatim (§1).

## 6. Phasing

Each slice lands as one or a few commit-sized PRs per anti-pattern
#23, with a measured gate before the next slice.

**Slice 1 — exact/token match, no scoring.** `SPARQL.FullText.fst`:
`fulltext_query`, `default_tokenizer`, `match_tokens` (all-tokens
mode only) — no `score_bm25`/`rank_results` yet, results in
documented dataset order with no ranking claim. Dispatch wiring at
both hooks (§3); index is in-memory only (linear scan +
tokenize-per-literal at query time), no on-disk companion file — this
proves the match-semantics contract before any storage commitment.
Gate: `fulltext_exact_match_regressions.sh` and
`fulltext_stemming_off_baseline_regressions.sh` pass; W3C SPARQL
suite stays at 631 pass, 0 fail (out of 631, per
[`docs/claude-rules/current-state.md`](../claude-rules/current-state.md))
— additive, not a regression risk to existing BGP evaluation.

**Slice 2 — BM25-ish scoring, deterministic.** `score_bm25` and
`rank_results` land with monotonicity stated and property-tested (an
F\* proof is the stretch goal, a regression test is the floor). On-disk
companion file (`data.fulltext.<field>.idx`) introduced per §4,
rebuild-on-batch, Option-B hash-witness CI. `estimate_tp_backend_mu`/
`pattern_predicate_hint` gain a `text:query` arm. Gate:
`fulltext_scoring_order_regressions.sh` passes; `jena_text_probe.sh`
shows subject-set parity; wall-time on the ukparliament-scale fixture
measured and labelled per `perf-benchmarking`, not asserted as a win
without a number.

**Slice 3 — analyzers/lang.** `assume val analyze_text` seam + one
glue patch (e.g. OCaml Snowball binding) tied to a new open issue per
Iron Rule #3. Per-field analyzer selection (jena-text's model) and
language-tag-aware tokenization — the point where open decision 5
must be resolved. Gate: `fulltext_lang_tag_regressions.sh` (updated
for tag-dispatch) passes; `fulltext_stemming_off_baseline_regressions.sh`
is kept as the regression fixture for the no-analyzer-configured
case, not deleted, so slice 1's contract stays checkable.

## 7. Open decisions

1. **Property function IRI.** Reuse `http://jena.apache.org/text#query`
   verbatim (maximizes probe/tool compatibility) vs. a
   factoidal-local namespace to avoid implying Jena compatibility not
   fully delivered (slice 1 gives subject-set semantics only, not
   Lucene-parity scoring). Leaning toward reusing the IRI verbatim —
   the argument shape is also being copied, and a different IRI with
   the same shape is the confusing middle ground.
2. **`GB_WithFullTextIndex` vs. a field on every `graph_backend`
   constructor.** The wrapping constructor (§3) composes better with
   `GB_Union` but needs `backend_search`/`backend_estimate` to look
   through it for non-fulltext patterns; needs a concrete sketch
   against the real `graph_backend` match arms before slice 1 starts.
3. **Match mode default.** Multi-word `text:query` strings: implicit
   AND vs. implicit OR (Lucene's actual default, which most jena-text
   users don't realize) vs. phrase. Recommend AND-by-default with an
   explicit OR/phrase syntax as a slice-3 mini-language addition,
   rather than silently matching Lucene's query-parser default.
4. **LIMIT pushdown interaction.** Whether `text:query` composes with
   the existing LIMIT-pushdown fast path
   (`backend_search_limited`, `SPARQL11.Store.fst` near line 414) or
   always materializes full postings before ranking — slice 2's
   scoring needs the full candidate set to rank correctly absent a
   priority-queue design. Decide whether this blocks pushdown for
   fulltext-containing queries specifically, and document the perf
   implication rather than silently losing the fast path.
5. **Language-tag interaction before slice 3.** Whether slice 3's
   tag-dispatch is opt-in per query (a tagged variant of `ftq_field`
   — jena-text has no such thing) or purely index-time configuration
   (matches jena-text; query stays tag-blind, only the field's
   declared-language analyzer is tag-aware). Recommend the latter for
   vocabulary compatibility.
6. **Where the index-build trigger lives.** §4 assumes the same
   producer-side pass as other COTTAS sidecars
   (`tools/corpus_pipeline.py`-adjacent), per rule #11's
   consumer-tools-belong-in-`bin/` clause. Whether that is a new
   `bin/fulltext-indexer` consumer or a flag on the existing pipeline
   is an implementation-slice decision; the module boundary (§2.2)
   assumes a separate consumer tool, not logic embedded in
   `factoidal-cli`.
