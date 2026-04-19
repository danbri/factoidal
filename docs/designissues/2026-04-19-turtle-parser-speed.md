# Turtle Parser Speed — Plan as of 2026-04-19

Companion to:
- [`turtle-parser-metrics.md`](turtle-parser-metrics.md) — the benchmark harness
- [`turtle-text-scanner.md`](turtle-text-scanner.md) — the scanner architecture
- [`parser-speed-status.md`](parser-speed-status.md) — broader parser-speed context
- CLAUDE.md §"Known Performance Issues" — the O(n²)-ish measurements

This note exists because the 2026-04-17 scanner integration helped, but the
Turtle parser is still ~50–240 triples/s depending on input shape, and the
35MB file still doesn't finish. That's ~250× away from usable, and the
current refactor trajectory (more scanner calls, more span plumbing)
will not close that gap. This doc says what would.

## Honest current state (audit 2026-04-19)

| Source input (1000 triples) | Wall time | Rate |
|---|---|---|
| `prefixed-1000.ttl` | 4.11 s | ~243/s |
| `fulliri-1000.ttl` | 19.35 s | ~52/s |
| `unicode-1000.ttl` | 8.19 s | ~122/s |
| `berlin-1000.ttl` (993 triples) | 14.37 s | ~69/s |

Numbers from `turtle-parser-metrics.md` (2026-04-17, post-scanner). The
median across these is still bracketed by the 40 triples/s figure in
CLAUDE.md pre-scanner — scanner integration bought ~2–4×, not an order
of magnitude.

Architecture today:
- `Parser.TurtleScanner.fst` (342 lines) — span-based tokenizer exists
  and is wired for prefixed names, IRI refs, short strings.
- `Parser.Turtle.fst` (1799 lines) — grammar + semantic layer; calls the
  scanner for the three token classes above, but the **document-level loop
  still manually scans whitespace/comments char-by-char** via
  `skip_ws_and_comments` (`Parser.Turtle.fst:297-311`) and `skip_to_eol`
  (`:285-294`), both using `String.index` per char.
- `Parser.Combinators.fst` (387 lines) — shared combinator foundation;
  `pstring` (`:70-73`) still calls `String.sub`/`String.index`.

## The three structural bottlenecks

These are the audit findings — none of the three is fixed yet, and until
at least two of them move the per-char constant will stay roughly where
it is.

### 1. Positions are `nat`, which extracts to `Z.t` (arbitrary-precision bignum)

Every `pos: nat` in Parser.Turtle.fst and Parser.TurtleScanner.fst becomes
a GMP `Z.t` after F\* → OCaml extraction. Every `pos + 1`, `pos < len`,
`len - pos`, `pos + 6` in the inner loop is a bignum operation routed
through `Zarith` and ultimately `libgmp`.

For a Turtle doc with N characters and K tokens, the parser does on the
order of `N * (lookahead factor)` position updates. Each one is a heap
allocation or at best a word-sized bignum operation. This is the single
biggest per-char tax.

**Estimated win if fixed:** 10–30×. Alone, this probably moves us from
~100 triples/s median to ~1–3k triples/s median.

**What "fixed" looks like:**
- Introduce a machine-int position type in F\*, e.g. `type pos_t = n:int{n >= 0}` with refinement, or a thin wrapper that extracts to OCaml `int` (not `Z.t`).
- Or: use `UInt32`/`Int32` from F\*'s machine-integer library, which already extracts to OCaml native ints.
- Either way, audit every arithmetic site for overflow risk (file size > 2^31 bytes is out of scope; files up to 2^62 bytes fit in `int`).

Watch out: a naive swap is verification-hostile. Many proof obligations
in the parser assume `pos >= 0`. A refined `int` type preserves this.
A plain unrefined `UInt32` will require re-proving bounds at every call.

### 2. Spans get extracted to substrings immediately

`Parser.TurtleScanner.fst` returns `{sp_start; sp_end}` spans. Good.
Parser.Turtle.fst then calls `span_to_string` (`Parser.Turtle.fst:384-388`)
the moment a span leaves the scanner:

```fstar
let span_to_string (input: string) (sp: span) : string =
  if sp.sp_end >= sp.sp_start && sp.sp_end <= String.length input then
    String.sub input sp.sp_start (sp.sp_end - sp.sp_start)
  else ""
```

Call sites: `:569` (prefix namespace), `:1072` (short-string literal),
and everywhere IRIs and prefixed names are consumed. So "span-based"
is only true *inside* the scanner; the grammar sees fresh allocated
substrings per token.

**Estimated win if fixed:** 3–10×, compounding with (1). Large IRIs hurt
most here — `fulliri-1000.ttl` runs at ~52/s, which is consistent with
per-token allocation dominating.

**What "fixed" looks like:**
- Keep terms as `{input: string; span: span}` through the grammar. Only
  materialize a `string` when (a) emitting the final `iri` / `literal` in
  the output triple, or (b) doing a semantic operation that requires a
  concrete string (prefix lookup, IRI resolution).
- Prefix table keyed by `(input, span)` with a comparison that walks the
  spans without allocating — or, alternatively, a small string-interning
  layer that looks up a span in a `(string, int_id)` table once per
  token without `String.sub`.
- Critically: relative IRI resolution (`remove_dot_segments_step`,
  `:147-180`, which `String.sub`s per path segment) must be re-expressed
  to operate on spans or on a pre-allocated normalized form.

### 3. O(n) list append in the grammar

`append_list` (`:42-46`) is plain `List.Tot.append`, O(|xs|). Call
sites in the grammar: `:1366`, `:1394`, `:1410`, `:1464`, `:1531`, `:1663`.
These merge object triples, predicate-object triples, and collection
triples per statement. For a statement with `k` objects in a comma list
this is O(k²); for a collection of length n it's O(n²).

The document-level `rev_prepend` (`:36-40`, used at `:1718, :1720`) only
saves the outermost level — once control descends into a statement
body, appends are back to O(n).

**Estimated win if fixed:** modest on small fixtures, disproportionate
on Berlin-shaped data (long predicate-object lists per subject). The
Berlin regression vs. prefixed-1000 (14.37s vs 4.11s with similar
triple counts) is consistent with per-statement complexity.

**What "fixed" looks like:**
- Replace inner-statement accumulations with reversed-list plumbing
  and a single final reversal. Same pattern as the document loop.
- Or: a difference-list / CPS accumulator for triples, avoiding
  reversal entirely.
- `collect_verb_objs` and the predicate-object-list folders are the
  hot-spot callers.

## Secondary bottlenecks (worth mentioning, smaller individually)

- `remove_dot_segments_step` (`Parser.Turtle.fst:147-180`) allocates
  per IRI-path segment. Every relative IRI object pays this. Folded
  into bottleneck 2 once spans reach IRI resolution.
- `unescape_pn_local_fuel` (`:68-80`) and `decode_iri_escapes_acc`
  (`:392-427`) build `list char` and call `String.string_of_list`.
  Not hot on ASCII prefixed Turtle; noticeable on heavy-escape IRIs.
- `skip_ws_and_comments` and `skip_to_eol` are still hand-rolled in
  the grammar file instead of living on the scanner. Folding them
  into `Parser.TurtleScanner` is step 2/3 of `turtle-text-scanner.md`
  and not done.

## Design doc step-by-step status (from turtle-text-scanner.md)

1. ✅ Add `Parser.TurtleScanner` — module exists, 342 lines.
2. 🟡 Move hot textual recognizers out of `Parser.Turtle` — PARTIAL.
   Prefixed names, IRI refs, short strings moved. Whitespace and
   comments **not** moved.
3. 🟡 Replace direct raw-text scanning in `Parser.Turtle` with scanner
   calls — PARTIAL, same split as above.
4. ❌ Add chunk-resumable scanning — not started. `scanner_state` /
   `scan_mode` types defined in `Parser.TurtleScanner.fst:10-24` but
   no caller uses them. No streaming API.
5. ❌ Revisit document-level parsing — not started. Document loop is
   still fuel-based recursion with manual whitespace skipping.

## Plan (proposed)

Ordering matters: each step's measured win feeds the next step's
priority.

### Phase A — quick measurable wins (no architectural disruption)

**A.1 — Finish step 2/3 of turtle-text-scanner.md.** Move
`skip_ws_and_comments` and `skip_to_eol` into `Parser.TurtleScanner`
so every char scan in the hot path goes through one scanner surface.
Expected: 1.2–1.5×. Cheap. Prerequisite for A.2.

**A.2 — Replace `append_list` with reversed accumulators in the
per-statement grammar folders.** Target sites:
`collect_verb_objs`, `parse_predicate_object_list_rev` (rename reflects
intent), collection parsing. Expected: 1.5–3× on Berlin-shaped data,
less on flat-prefixed. Verification impact: local, per-function
`decreases` edits. Single-sitting task per function.

**A.3 — Bench against current fixtures + add a 10k-triple fixture.**
CLAUDE.md calls out that 10k triples has never been observed to finish;
make that a tracked number. If A.1+A.2 don't bring 10k-prefixed under
~30s wall-time, we have evidence (1) dominates (3) and need to
prioritize Phase B.

### Phase B — the structural change: machine-int positions

**B.1 — Introduce `Parser.Position`.** A small F\* module defining:
```
type pos_t = n:int{n >= 0}
val pos_zero : pos_t
val pos_succ : pos_t -> pos_t
val pos_add  : pos_t -> n:nat -> pos_t
val pos_lt   : pos_t -> pos_t -> bool
val pos_sub  : p:pos_t -> q:pos_t{q <= p} -> nat
```
Pointed at `int` extraction, not `Z.t`. String bounds checks stay as
refinements, but arithmetic is native.

**B.2 — Thread `pos_t` through `Parser.TurtleScanner` first.** It's
smaller, self-contained, and all its callers are in one file. Bench
with a scanner-only microbenchmark if A.3 hasn't already produced one.

**B.3 — Thread `pos_t` through `Parser.Turtle`.** Mechanical but wide.
Expect weeks of slow SMT as proofs re-shape. Keep `Parser.Combinators`
and the other RDF parsers on `nat` initially — don't take on the whole
combinator stack until Turtle lands.

**B.4 — Decide on the combinator framework.** If `Parser.Combinators`
stays on `nat`, Turtle has to stop using it on the hot path (either
by inlining the combinators it uses, or by duplicating them in a
`pos_t`-typed variant). This is a choice with repercussions for
N-Triples / N-Quads / TriG; handle it after B.3 measures.

**Estimated win for Phase B:** 10–30× on top of Phase A. If Phase A
delivers 3–5× and Phase B delivers 15×, we land at ~50× — ~2–5k
triples/s median. Close to usable; 35MB file finishes in minutes
rather than never.

### Phase C — lazy span threading

**C.1 — Change `span_to_string` call sites to stay in spans.** Audit
the ~20 call sites in Parser.Turtle.fst. For each, decide: can the
downstream consumer work on `(input, span)` directly?

**C.2 — Prefix table keyed by span, not string.** The current prefix
table (`:Parser.Turtle.fst:30-108` region) materializes namespaces
as strings. A span-keyed version needs a span-equality function
(`span_equal input sp1 sp2` walks both, no allocation).

**C.3 — IRI resolution on spans.** `remove_dot_segments_step` rewritten
to operate on a span into the input. Emit the resolved IRI once, at
triple-construction time, rather than per-segment.

**Estimated win for Phase C:** 3–10× on top of Phase B. Full-IRI
workloads (currently the worst at ~52 triples/s) benefit most.
Target: ~10k triples/s median across all four fixtures.

### Phase D — chunk-resumable scanner (steps 4–5 of turtle-text-scanner.md)

Revisit only after Phase B+C land. Streaming/chunk-resumable is a
necessary feature for very large files, but it is not the reason the
parser is slow today. Doing it before B+C just gives us a
chunk-resumable slow parser.

## What I am NOT proposing

- **Non-F\* tokenizer.** Keeping F\* as the source of truth is an iron
  rule (CLAUDE.md rule 1). Phase B goes out of its way to stay in the
  verified surface.
- **Lax verification.** `--admit_smt_queries true` is already a sore
  spot in `SPARQL11.Parser.fst`; not adding more.
- **Rewriting every RDF parser at once.** Turtle is the one with the
  measurable problem. N-Triples/N-Quads/TriG ride along only if they
  share the combinator framework and we touch it in B.4.

## Success criteria

Good outcomes in priority order:

1. **10k prefixed Turtle triples parse under 5 seconds** wall-clock.
   This is a 50× improvement and the minimum bar for "usable."
2. **35MB Berlin Turtle parses to completion** under the 10-minute
   rule-17 cap, ideally under 2 minutes.
3. **fulliri-1000 comes within 2× of prefixed-1000** on the metrics
   fixtures. Today the ratio is ~5×; that gap is IRI resolution
   cost and full-IRI allocation, which Phases B+C attack directly.
4. **No regression in verification.** Phase B may slow F\* proof
   checking — acceptable. No new `admit` / `assume` introduced.

Non-goals for this plan:
- Matching rdflib / Jena / Apache ARQ speeds. They are 100–1000×
  faster than what we'd achieve; not the target.
- Streaming / incremental output. Phase D, separate concern.
- GC tuning. If we're still GC-bound after Phases A–C, reopen then.

## Open questions

- **Is `int` extraction actually native in F\* 2025.12.15?** Need to
  confirm. If `Prims.int` extracts to `Z.t` unconditionally, we need
  `UInt32`/`Int32` wrappers, which are uglier to verify against string
  length.
- **Does zarith have a small-int fast path?** If `Z.t` operations on
  values < 2^62 stay word-sized in practice (Zarith does have this
  optimization via OCaml's GC tagging), then the ~25ms/triple constant
  is less "bignum overhead" and more "allocation + dispatch overhead,"
  which changes the estimated win on B. Needs a microbenchmark with
  a `nat`-typed vs `UInt32`-typed identical loop.
- **Is the combinator framework worth keeping for the hot path at all?**
  `pbind` + closures may be an extraction cost we haven't isolated.
  Phase A.1 gives us a clean place to isolate it (scanner calls
  vs. combinator calls) and measure.

## Tracking

This plan is not yet broken into GitHub issues. Candidate issue
titles:

- "Turtle perf A.1: move skip_ws_and_comments into TurtleScanner"
- "Turtle perf A.2: eliminate append_list from per-statement folders"
- "Turtle perf A.3: add 10k-triple fixture to bench-turtle-metrics.sh"
- "Turtle perf B.1: Parser.Position module with machine-int extraction"
- "Turtle perf B.3: thread pos_t through Parser.Turtle"
- "Turtle perf C.1: audit span_to_string call sites for lazy threading"

File and link once Phase A.1 has a PR to attach them to.
