# Turtle Parser CPU Profile — 2026-04-20

Companion to:
- [`2026-04-19-turtle-parser-speed.md`](2026-04-19-turtle-parser-speed.md) — audit + phased plan
- [`turtle-parser-metrics.md`](turtle-parser-metrics.md) — benchmark harness
- [`turtle-text-scanner.md`](turtle-text-scanner.md) — scanner architecture
- CLAUDE.md "Known Performance Issues"

The 2026-04-19 audit pointed at three structural bottlenecks (`nat` →
`Z.t`, eager `span_to_string`, O(n) list append) and guessed bignum
arithmetic was dominating. **This note takes an actual CPU profile and
shows the dominant cost is somewhere else entirely.** The headline: the
`FStar.String` surface in the F\* OCaml runtime routes every
`String.length` / `String.index` / `String.sub` call through
`BatUTF8`, a codepoint-indexed UTF-8 library where `length`, `nth`, and
`next` are O(n) byte walks. That turns every inner-loop `String.length
input` and `String.index input pos` in the Turtle parser into a linear
scan of the whole string. It is straightforwardly O(n²).

## 1. Methodology

Three synthetic Turtle files were generated under `/tmp/tperf/` —
`t-100.ttl`, `t-500.ttl`, `t-1000.ttl` — each a flat list of full-IRI
triples of the form `<http://ex/s$i> <http://ex/p> <http://ex/o> .` with
no prefixes, language tags, or typed literals. `factoidal --count` was
timed three times per file with a 600 s wall-clock cap (rule #17; no
timeouts were tripped). Timings use `python3 -c 'import time; ...'`
millisecond clocks. macOS `sample(1)` (1 ms sampling, 12 s window)
profiled a fourth run on the 1000-triple file; the target was given
a 2 s warm-up. All raw outputs are in
`/Users/danbri/working/factoidal/.claude-runs/tperf-timings-20260420.log`
and `/tmp/tperf/sample-1000.txt` (600 919 B). No F\* code was changed
and no build ran during this session — another subagent was doing an
`extract`/`compile` concurrently, and this work is read-only.

## 2. Scaling curve

| Triples | File size | Median wall time | Triples / second |
|---------|-----------|------------------|------------------|
| 100     | 4.6 KB    | 1035 ms          | 96.6 tps         |
| 500     | 23 KB     | 4060 ms          | 123.2 tps        |
| 1000    | 46 KB     | 16168 ms         | 61.9 tps         |

Variance across three runs was < 1 % at each N (measurement granularity
is ~1 s due to the `sleep 1` wait loop used in place of `timeout(1)`,
which is absent on macOS; the factoidal runs themselves were timed by
Python millisecond clocks and are accurate to ~1 ms).

Scaling ratios:

- 100 → 500 (5× input): 3.9× wall time. Sub-linear. (Startup amortisation.)
- 500 → 1000 (2× input): 4.0× wall time. Strongly super-linear.
- 100 → 1000 (10× input): 15.6× wall time. Between O(n^1.2) and O(n^1.5).

The 500→1000 doubling producing a 4× wall-clock hit is the clearest
signal of quadratic behaviour. A linear parser doubling with input would
show 2×; we see 4×. The 100→500 result under-scales because startup
(runtime init, argv parsing, file open) is a constant ~100 ms that
dominates the small-N case but washes out at larger N.

## 3. Top functions by sampled CPU time

`sample(1)` collected 10 111 stack samples over a 12 s window on the
1000-triple run. It split time by leaf frame ("self time") and by
"total in stack" (inclusive, recursive-counted-multiple).

**Self time (leaf frames, ≥ 5 samples):**

| Rank | Function | Samples | % of total |
|------|----------|---------|------------|
| 1 | `camlBatUTF8__length_aux_549` | 4873 | 48.2% |
| 2 | `camlBatUTF8__nth_aux_414`    | 2765 | 27.3% |
| 3 | `camlBatUTF8__next_390`       | 2459 | 24.3% |

Those three `BatUTF8` primitives account for **99.9 % of all leaf
samples**. Nothing else registers as a leaf above the 5-sample
threshold. The program is, essentially, running `BatUTF8` full-time.

**Inclusive / "total in stack" (recursive multiples counted):**

| Rank | Function | Samples |
|------|----------|---------|
| 1  | `camlFactoidal_cli__fun_3777` (top-level `--count` entry)  | 10 111 |
| 2  | `camlBatUTF8__nth_aux_414` (appears on many sub-stacks)    |  7 988 |
| 3  | `camlBatUTF8__length_aux_549`                              |  7 450 |
| 4  | `camlParser_TurtleScanner__scan_iri_ref_end_1167`          |  3 245 |
| 5  | `camlBatUTF8__next_390`                                    |  2 459 |
| 6  | `camlParser_Turtle__decode_iri_escapes_acc_1427`           |  1 635 |
| 7  | `camlParser_TurtleScanner__scan_ws_comments_887`           |    950 |
| 8  | `camlParser_TurtleScanner__skip_ws_comments_895`           |    560 |
| 9  | `camlParser_Turtle__parse_turtle_iri_1589`                 |    174 |
| 10 | `camlParser_Combinators__pstring_717`                      |    162 |

Numbers derived by summing the subtree count at every occurrence of the
function name in the call graph section of
`/tmp/tperf/sample-1000.txt`. They over-count recursion, but the
relative ordering is trustworthy.

The top F\*-originated callers of BatUTF8 are:

- `decode_iri_escapes_acc` (`Parser.Turtle.fst:392-427`) — calls
  `String.length` and `String.index` repeatedly while walking a
  character list. The 1635 samples here are almost entirely BatUTF8 at
  the bottom of the stack.
- `scan_iri_ref_end` (`Parser.TurtleScanner.fst:233-280`) — the inner
  loop for IRI-reference scanning. Does `String.length input`
  **every iteration** (line 237) and `String.index input pos` at
  several positions (lines 240, 246, 250–253, 263–270). On a full-IRI
  fixture with 1000 triples each of which contains three IRIs of
  average length ~14 chars, this function alone calls `String.length`
  ~40k times, each doing a full UTF-8 walk of the entire document.
- `scan_ws_comments` / `skip_ws_comments` — inter-triple whitespace
  skipping, same pattern.
- `pstring` from `Parser.Combinators.fst` — `String.sub` / `String.index`
  during fixed-string matching.

## 4. Interpretation

The 2026-04-19 audit was right that there is an O(n²)-ish cost and
partially right about where it lives, but the **specific primitive**
is not `FStar_String.sub` copying, and it is **not** `Z.t` bignum
arithmetic. It is `BatUTF8.length_aux`, `BatUTF8.nth_aux`, and
`BatUTF8.next`.

The F\* OCaml runtime at
`~/.opam/fstar/lib/fstar/ulib/ml/app/FStar_String.ml` defines:

```ocaml
let length s = Z.of_int (BatUTF8.length s)
let get s i = BatUChar.code (BatUTF8.get s (Z.to_int i))
let index = get
let substring s i j =
  BatUTF8.init (Z.to_int j) (fun k -> BatUTF8.get s (k + Z.to_int i))
let sub = substring
```

And in `batUTF8.ml`:

```ocaml
let rec length_aux s c i =              (* O(|s|) *)
  if i >= String.length s then c else
    let n = Char.code (String.unsafe_get s i) in
    let k = (* 1/2/3/4 based on leading byte *)
    length_aux s (c + 1) (i + k)

let rec nth_aux s i n =                 (* O(n) codepoints from byte 0 *)
  if n = 0 then i else nth_aux s (next s i) (n - 1)

let get s n = look s (nth s n)          (* => O(n) per get *)
```

So:

- Every `String.length input` in the parser is a **full UTF-8 walk of
  the entire input** (O(N) where N = file size in bytes), not the
  O(1) you'd expect from reading F\* source.
- Every `String.index input pos` is a **walk from byte 0 to codepoint
  `pos`** (O(pos) bytes), again not O(1).
- Every `String.sub input i j` allocates a new string and does `j`
  calls to `BatUTF8.get`, each O(i + k). So a single `sub` is
  O(j × (i + j)), not O(j).

`Parser.Turtle.fst` contains 186 grep-matchable `String.length` /
`String.sub` / `String.index` uses; `Parser.TurtleScanner.fst` has
49; `Parser.Combinators.fst` has 29. Many are in inner loops that do
one or more `String.length input` per character step. That alone is
sufficient to explain the 4× slowdown per 2× input — the product of
two roughly-linear passes.

`Z.t` (zarith) arithmetic does not appear in the sample profile at all
above the 5-sample threshold. The 2026-04-19 audit's **Estimated win
if fixed: 10-30× for machine-int positions** is almost certainly an
over-estimate; zarith has a tagged-small-int fast path that keeps
positions < 2^62 word-sized, and nothing in the profile points at
`caml_mul`, `caml_add`, or `zarith`-prefixed symbols. Machine-int
positions are still worth doing eventually (they have compile-time
benefits too), but they are **not where today's wall-clock lives**.

## 5. Proposed fix

**Choice: (a) — narrow `assume val` boundary for string primitives.**

Replace the `FStar.String` surface used on the hot path with a small
module, `Parser.FastString.fst`, whose operations are declared `assume
val` in F\* and implemented in OCaml directly on `Bytes` / `String`
using byte indices (not UTF-8 codepoints). This preserves the verified
parser algorithm — every Turtle grammar rule, every scanner state
machine, every IRI-escape decoder keeps its current F\* definition and
proof obligations — while narrowing the **trusted code boundary** to
roughly a hundred lines of OCaml.

Rationale over the alternatives:

- **(b) hand-written OCaml tokenizer** — The hot functions are
  `scan_iri_ref_end`, `scan_ws_comments`, `decode_iri_escapes_acc`,
  `pstring`. These are lexer-layer functions and (b) would help. But
  `scan_iri_ref_end` is already in F\* and the logic is correct and
  verified; the only thing wrong with it is that the F\* runtime makes
  its string primitives O(n). Replacing the primitives is strictly
  narrower than replacing the whole tokenizer, and it keeps the
  verified-surface claim true.
- **(c) byte-offset rewrite of the parser** — Does not help on its own.
  Today the parser already uses byte offsets (typed as `nat`); what's
  slow is that when it says `String.length input` to check a bound,
  the runtime doesn't just read a header word — it re-scans the whole
  string. Fixing (c) without fixing the primitives is shuffling deck
  chairs. Fixing the primitives without (c) closes most of the gap.
  If, after (a), we still need to avoid allocation in `String.sub`
  (scenario: very long quoted literals), we can layer (c) on top as a
  second pass.

### What would change

A new file `formal/fstar/Parser.FastString.fst`:

```
module Parser.FastString

(* UTF-8 validated byte string. For the parser hot path only. *)

val byte_length  : string -> nat          (* O(1) — reads OCaml string length *)
val byte_index   : s:string -> i:nat{i < byte_length s} -> FStar.Char.char
val byte_sub     : s:string -> i:nat -> j:nat{i + j <= byte_length s} -> string
val byte_eq_at   : s:string -> i:nat -> t:string -> bool   (* prefix eq, O(|t|) *)

(* Optional: a codepoint-decoding step on top of byte indexing, for the few
   places the parser actually needs codepoint semantics (e.g. PN_LOCAL
   character classes). Bytes in, codepoint out, advances by byte count. *)
val decode_utf8_at : s:string -> i:nat{i < byte_length s} -> option (nat & nat)
```

All four `val`s are `assume val`, implemented via `ocaml-patches.sh`
and the `minimal_regrettable_glue_code_each_with_an_open_issue/`
directory (new file, e.g. `NN_parser_faststring.sh`, with an open
issue). The OCaml bodies are one-liners over `String.length`,
`String.unsafe_get`, `String.sub`, and a compact UTF-8 decoder (well
under 30 lines).

Then, the mechanical part: replace `String.length`, `String.index`,
and `String.sub` call sites in `Parser.Turtle.fst`,
`Parser.TurtleScanner.fst`, and `Parser.Combinators.fst` with
`byte_length`, `byte_index`, `byte_sub`. Most sites are already
operating on what is semantically a byte offset, so the swap is
type-safe; places that need codepoint semantics (a minority — the
character-class checks in `decode_iri_escapes_acc` for instance)
route through `decode_utf8_at`.

### Estimated effort

- `Parser.FastString.fst` + its `assume val` stubs: 1 F\* module,
  ~50 LOC F\* signature, ~40 LOC OCaml patch. Single session.
- Swap in `Parser.Turtle.fst` / `Parser.TurtleScanner.fst` /
  `Parser.Combinators.fst`: 186 + 49 + 29 = 264 call sites. Most are
  mechanical. Plan on two sessions for the swap and re-verification
  (F\* may need annotation tweaks where refinements previously relied
  on `String.length` being Z.t-typed).
- Benchmark + regression: one session, reusing the 100/500/1000
  fixture from this profile plus the existing `turtle-parser-metrics.sh`.

Total: ~3-4 focused working sessions, no build-infrastructure work.

### Estimated speedup

Realistic prediction: **5-15× on the 1000-triple fixture**, landing in
the range **300-1000 triples/sec** on full-IRI input. The largest
uncertainty is whether removing BatUTF8 surfaces **some other**
constant that was previously hidden under it — allocation cost in
`String.sub` results, list manipulation in `decode_iri_escapes_acc`,
etc. The profile says leaf time is 99.9 % BatUTF8, so in principle
killing it should give an order of magnitude; in practice the next
layer of cost may eat some of that. I am **not** claiming 100×. The
auditor's 2026-04-19 target of "usable" = 5000 triples/sec is a
**further** step beyond this fix, and likely needs (c) byte-offset
parser plumbing to reach.

## 6. Out of scope

- **N-Quads / N-Triples / TriG performance.** Those parsers share
  `Parser.Combinators.fst` but not the Turtle-specific scanners. The
  `FastString` swap in `Parser.Combinators.fst` would benefit them
  automatically; their own files can swap later.
- **Turtle semantic features.** Prefixed names, collections
  (`( … )`), blank-node property lists, `a`-shorthand, base-IRI
  resolution, language-tagged / typed literals — all stay in F\*,
  unchanged. This fix only touches string primitives.
- **N-Quads / TriG scanner fusion.** Possibly worthwhile later; not
  on the critical path for "Turtle is too slow".
- **JS / wasm targets.** js\_of\_ocaml ships its own `String` and
  `Bytes` implementations; the BatUTF8 surface may behave differently
  there. A separate profile pass under `node` or a browser would be
  needed before claiming wins on those targets.

## 7. Success criterion

Pick a single, defensible bar:

**The 1000-triple full-IRI fixture from this profile must parse in
under 1 second wall-clock** (median of 3 runs, same machine). That's
≥ 1000 triples/sec, a 16× improvement over today's 61.9 tps. Realistic
relative to the profile's prediction, and 25× below the audit's
"usable" bar of 5k tps — which remains the target for the subsequent
phase (byte-offset plumbing + lazy span threading).

Secondary: the 100/500/1000 scaling curve must be **linear** (within
~20 %) after the fix. If it's still super-linear, some other O(n²)
site is lurking — most likely the list-append path (audit §3) or
`String.sub`-allocated substring comparison in prefix-name lookup.

If the fix lands and the 1000-triple number stays above 5 s
(i.e. < 200 tps), the hypothesis was wrong and we fall back to (b) or
(c). The profile would need to be re-run post-fix to identify what
rose to the top once BatUTF8 left.
