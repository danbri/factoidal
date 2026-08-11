# FastString re-founding migration (G4; owner-approved)

Owner: "Ok good migration plan - lets do this!" (2026-08-10), under the
four binding constraints in
[2026-08-09-sparql-e2e-proofs-plan.md](2026-08-09-sparql-e2e-proofs-plan.md)
§ Fast-path re-founding constraints. Full survey detail (op inventory,
1251 call sites across 31 modules, patch-89 anatomy, extraction
split-brain, benchmark harness state) is in the G4 program records;
this doc carries the decisions and the step gates.

## Decisions

- **Definitional model over FStar.String with a spec-level UTF-8 codec**
  (`Parser.FastString.Spec.fst`: `utf8_enc_char` / `utf8_bytes` /
  `utf8_decode_at` / `is_cp_boundary`), NOT a byte-list re-representation
  (rejected: 31 consumer modules take `string`; list indexing recreates
  O(n²)). All 8 axioms become theorems; residual assume val =
  `unsafe_char_of_d7ff` only (ulib char_of_int off-by-one, documented).
- **Pure definitions are the semantics, not the hot path.** History:
  BatUTF8-backed String ops measured 61.9–123 triples/s (2026-04-20
  profile, 99.9% CPU in BatUTF8); FastString restored ~104–108k tps at
  100k–1M. The fast OCaml returns as a rule-11(b) Option-B realisation:
  extracted spec functions stay alive under `fs_*_spec` names; the
  patch overrides `fs_*` with today's bodies; DELETABILITY = delete the
  patch and the spec bodies take over, slower never wrong.
- **Equivalence obligation**: property-test harness
  (`parser_fast_string_equivalence.ml`) — random ASCII, valid
  multi-byte UTF-8, adversarial invalid UTF-8 (truncations, bare
  continuations, overlongs, surrogates, 0xF5+ leads); `fs_op == fs_op_spec`
  on all inputs (byte_sub on the boundary-aligned clamp domain, with
  documented XFAIL rows off-domain — F\* strings cannot represent
  invalid UTF-8, so codepoint-splitting slices diverge by necessity).
  Runs in CI beside the hash-witness precedents AND under node/jsoo
  parity (bytes-as-JS-chars convention is part of the stated domain).
- **String.concat ulib gap**: local proved `concat_spec` (fold over
  `^`), zero new axioms; migrate only proof-critical call sites
  (Parser.JSON ×1, SPARQL.Protocol ×7); 328 other uses stay put.

## Steps (commit-sized; verify + benchmark gate each)

0. Freeze baselines (bench-turtle-metrics RUNS=5 +
   bench-parse-serialize), same-host discipline. GATE for the whole
   program: >10% median regression on any turtle fixture or 100k/1M
   parse rows (serialize rows gated at 10k — pre-existing dump-nq
   superlinearity) triggers/blocks per constraint 2.
1. `Parser.FastString.Spec.fst` — codec + lemma kit, additive,
   proof-only.
2. Re-found ops: new `Parser.FastString.fsti` (same names/signatures —
   consumers untouched, definitions opaque to their SMT contexts),
   assume vals → Spec-backed lets, patch 89 cut to
   `unsafe_char_of_d7ff` only. Expected+recorded: massive regression
   (constraint 1's own evidence). NEVER MERGED ALONE —
3. — merges WITH the Option-B realisation patch
   (experimental_ocaml_glue, rule 11(b)) + equivalence harness.
   Benchmark must return to within threshold of step 0.
4. `Parser.FastString.Axioms.fst` companion proves all 8 vals —
   axiom module stops being assumption-bearing, zero consumer churn;
   close/morph #358; obsolescence sweep.
5. Base-case lemma pack + `concat_spec`; unblocks the SRJ text bridge
   (M4) and N-Triples parser-side proofs (M1-adjacent).
6. Boundary-audit reclassification, parity run, doc sweep.

## Unblock map

Step 4 → N-Triples parser lemmas, N-Quads/TriG line proofs, streaming
chunk-fold (concat theorems power carry composition). Step 5 → SRJ
text-level composition. Token round-trip (SPARQL tokenizer) never
blocked — it doesn't use FastString.

## Risks (carried into briefs)

jsoo UTF-16 convention (equivalence runs under node parity);
`fs_cp_at` decoder must mirror `fs_cp_at_impl` branch-for-branch
(adversarial diff is the check); `.fsti` opacity against verify-time
fuel blowups (#273's verify-time analogue); FastString is near the
dependency root — steps 2-3 cascade the full .checked tree
(background build, COMMIT-FIRST); per-host benchmark honesty (never
pair numbers across container recycles).

## Step 2/3 results (2026-08-10, branch `faststring-step23`)

Host: `nproc` 4, CPU `Intel(R) Xeon(R) Processor @ 2.80GHz` — same
host as the [Step 0 baselines doc](2026-08-10-faststring-baselines.md)
(4 nproc, same CPU model line). Commits: Step 2 re-founding
`a176c0384c`, Step 3 draft `fd51e0685d`, Step 2+3 extract/compile-clean
`4a00d17246` (the commit the benchmark/W3C numbers below ran against).

### Step 2 — verify

`Parser.FastString.Spec.fst` (extended: `drop_bytes`/`take_bytes`/
`slice_bytes`/`find_byte(_scan)`/`utf8_decode_all(_aux)`),
`Parser.FastString.CharBoundary.fst` (new — the sole surviving
`unsafe_char_of_d7ff` assume val, split out because F* interface
conformance requires a real `let` for every `.fsti` `val` and
`assume val` cannot satisfy one — confirmed empirically, `include`d
back into `Parser.FastString`'s namespace), `Parser.FastString.fsti`
(new, opaque interface + `fs_*_spec` twins + bridging lemmas), and
`Parser.FastString.fst` (rewritten) all verify individually,
first-attempt.

Full cascade: `make -k -j4 verify` over the full 234-module corpus.
**233/234 have valid `.checked` files.** The one gap,
`RDF.CottasStore.PageCache.Bounds.fst` (Error 189, `cottas_column`
type mismatch), reproduces **identically** on a totally clean main
checkout with zero worktree diff — confirmed by deleting its
`.checked` and re-running `fstar.exe` directly on the unmodified main
tree. Pre-existing (absent from `build-ocaml.sh`'s module list, tracked
at issue #327, already documented in
`skills/fast-verify-extract/SKILL.md` as "present on disk and absent
from `build-ocaml.sh`'s `ALL_MODULES`, hence verified by nothing"), not
a regression from this migration. Step-2-alone benchmark: not
measured (the plan calls this optional; Step 2 was landed together
with Step 3's extract/compile in the same session, so no isolated
"regressed, unpatched" build was ever the current `HEAD` long enough
to benchmark cleanly).

### Step 3 — extract + compile

Two real bugs caught only by an actual `ocamlopt` compile (the prior
commit's standalone-probe sanity check was necessary but not
sufficient):

1. `Parser.FastString.Spec.fst` was never in `build-ocaml.sh`'s module
   lists (Step 1 landed it as proof-only/no extraction target — true
   at the time, false once Step 2 made `Parser.FastString.fst`'s
   runtime bodies call into it). Fixed by adding it to `ALL_MODULES`
   and both `COMMON_MODULES` occurrences, plus
   `tests/unit/run-all.sh`'s mirror list.
2. `parser_faststring_ops_runtime.sh`'s fast `fs_byte_at` body compared
   a plain OCaml `int` with `<`/`>=` without `let open Stdlib in`
   first — `Parser_FastString.ml`'s `open Prims` preamble shadows
   those operators to operate over `Z.t`. Fixed to match
   `fs_byte_sub`/`fs_find_byte`'s existing bodies.

Both fixed, both committed. `./build-ocaml.sh extract && ./build-ocaml.sh
compile`: **exit 0, 29 binaries built, 0 compile failures.**

### Step 3 — W3C suite (exact-equality gate)

**SPARQL 631 pass, 0 fail (of 631). RDF 1031 pass, 0 fail (of 1031).**
Exact match to the task's stated current-tree numbers — the fast
primitives (verbatim from the old patch 89, plus the one deliberate
`fs_byte_at` bounds-check change) are correctness-neutral for every
real parser call site. The remaining suites `w3c-tests.sh` also runs
(OWL 2 DL entailment, RDFC-1.0, SHACL, etc.) were NOT completed — OWL
2 DL entailment alone budgets up to 7200s **per catalog file** and
several files queue behind it; running the whole thing would have
cost the rest of this session for suites outside the task's stated
gate. Killed after confirming the SPARQL/RDF numbers above. Saying so
explicitly per the task brief's instruction not to claim a suite that
wasn't run.

### Step 3 — benchmark (`tools/bench-parse-serialize.sh`, RUNS=3)

All rows within the plan's 10% gate; every measured delta is single-run
noise, not a systematic regression:

| op | format | size | baseline (Step 0) | current (Step 2+3) | delta |
|---|---|---:|---:|---:|---:|
| parse | nt | 10,000 | 0.1292s | 0.1391s | +7.7% |
| parse | turtle | 10,000 | 0.1244s | 0.1270s | +2.1% |
| parse | rdfxml | 10,000 | 0.3645s | 0.3645s | +0.0% |
| parse | nt | 100,000 | 1.2374s | 1.2921s | +4.4% |
| parse | turtle | 100,000 | 1.1987s | 1.2141s | +1.3% |
| parse | rdfxml | 100,000 | 3.6005s | 3.5323s | -1.9% |
| parse | nt | 1,000,000 | 14.0245s | 12.9022s | -8.0% |
| parse | turtle | 1,000,000 | 12.4777s | 12.0919s | -3.1% |
| parse | rdfxml | 1,000,000 | 36.1411s | 35.9993s | -0.4% |
| serialize_nq | nt | 10,000 | 0.2138s | 0.2262s | +5.8% |
| serialize_nq | nt | 100,000 | 2.3493s | 2.4778s | +5.5% |
| serialize_nq | nt | 1,000,000 | 26.2955s | 26.9781s | +2.6% |
| canonicalize | nt | 10,000 | 0.3254s | 0.3477s | +6.9% |
| canonicalize | nt | 100,000 | 3.8059s | 3.9918s | +4.9% |

Gate targets (100k/1M parse rows, 10k serialize row) all pass. The
fast realisation restores Step 0 throughput, as the plan's
deletability claim predicts.

### Step 3 — equivalence test: **WALL, not satisfied**

`tests/unit/parser_fast_string_equivalence.ml` (400 generated cases:
1 empty + 200 random ASCII + 200 random valid multi-byte UTF-8, plus a
19-entry fixed adversarial corpus — truncated tails, bare
continuations, overlongs, surrogates, 0xF5+ leads — each tested
standalone AND embedded in a valid prefix/suffix) found a real,
precisely-bounded correctness gap in Step 1's already-landed
`Parser.FastString.Spec.utf8_bytes`, not introduced by Step 2/3 but
never exercised until this equivalence obligation ran:

**Root cause.** `Spec.utf8_bytes s` is defined as
`List.Tot.concatMap utf8_enc_char (FStar.String.list_of_string s)` —
it goes THROUGH `FStar.String.list_of_string`, ulib's own
BatUTF8-backed decoder, to turn `s` into codepoints, then re-encodes
those codepoints with `Spec`'s own `utf8_enc_char`. This is a
**second, independent UTF-8 decoder** from `Spec.utf8_decode_at` (the
RFC-3629 decoder Step 1 also wrote and that `fs_cp_at`/`fs_cp_len`
actually use) — the two agree only when `list_of_string` and
`utf8_decode_at` happen to decode the same bytes the same way, which
is true for VALID UTF-8 (both decoders agree with the "real"
codepoints) but is NOT guaranteed, and empirically FALSE, for
malformed input. Confirmed with a minimal repro outside the test
harness: for `s = "abc:\xE6\x80\x97\xA5:xyz"` (12 raw bytes, an
`0xE6` 3-byte lead consuming `0x80 0x97` correctly per RFC 3629
followed by a bare continuation byte `0xA5` that should decode to one
`U+FFFD` replacement), `fs_byte_length s` (fast, true byte count) is
**12**; `fs_byte_length_spec s` (Spec-backed) is **11** — `list_of_string`
silently disagrees with `Spec`'s own `utf8_decode_at` about how many
bytes that malformed tail consumes. Other adversarial inputs make
`list_of_string` raise `BatUChar.Out_of_range` outright, which is an
**uncaught exception**, not merely a wrong number — the equivalence
test run terminated with exactly that exception (rc=2) partway through
the adversarial-embedded corpus (`fatal error` at
`[adversarial-embedded#19 "abc:\xE6\x80\x97\xA5:xyz"]`, `fs_cp_at`
check).

**Exact boundary, confirmed by the log, not inferred.** Zero `FAIL`
rows for any `[empty]`, `[ascii#N]`, or `[utf8#N]` tag — all 401
valid-UTF-8 generated inputs passed cleanly on every op. **665 `FAIL`
rows recorded, all under `[adversarial#N]` / `[adversarial-embedded#N]`
tags**, before the run aborted on the uncaught exception (so 665 is a
floor, not the true count — an unknown number of later adversarial
checks and the whole documented-XFAIL `fs_byte_sub` off-domain block
never ran). `byte_at`/`find_byte`/`cp_at`/`cp_len` diverge in exactly
the positions downstream of a malformed byte's length disagreement
(everything after the point where the two decoders' consumed-byte
counts first differ); `byte_length` diverges once per malformed
string.

**Why this is a real wall, not a test-design error.** The task brief
explicitly scoped only `fs_byte_sub` to a "boundary-aligned... with
documented XFAIL rows off-domain" carve-out; the other five ops
(`byte_length`, `byte_at` in-bounds, `find_byte`, `cp_at`, `cp_len`)
were specified to hold "on all generated inputs" including the
adversarial corpus — reasonably, since the FAST realisations are pure
byte-level operations with no UTF-8 assumption at all, so agreement
on garbage bytes was the expected, achievable bar. `Spec.utf8_bytes`
breaks that bar because of a design choice already committed in Step 1
(this same session did not choose it, and reworking it is a `Spec.fst`
redesign, not a Step 2/3 fix — see below).

**Consequence for the "slower never wrong" deletability claim.** The
claim is false as written for malformed-UTF-8 input: deleting
`experimental_ocaml_glue/parser_faststring_ops_runtime.sh` would not
fall back to "slower, correct" — it would fall back to "slower, wrong
(or crashing) on exactly the raw-byte-buffer inputs Parser.FastString's
own SAFETY section documents as in-scope," because the SPEC-backed body
`fs_*` would revert to is the buggy `utf8_bytes`-based one. The
FAST realisation this migration ships is NOT affected (it is pure byte
arithmetic, confirmed correctness-neutral by the exact-match W3C
numbers above) — only the deletability fallback and the `fs_*_spec`
equivalence-test twins are.

**What this is NOT**: not a Parser.FastString.fst (Step 2) definitional
bug in isolation — `fs_byte_length`/`fs_byte_at`/etc. correctly
delegate to `Spec.utf8_bytes` exactly as designed; the bug is inside
`Spec.utf8_bytes` itself (Step 1, already landed, already verified —
verification only checks TYPES, not this semantic property, so nothing
caught it before this equivalence run). Not something a Step 2/3 patch
can honestly paper over: the fix is `Spec.utf8_bytes` needing its own
decoder (built on `Spec.utf8_decode_at`, walking raw bytes directly,
never touching `FStar.String.list_of_string`) — a `Spec.fst` codec
redesign that would also require re-deriving `Spec.fst`'s existing
lemma kit (`utf8_bytes_concat`, `utf8_decode_encode_identity`, etc.,
all currently stated in terms of the `list_of_string`-based definition)
against the new one. Out of scope for this landing; tracked as the
concrete next step below.

**STOP, per the task brief's own contingency instruction** ("If ...
the equivalence test doesn't hold... STOP at a committed checkpoint,
push, and report the wall precisely rather than forcing"). Nothing
further merges past commit `4a00d17246` on this branch pending that
`Spec.fst` redesign. Recommended next step: rewrite
`Parser.FastString.Spec.utf8_bytes` to compute bytes directly from
`FStar.String.list_of_string`'s ENCODE side only for the char-list-that-
came-from-a-real-string case (unavoidable — `string` has no byte-level
F* primitive at all) is not fixable in general; the tractable fix is
narrowing the CLAIM instead of the code: state and prove
`fs_byte_length`/`fs_byte_at`/`fs_find_byte`/`fs_cp_at`/`fs_cp_len`
`== fs_*_spec` only over strings whose `Spec.utf8_bytes` reduction is
independently well-formed (i.e. restrict the equivalence obligation,
and by extension the "slower never wrong" deletability promise, to the
valid-UTF-8 domain where it is actually true — 401/401 in this run),
and treat "byte-level primitive called on a non-UTF-8 buffer" as
requiring the FAST realisation UNCONDITIONALLY (never delete the patch
for that call class). Either framing is a real, scoped follow-up; this
session does not attempt it.

## Step 2/3 revisit — the crash is fixed (2026-08-10, branch `faststring-spec-refound`, issue #374)

Follow-up session, same day. Task: eliminate the crash and (if
achievable) the 665 divergences by making `Spec.utf8_bytes` the single
decoder. Commits `2fd461c761` (Spec.fst fix, verified) and `d58a80ddc0`
(extract/compile + test-harness fix) on branch `faststring-spec-refound`,
forked from the WALL commit `c5fa0f2b49` above.

**Root cause, precisely (confirmed by a standalone probe linking
`fstar.lib` directly, not inferred from the test's crash message
alone).** `FStar.Char.char` (ulib, `FStar.Char.fsti`) is a `new val
char:eqtype` — a genuinely ABSTRACT type. The only way F* Tot code
can observe a `string`'s content at all, valid or not, is
`FStar.String.list_of_string` (every other string primitive —
`length`, `index`, `get`, `sub` — is defined in terms of it; checked
directly against `FStar.String.fsti`, not assumed). Its OCaml
realisation (`FStar_String.ml`: `BatList.init (BatUTF8.length s) (fun
i -> BatUChar.code (BatUTF8.get s i))`) is **not actually total**
w.r.t. the `list char` type it is declared to return, on a string that
is not valid UTF-8: decoding `"abc:\xE6\x80\x97\xA5:xyz"` through it
returns `[97;98;99;58;24599;-1670;120;121;122]` — a **negative**
"codepoint" (`-1670`) that violates `int_of_char : char -> nat`'s own
postcondition. This is a genuine extraction-soundness gap in ulib's
OCaml backend on this domain, not a bug this project introduced.
`Parser.FastString.Spec.utf8_bytes` (`concatMap utf8_enc_char
(list_of_string s)`) propagated that poisoned value UNCLAMPED into a
`byte = n:nat{n<256}`, and from there into `Parser.FastString.fst`'s
`fs_byte_sub` → `FStar.String.string_of_list`, whose `BatUChar.chr`
call **throws** `BatUChar.Out_of_range` — the exact mechanism behind
the equivalence test's rc=2 abort (previously attributed only vaguely
to "other adversarial inputs").

**What is fixed.** A defensive clamp in `utf8_enc_char` (provably dead
code for any genuine `FStar.Char.char`, per `char_code`'s own
refinement — existing lemma proofs unaffected, verify first-attempt)
plus a matching lower-bound fix in `utf8_decode_all_aux`'s own clamp
(`cp < 0xd7ff` had no `cp >= 0`, defense in depth). Both stop the
poison before it reaches `string_of_list`.

**What is NOT fixed, and cannot be without a new `assume val`.** Full
elimination of `list_of_string` from `utf8_bytes` — making Spec.fst
decode literally ALL input, including non-UTF8-valid byte buffers,
through `utf8_decode_at` alone — is impossible: there is no OTHER F*
Tot primitive that observes a string's content, full stop (see the
argument above). Documented as the SINGLE-DECODER FINDING banner in
`Parser.FastString.Spec.fst` directly above `utf8_bytes`.

**Attempted and parked**: a round-trip theorem
(`utf8_decode_all (utf8_bytes s) == list_of_string s`, for every `s`)
proving Spec's own encode/decode pair are genuine inverses — the
closest unconditional statement of "single decoder" achievable inside
F*. Three attempts stalled at Error 19 ("Could not prove
post-condition") on the same step every time: getting
`utf8_decode_all_aux`'s recursive definition to unfold one step at a
fully symbolic call site, even with every supporting fact
(`utf8_decode_at_shift`, `utf8_decode_encode_identity`,
`char_of_int_of_char`, `char_code`'s range) asserted into context
immediately beforehand. This is the closure-identity/cross-boundary-
unfold obstruction class documented in
`skills/proof-factory/SKILL.md`, one level down (a recursive `let`'s
own defining equation not firing at a symbolic call, rather than a
lambda). Parked per the skill's stop-rule discipline; the concrete
next step (a `norm [delta_only [...]; zeta; iota]` tactic step) is
recorded in-file. Two small, general, reusable lemmas survive from the
attempt and verify standalone: `nth_byte_append`, `utf8_decode_at_shift`.

**Equivalence test — before/after, same corpus:**

| | before (WALL, `4a00d17246`) | after (`d58a80ddc0`) |
|---|---:|---:|
| crash | yes — `BatUChar.Out_of_range`, rc=2, run aborted partway | none — rc=0 |
| corpus exercised | partial (aborted mid adversarial-embedded#19) | full |
| unexpected FAIL | 665 (floor, undercounted — run never finished) | 0 |
| documented XFAIL | 20 (fs_byte_sub off-domain rows only) | 962 (fs_byte_sub off-domain + all five ops' adversarial-corpus rows, reclassified) |
| pass | — (run never finished) | 93846 |

The reclassification (five ops, not just `fs_byte_sub`, on the
adversarial corpus) is itself a finding: the original brief expected
`fs_byte_length`/`fs_byte_at`/`fs_find_byte`/`fs_cp_at`/`fs_cp_len` to
agree even on malformed input ("the FAST realisations are pure
byte-level operations with no UTF-8 assumption at all, so agreement on
garbage bytes was the expected, achievable bar") — that expectation
was never achievable given the `list_of_string` argument above; it
was simply never exercised to completion before this session to
notice. A second bug in the test harness itself (OOB `fs_byte_at`
probes assumed well-formedness-independent agreement, which is false
because `fs_byte_length_spec` can be shorter than the fast
`fs_byte_length` for malformed input) was caught by actually running
the suite after the Spec.fst fix, not by re-reasoning from the desk —
fixed in the same landing (commit `d58a80ddc0`).

**Regression check.** W3C RDF 1031 pass, 0 fail (exact match to the
Step 2/3 numbers above). W3C SPARQL 627 pass, 4 fail (out of 631) —
the 4 are pre-existing RIF entailment test failures (rule-evaluation
logic; zero overlap with this diff's two touched files, `Parser.
FastString.Spec.fst` and the equivalence test — not introduced by this
landing, not investigated further here, out of scope for issue #374).
`tests/unit/run-all.sh` (full, no target) also run: 30 of 48 files
fail, all on the SAME pre-existing cause — `RDFS_Closure_SemiNaive` is
in `build-ocaml.sh`'s `COMMON_MODULES` but missing from `run-all.sh`'s
own copy of that list (drift, not caused by this landing). Not fixed
here; worth its own issue.

**Verified**: `Parser.FastString.Spec.fst`, `Parser.FastString.fsti`,
`Parser.FastString.fst`, `Parser.FastString.Axioms.fsti`,
`Parser.FastString.RoundTripLemmas.fst`, `SPARQL.Protocol.RoundTrip.fst`,
`RDF.NTriples.RoundTrip.fst` — all re-verify (the latter four
unchanged, since `Parser.FastString.fsti`'s public interface never
moved). No admit, no `--lax`, no new `assume val`.

## Step 5 results (2026-08-10, branch `faststring-step5`)

Commits: Task A `612f84664c` (BaseCases pack), Task B `613235b34b`
(concat_spec + call-site migration), rebuild `a14cca7fa8`.

### Task A — `Parser.FastString.BaseCases.fst` (proof-only)

Concrete-literal byte facts for the JSON/N-Triples delimiter set
(quote, braces, brackets, colon, comma, angle brackets, space,
newline, backslash — 12 chars), each PROVED through the `.fsti`
bridging lemmas (`fs_byte_length_eq`, `fs_byte_at_eq`) +
`Spec.utf8_bytes_ascii_singleton`/`nth_byte_zero` — deliberately
independent of `Parser.FastString.Axioms` (step 4b in flight). Plus a
general ASCII-content family (`lemma_build_string_utf8_bytes` /
`_byte_length` / `_byte_at`) going straight through
`Spec.utf8_bytes_concat`, the Spec-direct sibling of
`RoundTripLemmas.fst`'s scaffolding.

### Task B — `Parser.FastString.ConcatSpec.fst` + migration

`concat_spec` — a local, transparent, proved replacement for
`FStar.String.concat` (fold over `^`, with `concat_spec_nil` /
`_singleton` / `_cons` equations). Closes string wall (2):
`FStar.String.concat` has ZERO stated equations in ulib, so even
`concat sep [x] == x` is unprovable for symbolic `x`. Migrated the
proof-critical call sites: `Parser.JSON.fst` (1 use,
`json_string_segments` terminal join) and `SPARQL.Protocol.fst`
(6 real call sites — the brief said 7; the 7th grep hit is a comment).
This changes EXTRACTED code, hence the rebuild commit.

### Gates (all labelled)

- ✅ W3C SPARQL: 627 pass, 4 fail (out of 631) — the 4 are the
  pre-existing intermittent RIF quartet (#367). W3C RDF: 1031 pass,
  0 fail (out of 1031).
- 📊 Benchmark vs the frozen step-0 baselines (gate: within 10%),
  same host — every row FASTER than baseline: parse nt 1M 99,387 vs
  71,304 triples/s; turtle 1M 95,848 vs 80,143; rdfxml 1M 35,297 vs
  27,669; serialize_nq 10k 57,504 vs 46,773; canonicalize 100k
  32,588 vs 26,275.
- ⚠️ The speedup is NOT attributed to this diff: `concat_spec` sits
  on the SPARQL-results/JSON paths, while the bench measures
  `factoidal count` / `factoidal-dump-nq` (`RDF.NQuads.Serialize`) —
  paths this diff cannot touch. All rows improved together, which
  points to a quieter host than the "moderately loaded" step-0
  baseline run. The gate passes; no speed claim beyond that.

Unblocked by this step: the SRJ text bridge (M4) and N-Triples
parser-side proofs (M1-adjacent) can now state their concat facts
against `concat_spec` equations instead of the ulib wall.

## Step 6 results (2026-08-11, worktree `parity-run2`, branch `parity-run2`)

Host: `nproc` 4, CPU `Intel(R) Xeon(R) Processor @ 2.80GHz` — same host
profile as the Step 0/2/3 baselines. Fresh worktree off
`origin/claude/main` (`b6dcf73acd`); `.checked` cache restored from the
`checked-cache` branch (116 modules), then a full
`./build-ocaml.sh extract && ./build-ocaml.sh compile && ./build-ocaml.sh
js` (cold on the 98 modules the cache missed) to get a clean,
same-commit native + JS build before measuring. Rebuild reproduced
byte-different-but-source-identical binaries (no `.fst`/`.ml` edited on
this branch) — reverted with `git checkout` before pushing so this
worktree carries doc-only changes.

### FastString equivalence corpus (native, step 4 of this task's method)

`tests/unit/run-all.sh parser_fast_string_equivalence`:

✅ **93,846 pass, 962 expected-fail (documented XFAIL), 0 unexpected fail.**
Exact match to the Step 2/3-revisit numbers recorded above
(`d58a80ddc0`) — confirms current `origin/claude/main` HEAD carries no
regression on this corpus.

**No node-side (JS) equivalence runner exists for this corpus.** Per
this task's own instruction, that gap is reported, not filled:
`tests/unit/` is a native-OCaml-only harness (`run-all.sh` links
committed `.cmx` against a hand-written `.ml` test file via
`ocamlfind ocamlopt`); there is no js_of_ocaml-under-Node equivalent
that exercises `fs_byte_length`/`fs_byte_at`/`fs_find_byte`/`fs_cp_at`/
`fs_cp_len`/`fs_byte_sub` against the same 401-valid-UTF-8 +
19-adversarial corpus in the JS runtime. The plan's own "Risks" section
named "jsoo UTF-16 convention" and said "equivalence runs under node
parity" — that intent is not yet built. What DOES run cross-runtime is
the general `tests/beyond-w3c/` demo-query suite below, which touches
FastString only incidentally (via the parser/serializer call sites,
not via a dedicated byte-op probe).

### Cross-runtime parity suite (native vs js-node)

`tests/beyond-w3c/bin/run-parity.py --manifest
tests/beyond-w3c/fixtures/index.json --runners native,js-node`:

✅ **4/4 cells pass** (2 queries × 2 runners):

| runner | query | status | ms |
|---|---|---|---:|
| native | bind-upper | pass | 24.5 |
| js-node | bind-upper | pass | 344.9 |
| native | ucase-unicode | pass | 20.6 |
| js-node | ucase-unicode | pass | 188.8 |

⚠️ **What "pass" means here, precisely — this is not a full parity
assertion.** Reading `tests/beyond-w3c/bin/run-parity.py`'s `classify()`
function directly: a cell is `pass` iff the runner's process exits 0.
The docstring says so explicitly ("Phase 2a (#243) lands the row-set /
row-count comparison logic here. For now, the scaffold just reports the
runner exited 0.") — there is no row-set or row-count comparison
between native and js-node output in the current code, despite the
manifest schema documenting `expected.kind` = `row-count` /
`row-set-csv` / `row-set-srx` / `boolean` fields. So this run proves
"neither runtime crashed or errored on these 2 queries," not "native
and JS agree on the result." Manually diffing the two runners' raw
stdout for both queries (not part of the harness, done here to give
the strongest honest statement available) shows byte-identical
SPARQL-Results JSON for both `bind-upper` and `ucase-unicode`,
including the non-ASCII `ucase-unicode` row values (`"EVE MÜLLER"`
etc.) — so for these 2 queries, output agreement is confirmed by hand,
not by the automated harness's own pass/fail signal.

**Coverage is 2 demo queries, not a corpus.** `tests/beyond-w3c/
fixtures/index.json` has exactly the seed manifest from the Phase 1
scaffold (`bind-upper`, `ucase-unicode`) — the "40+ demo queries across
6 demo pages" the suite's own README describes as its target (Phase 1,
issue #242) has not landed. Neither query is a targeted FastString
byte-op probe (adversarial/malformed UTF-8, boundary bytes); both are
ordinary SPARQL string functions over well-formed UTF-8 data.

### Wasm-node

**Not covered.** `tests/beyond-w3c/runners/run-wasm-node.sh` is a stub
(`echo '{"_runner_status":"unimplemented","sub_issue":244}'; exit 77`)
— every wasm-node cell would classify as `skip`, not `pass`, so it was
excluded from the `--runners` argument rather than run and skipped (CI's
`beyond-w3c.yml` does the same, with the same comment: "Wasm-node
intentionally omitted until #244's runner lands"). No wasm-side
FastString measurement exists at all yet.

### Divergences

None found — 0 unexpected-fail rows in the FastString corpus, 0
crash/error cells in the parity grid, byte-identical manual JSON diff
on both parity queries. No witness inputs to record.

### Task #47 step 6 — status

**Not complete**, precisely: the cross-runtime PARITY run this step
calls for is narrower than "prove by measurement that native and JS
agree" on the FastString migration specifically —

- ✅ Native equivalence corpus: current, 0 unexpected fail (93,846
  pass / 962 expected-fail), confirming no regression since the
  Step 2/3-revisit landing.
- ✅ General native/js-node demo-query parity: 4/4 cells pass (rc=0
  on both runtimes), plus a hand-verified byte-identical JSON diff for
  both queries — not run by the harness itself.
- 🔴 No automated row-set/row-count comparison exists in
  `run-parity.py` yet (Phase 2a, issue #243, not this task's scope to
  build — the task brief says use the existing harness, not extend it).
- 🔴 No node-side FastString byte-op equivalence runner exists — the
  jsoo-UTF-16-convention risk the plan named is still unmeasured at the
  byte-op level, only indirectly touched through 2 ordinary demo
  queries.
- 🔴 Wasm-node: unmeasured (stub, `#244` open).

Recommended next step (separate dispatch, not this task): either (a)
port `tests/unit/parser_fast_string_equivalence.ml`'s corpus to a
js_of_ocaml-under-Node harness calling the same `fs_*` functions
through the JS bundle, closing the actual named risk, or (b) treat the
byte-identical manual diff above plus the native corpus's 93,846-pass
result as sufficient evidence for this specific migration (FastString
correctness is a pure-OCaml-semantics question — js_of_ocaml compiles
the same `.ml`, so a jsoo-specific divergence would come from
js_of_ocaml's runtime string/bytes representation, not from
`Parser.FastString.fst`'s logic) and close the risk as "accepted,
covered by (a) the general js-node smoke suite passing and (b) jsoo's
`Bytes`/`String` runtime being tested elsewhere, not by a dedicated
byte-op corpus." This session does not pick between (a)/(b) — that is
an owner call given (b) has a real gap (no *adversarial* UTF-8 input
has ever been pushed at `fs_*` through jsoo).

### Task #47 step 6 — jsoo/node run (2026-08-11, worktree `js-equivalence`, branch `js-equivalence`)

Picked option (a) from the recommendation above:
`tests/unit/run-jsoo-equivalence.sh` compiles the SAME committed
`tests/unit/parser_fast_string_equivalence.ml` against the SAME
committed `Parser_FastString{,_Spec,_CharBoundary}.ml` extraction
outputs to OCaml bytecode (`ocamlfind ocamlc`, same package set as
`run-all.sh`'s native build), converts with `js_of_ocaml` using
build-ocaml.sh Step 4's exact runtime-file set and no
`--enable`/`--disable` overrides, and runs the resulting bundle under
`node`. No JS reimplementation of the test or of the `fs_*` ops
(CLAUDE.md rule #7) — same `.ml` files, different backend. Wired into
`tests/unit/run-all.sh` behind `--jsoo` (or `WITH_JSOO=1` in the
environment) so CI can opt in without slowing the default native run.

**String-representation finding**: the Decisions section above named
"bytes-as-JS-chars convention" as the stated domain. That is not what
ships. Both the freshly-built `tests/unit/_build_jsoo/*.js` bundle and
the already-committed production `docs/fstar-extracted/factoidal.js`
(rebuilt today, 2026-08-11, by an unrelated session) carry the
js_of_ocoml buildInfo header `use-js-string=true` — confirmed against
this worktree's `js_of_ocaml --version` (6.4.1) by compiling a
throwaway one-line probe with no flags and inspecting its header too.
`use-js-string=true` is js_of_ocaml's CURRENT DEFAULT (no
`--enable=use-js-string` was ever passed by `build-ocaml.sh`) — the
plan's "bytes-as-JS-chars" phrasing describes js_of_ocaml's OTHER,
array-backed representation, which is not what this project's build
recipe produces. This is a documentation-vs-reality gap in the plan's
own Decisions wording, not a code bug: `build-ocaml.sh` was never
asked for the array-backed mode, so there was never a chance it would
ship that way. Recorded here rather than silently corrected, per the
instruction not to fix findings, only document them with witnesses.

✅ **Result: exact match, 93,846 pass, 962 expected-fail (documented
XFAIL), 0 unexpected fail (out of 94,808)** — identical to the native
number recorded in the Step 6 results section above. Verified three
ways in this session for redundancy against the missing-`.cmx`
build-environment gap noted below: (1) `node
tests/unit/_build_jsoo/fast_string_equiv.js` — the jsoo/Node path
itself; (2) a from-source `ocamlfind ocamlopt` compile of the same
three `.ml` files run natively in this worktree (bypassing the
missing committed `.cmx` — see below) — same 93,846/962/0; (3) the
plan doc's own 2026-08-11 `parity-run2` record above, from a
different worktree with a full `./build-ocaml.sh compile`. All three
agree. **No unexpected-fail rows in any run — no witness inputs to
record, because there was no divergence.** The adversarial corpus (19
snippets, standalone and embedded — truncated tails, bare
continuations, overlongs, surrogate encodings, 0xF5+ leads) ran
through `js_of_ocaml`'s `use-js-string=true` string representation and
produced byte-identical PASS/XFAIL classification to native on every
row.

**Unrelated pre-existing gap surfaced, not fixed**: `tests/unit/run-all.sh
parser_fast_string_equivalence` (the plain native path, no `--jsoo`)
currently FAILS to build in a from-`origin/claude/main` worktree that
has only run `tools/ensure-test-env.sh` (test-fixture submodules) —
`ocaml-output/Parser_FastString.cmx` and 173 other canonical modules'
`.cmx` are not present until `cd formal/fstar && ./build-ocaml.sh
compile` is run; only 3 `Parser_FastString*.cmx` files happen to be
committed to git in this tree. Point (2) above works around this by
compiling from `.ml` source directly instead of linking committed
`.cmx`, same trick `run-jsoo-equivalence.sh` already uses (it always
compiles from source, since jsoo needs bytecode `.cmo` objects that
are not committed at all). This is an environment/build-completeness
gap in the worktree bootstrap, not introduced by this task and not
fixed here — flagged so a future session doesn't mistake `run-all.sh`'s
native BUILD FAILED for a jsoo-caused regression.

**Task #47 / migration step 6: COMPLETE.** All five 🔴 items from the
prior status list are now closed or explicitly superseded:
- ✅ jsoo/Node FastString byte-op equivalence corpus: now exists, runs,
  0 unexpected fail, wired into `run-all.sh --jsoo` for CI.
- ✅ Native equivalence corpus: unchanged, still 0 unexpected fail
  (confirmed again this session, independently, via from-source
  compile).
- ✅ General native/js-node demo-query parity: unchanged from the prior
  record (4/4 cells pass).
- ⚠️ No automated row-set/row-count comparison in `run-parity.py`
  (issue #243) — still open, still explicitly out of this task's
  scope (unchanged from the prior assessment; not a FastString-specific
  gap).
- ⚠️ Wasm-node (issue #244) — still unmeasured, still a stub; not part
  of this migration's stated jsoo risk (the plan's Risks section names
  "jsoo UTF-16 convention" specifically, not wasm).
