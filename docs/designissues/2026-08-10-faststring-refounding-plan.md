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
