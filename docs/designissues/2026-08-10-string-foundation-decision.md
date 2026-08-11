# String foundation: 4 remaining ulib gaps — owner decision needed

Owner-decision doc, G4/#358 Step 4 Task B
([2026-08-10-faststring-refounding-plan.md](2026-08-10-faststring-refounding-plan.md)).
Written after `Parser.FastString.Axioms.fst` landed (branch
`faststring-step4b`) — that work proved all 8 remaining axioms about
OUR OWN `Parser.FastString` module and closed it as a source of
`assume val`s. This doc is about a DIFFERENT, deeper layer: gaps in
F\*'s standard library (`ulib`, specifically `FStar.String.fsti`)
itself — things our code cannot fix by proving harder, because the
fact needed does not exist anywhere in the trusted base to build a
proof on top of.

Plain-English summary: F\*'s built-in string library gives us some
facts about strings "for free" (already proven, in `ulib`) and leaves
others completely unstated. Where a fact is unstated, no amount of
proof effort on our side can produce it — that is not a skill gap on
our end, it is a hole in the foundation. Four such holes are listed
below, with the exact evidence, and for each one, two ways forward:
prove it ourselves without adding any new trusted assumption (slower,
but keeps our "no assume val" promise intact), or add ONE new
carefully-scoped trusted assumption (faster, but is a real crack in
the foundation that has to be tracked forever). Two are now fully
resolved (one closed this session, one merged to the main branch
during this session). Two are still open and need a decision.

## Gap 1 — `FStar.String.sub` has no content spec

**What's missing.** `FStar.String.fsti` declares:

```
val sub: s:string -> i:nat -> l:nat{i + l <= length s} -> Tot (r: string {length r = l})
```

That is the ENTIRE specification — it only promises the output has
the right LENGTH. It says nothing about which CHARACTERS come out.
Compare this to `FStar.String.fsti`'s OTHER operations, which do carry
content facts: `index_string_of_list`, `index_list_of_string`,
`concat_length`, `list_of_concat`. `sub` has no equivalent.

**Evidence, in-tree.**
`formal/fstar/SPARQL11.Parser.AskBgpRoundTrip.fst` (lines 656–730) ran
a real proof attempt and hit this wall directly. Two probe lemmas,
written in the most favorable possible form —

```
val sub_of_concat (a b : string)
  : Lemma (ensures (FStar.String.concat_length a b;
                     String.sub (a ^ b) (String.length a) (String.length b) == b))

val sub_of_concat_literal (rest : string)
  : Lemma (ensures (FStar.String.concat_length "ASK" rest;
                     String.sub ("ASK" ^ rest) 0 (String.length "ASK") == "ASK"))
```

— both fail with "Could not prove post-condition" (Error 19), even
raising the solver's search budget. The file's own conclusion, quoted
directly: *"No F\* proof text, however constructed, can close a lemma
whose truth depends on a fact the trusted interface never asserts —
this is a SOUNDNESS boundary, not a search-budget one."*

**Why it matters.** Every SPARQL 1.1 token that carries text — an
IRI, a variable name, a string literal, a number, a blank-node label,
a language tag, or a keyword like ASK/SELECT/WHERE — is extracted by
`formal/fstar/SPARQL11.Parser.fst`'s `substring` wrapper (line 164),
which for the normal in-bounds case is just `String.sub` (line 166:
`String.sub s p len`). So this one gap blocks proving that ANY
SPARQL query, printed back out to text, parses back to the same
query — for every construct beyond bare punctuation tokens.

**Option A — zero new axiom.** Migrate `SPARQL11.Parser.fst`'s
`substring` (line 164) from `FStar.String.sub` to
`Parser.FastString.fs_byte_sub` / the codepoint-list machinery in
`Parser.FastString.fst`. This is not a new idea — the
`AskBgpRoundTrip.fst` banner itself names it as option (ii),
"restructuring the lexer to avoid substring's opaque path." What
changed since that banner was written: `Parser.FastString` is now
FULLY specified with no open gaps (this session's Task A closed the
last ones), including `fs_byte_sub_self` — the exact "slice recovers
the string" fact `FStar.String.sub` is missing. So this path now has
everything it needs already proven and sitting in the tree; nothing
new needs inventing, only a migration. It is still real work: the
SPARQL lexer currently indexes by CODEPOINT position (`FStar.String
.length`/`index`), while `Parser.FastString` indexes by BYTE position
— the lexer's position bookkeeping would need to move to byte
offsets, a genuine engine change, not a one-line swap. Untried this
session; no size estimate exists yet.

**Option B — owner-gated trusted rule.** Add ONE new `assume val` to
a small first-party interface (not editing `FStar.String.fsti`
itself) stating the content fact ulib omits — something in the shape
of "`list_of_string (sub s i l) == slice of (list_of_string s) from i
to i+l`." This is a real, permanent addition to the trust surface
(iron rule #3(a): needs its own open GitHub issue, stays visible in
the assume-val ledger forever) but unblocks the text-level round-trip
theorems immediately, without an engine rewrite.

**Recommendation.** Option A (zero new axiom) is the right LONG-TERM
answer — it reuses proven work instead of adding a permanent trust-
surface item, and it is philosophically identical to what this whole
FastString migration has been doing. But its size is unknown and it
touches the SPARQL 1.1 lexer, a load-bearing file. Option B is smaller
and immediate. This is exactly the kind of size-vs-permanence trade
this doc exists to put in front of the owner rather than guess at.

## Gap 2 — `FStar.String.concat` has zero equations

**What's missing.** `FStar.String.fsti` declares `val concat: string
-> list string -> Tot string` with no `Lemma` anywhere in the file
mentioning it — confirmed by grep. Even the simplest possible fact,
"`concat sep [x] == x`" for a single-element list, is unprovable
against it for a symbolic `x`.

**Status: FIXED, zero new axiom, MERGED to `claude/main`.** (Checked
live while writing this doc: `origin/claude/main` moved during this
session and now contains this fix — `git merge-base --is-ancestor
origin/faststring-step5 origin/claude/main` now reports true. An
earlier draft of this section, written minutes earlier against an
older `claude/main`, said "not yet merged" — corrected here rather
than left stale, since a wrong merge-status claim in an owner-decision
doc is exactly the kind of thing this project's anti-pattern #3
warns about.) Branch `faststring-step5`, commit `613235b34b`
("faststring step 5, Task B: concat_spec, migrate JSON + Protocol call
sites") adds `formal/fstar/Parser.FastString.ConcatSpec.fst`: a local,
fully proved replacement —

```
val concat_spec (sep : string) (l : list string) : Tot string (decreases l)
let rec concat_spec sep l =
  match l with
  | []        -> ""
  | [x]       -> x
  | x :: rest -> x ^ sep ^ concat_spec sep rest
```

— with three lemmas (`concat_spec_nil`, `concat_spec_singleton`,
`concat_spec_cons`), each a direct restatement of one line of the
`match`, proved by `= ()`. The 7 proof-critical call sites were
migrated: `Parser.JSON.fst`'s `json_string_segments` (1 site) and
`SPARQL.Protocol.fst`'s four `serialise_response_*` functions plus
`decode_request` and `extract_status_class` (6 sites). Both files
re-verify clean. A follow-up commit on the same branch,
`a14cca7fa8` ("rebuild binaries after concat_spec migration"), shows
the change is extraction-clean and gate-clean: SPARQL 627/631 pass (4
pre-existing, unrelated RIF failures), RDF 1031/1031 pass, and every
`tools/bench-parse-serialize.sh` row inside the plan's 10% regression
gate.

This module does NOT claim `concat_spec == FStar.String.concat` —
that would hit the exact same wall it is working around (comparing a
defined function to an opaque one with no equations). Instead it
REPLACES the call sites, so the opaque primitive stops appearing on
proof-critical paths. 328 other, non-proof-critical `String.concat`
call sites in the tree are untouched by design (the plan's own
scoping).

**No decision needed here.** The fix is in place and merged. Listed
for completeness and traceability only, since Task B was scoped to
include it.

## Gap 3 — `list_of_string` returns negative codepoints on invalid UTF-8

**What's missing.** `FStar.String.list_of_string : string -> Tot (list
char)` is DECLARED total, but its OCaml realization
(`FStar_String.ml`: `BatList.init (BatUTF8.length s) (fun i ->
BatUChar.code (BatUTF8.get s i))`) is not actually total with respect
to that declared return type when handed a string that is not valid
UTF-8. Measured directly (a standalone probe linking `fstar.lib`
outside any test harness, not inferred from a crash message): decoding
the 12-byte buffer `"abc:\xE6\x80\x97\xA5:xyz"` returns the codepoint
list `[97;98;99;58;24599;-1670;120;121;122]` — a NEGATIVE "codepoint"
(`-1670`) that violates `FStar.Char.int_of_char : char -> nat`'s own
stated postcondition (a `char`'s code is always a natural number).
This is a genuine soundness gap in ulib's OCaml extraction, not a bug
in this project's code — full argument in
`formal/fstar/Parser.FastString.Spec.fst`'s "SINGLE-DECODER FINDING"
banner (issue #374).

**Status: contained, zero new axiom, already landed on
`claude/main`.** `Parser.FastString.Spec.fst`'s `utf8_enc_char` and
`utf8_decode_all_aux` both carry defensive clamps that catch a
poisoned codepoint (negative, or otherwise out of `FStar.Char.char`'s
valid range) before it reaches `FStar.String.string_of_list`, whose
`BatUChar.chr` call is what actually THROWS (`BatUChar.Out_of_range`)
— that was the exact mechanism behind a real crash caught by the
equivalence test harness before the fix (`tests/unit
/parser_fast_string_equivalence.ml`, rc=2 abort). After the fix: 0
crashes, 93,846 pass, 962 documented XFAIL rows (malformed input where
the two independent decoders — ulib's and `Parser.FastString.Spec`'s
own — legitimately disagree on how many bytes a bad byte run
consumes; a divergence in COUNT, contained, never a crash).

**What remains unfixed, and cannot be fixed on our side.** The
clamps stop the crash and contain the damage, but they do not — and
architecturally cannot — make `list_of_string` itself correct on
malformed input; that would require a fix inside `BatUTF8`/`ulib`
itself, third-party code outside this project's verified boundary.

**Option A — zero new axiom (already in place).** Keep the
containment as the permanent posture: malformed UTF-8 never crashes,
byte-count divergence from it is documented and bounded, and no
`assume val` is added anywhere. This is the status quo.

**Option B — report the bug upstream to FStarLang/FStar.** This
would be the "real" fix (getting ulib itself corrected, or at least
officially acknowledged), but it is explicitly gated. Owner
instruction, quoted verbatim, 2026-08-10, issue #376 comment: *"Do
not open a ticket upstream without my sayso. The FStarLang/FStar
report mentioned in this issue (list_of_string negative codepoints on
invalid UTF-8) is OWNER-GATED — no upstream filing by any session
without explicit owner approval."*

**Recommendation.** Keep Option A (already working, zero cost, zero
new trust surface). Option B is a one-line yes/no from the owner
whenever they want it filed — nothing here is time-sensitive since
the containment already holds.

## Gap 4 — the parked decode-encode theorem — RESOLVED this session

**What was missing.** `Parser.FastString.Spec.fst`'s own banner
recorded a theorem — `utf8_decode_all (utf8_bytes s) ==
FStar.String.list_of_string s` for every string `s` (encoding then
decoding recovers the original codepoints) — as "ATTEMPTED, PARKED"
after three failed proof attempts, each stalling at the same step:
getting the recursive function `utf8_decode_all_aux` to unfold at a
fully symbolic call site.

**Status: PROVED, 2026-08-10, branch `faststring-step4b`
(`Parser.FastString.Axioms.fst`, function
`utf8_decode_all_utf8_bytes_identity`).** Zero new axioms. The
technique that unstuck it: instead of asking the SMT solver to unfold
the recursive function automatically inside a separate induction
(what all three prior attempts tried), state the function's own
defining equation as a SEPARATE, non-recursive lemma
(`utf8_decode_all_aux_unfold`, proved by `= ()`) and CALL that lemma
explicitly at each induction step. Two structural inductions built on
top of it — one showing the decoder is prefix-oblivious
(`lemma_decode_all_aux_shift`), one walking the encoded character list
(`lemma_decode_all_aux_encode`) — close the theorem. Full account:
`Parser.FastString.Axioms.fst`'s own comment above
`utf8_decode_all_utf8_bytes_identity`.

**No decision needed here.** Listed for completeness and traceability
only, since Task B was scoped to include it. One small housekeeping
follow-up (not a decision): the proof currently lives as a private
helper inside `Parser.FastString.Axioms.fst`; moving it into
`Parser.FastString.Spec.fst`'s own lemma kit (replacing that file's
now-stale "ATTEMPTED, PARKED" banner) would make it reusable by other
proof modules. Tracked under Task C's obsolescence sweep.

## Decision table

| # | Gap | Status | Zero-new-axiom option | Owner-gated option | Recommendation | Owner answer |
|---|---|---|---|---|---|---|
| 1 | `String.sub` no content spec | OPEN | Migrate SPARQL 1.1 lexer's `substring` to `Parser.FastString`'s byte primitives (untried, size unknown, touches lexer indexing) | Add 1 new `assume val` stating `sub`'s content fact (immediate, permanent trust-surface item, needs its own issue) | Zero-axiom path is right long-term; owner should say whether to spend time trying it or take the fast trusted-rule path now | _pending_ |
| 2 | `String.concat` zero equations | FIXED, zero axiom, MERGED to `claude/main` | Already done (`Parser.FastString.ConcatSpec.fst`) | Not needed | None | _no decision needed_ |
| 3 | `list_of_string` negative codepoints on invalid UTF-8 | CONTAINED, zero axiom, on `claude/main` | Already done (defensive clamps, issue #374) | File upstream FStarLang/FStar report | Keep containment; file upstream only on explicit owner go-ahead (already OWNER-GATED, issue #376) | _pending (upstream filing only)_ |
| 4 | Parked decode-encode theorem | RESOLVED 2026-08-10 | Already done (`Parser.FastString.Axioms.fst`, branch `faststring-step4b`) | Not needed | None — optionally promote the lemma into `Parser.FastString.Spec.fst`'s own lemma kit later | _no decision needed_ |
