# 2026-08-11 — EverParse evaluation (task #50)

Owner steer: "Do it." (2026-08-11, on task #50: evaluate whether
factoidal should integrate EverParse). This doc answers that steer
directly. It supersedes nothing — it **builds on**
[`everparse.md`](everparse.md) (research-only, compiled 2026-04-25,
reading log at
[`2026-04-25-tav4-everparse-research-scratch.md`](2026-04-25-tav4-everparse-research-scratch.md))
and narrows that broad research into six specific yes/no questions
against factoidal's current architecture. Read `everparse.md` first
for the full component map, comparison table against Narcissus/
RecordFlux/Nail, and the 3DGen LLM angle — this doc does not repeat
that material except where a fact needs re-confirming for a
recommendation.

Every claim below is tagged **VERIFIED** (checked against a primary
source this session — repo file, official doc, or a peer-reviewed
paper abstract with an exact quote) or **UNVERIFIED** (network
returned nothing, a page 404'd, or the claim is inference rather than
a direct citation). Network access worked for GitHub raw files,
GitHub search, and the EverParse project pages this session; two
specific URLs 404'd (noted at point of use) — those are the only
network-blocked claims here, not a wholesale bypass.

## Summary table

| # | Question | One-line answer | Confidence |
|---|---|---|---|
| 1 | What is EverParse? | A framework (LowParse combinator library + 3D/QuackyDucky DSLs) that proves generated binary parsers are safe, correct, and non-malleable; extraction targets are C and Rust via KaRaMeL, not OCaml/JS/wasm. | VERIFIED |
| 2 | Fit — COTTAS binary surfaces | Structurally a good match (our delta-log/sidecar framing is exactly the magic+version+length+payload+checksum shape LowParse targets), but adopting it would add a second extraction pipeline that doesn't reach our OCaml/js/wasm targets without new FFI work our current plain-F* + hash-witness pattern doesn't need. | VERIFIED (structural comparison) / UNVERIFIED (no pilot run) |
| 3 | Fit — text parsers (N-Triples/Turtle/SPARQL) | Poor fit. LowParse's combinator inventory is binary tag-length-value; no UTF-8/text-grammar combinators found in the component inventory. Our `Parser.FastString`/`Parser.NTriples.Locality` proof program already gives the locality + round-trip properties we need, in the register (byte position facts, not string-equality facts) that this project already learned is the one Z3 can chain. | VERIFIED (component absence) / UNVERIFIED (no source-tree re-audit this session — relies on the 2026-04-25 GitHub-API listing) |
| 4 | Unicode/byte utilities | No evidence EverParse ships reusable UTF-8 codec facts. `Parser.FastString.Spec.fst`'s `utf8_decode_at`/`utf8_enc_char` (RFC 3629 codec, termination-guaranteed replacement-character fallback) has no EverParse counterpart found. | VERIFIED (absence in inventory), UNVERIFIED (exhaustive search not repeated this session) |
| 5 | Vendoring | Apache License 2.0 (same family as our HACL* precedent); actively maintained (release 2026-07-02, five weeks before this evaluation); large surface (~80 LowParse `.fst` files plus 3D/QuackyDucky/EverCBOR/EverCDDL/EverCOSign); F*-version coupling risk is real but its exact minimum version is UNVERIFIED (build.html 404s). | VERIFIED (license, activity) / UNVERIFIED (exact F* version floor) |
| 6 | Recommendation | **Do not adopt now.** Run the already-proposed one-week 3D pilot on a single small companion-file format (the delta-log entry/batch framing is the best candidate) before any real commitment; do not touch the text-parser stack. Extraction-target mismatch (C/Rust vs. our OCaml-native/js_of_ocaml/wasm_of_ocaml trio) is the decisive blocker, not F*-vs-cobbling — EverParse is F*, so rule #7 doesn't apply, but rule #11's "three targets from one module" property, which our current delta-log framing already has, is not something EverParse's proof-bearing layer gives us today. | VERIFIED (reasoning from cited facts) |

---

## 1. What EverParse is

**VERIFIED.** EverParse's own description (project page, fetched this
session): "EverParse is a framework for generating verified secure
parsers and formatters from domain-specific format specification
languages. ... LowParse, a verified library of parsing and formatting
combinators programmed and verified in F\* and Pulse."

Three front-ends compile down to LowParse:

- **3D** — a C-like DSL (`struct`, `casetype` for tagged unions,
  fixed-width integers, bitfields, byte-counted variable arrays,
  dependent fields) that compiles to a verified interpreter
  representation, then to C.
- **QuackyDucky** — an older RFC-table-style DSL; produces F\* files
  you then run through `fstar.exe` and KaRaMeL by hand. Its flagship
  case study is the full TLS 1.0–1.3 message-format set (293
  datatypes) integrated into miTLS.
- **EverCDDL** (2025-era) — CDDL → verified CBOR/COSE parsers via
  **PulseParse**, a separation-logic rewrite of LowParse.

**Verification guarantees, VERIFIED with exact quotes:**

- USENIX Security 2019 paper (the founding paper), verbatim: "The
  resulting code is verified to be safe (no overflow, no use after
  free), correct (parsing is the inverse of serialization) and
  non-malleable (each message has a unique binary representation)."
  Formally: `∀s. parse (serialize s) == Some s` and `∀b v. parse b ==
  Some v ⟹ serialize v == b`.
- PLDI 2022 paper adds "arithmetic safety" (length/offset arithmetic
  doesn't overflow) and "double-fetch freedom" — the 3D-generated C
  validator reads each input byte at most once, closing a
  time-of-check/time-of-use class of bug relevant to kernel-mode
  validators reading shared memory.
- PulseParse (2025, arXiv:2505.17335, Distinguished Artifact Award at
  ACM CCS 2025) adds separation-logic zero-copy reasoning, full
  bidirectional serialization, and a proved constant-stack-space
  recursive-format class (their Theorem 2.1) — the property that
  matters for adversarial deeply-nested input, which a naive
  recursive-descent parser is vulnerable to.

**Extraction targets, VERIFIED:** C (primary, via KaRaMeL) and Rust
(via KaRaMeL's newer Rust backend — `EverCBOR`/`EverCOSign` ship both
C and Rust flavours). The EverParse project page and doc index make
no mention of OCaml or JavaScript/wasm output for the LowParse
`Low.*`/Pulse implementation layer. **UNVERIFIED speculation, marked
as such**: LowParse also has a pure specification layer (`SLow.*`,
buffer-free) that in principle could extract to OCaml via
`fstar.exe --codegen OCaml` the same way our own pipeline works —
this session found no documentation or example of anyone actually
doing that, so it is a theoretical possibility, not a demonstrated
path.

This matters immediately for factoidal because our own extraction
targets, per the `ocaml-boundary` skill's own one-line summary, are
"OCaml native, js_of_ocaml, wasm_of_ocaml, KaRaMeL C" — **four**
targets, three of which EverParse's proof-bearing implementation layer
does not reach.

## 2. Fit — COTTAS binary surfaces (delta log, sidecars)

**Structural match: VERIFIED.** `skills/disk-storage-format/SKILL.md`
§1.1 (`docs/designissues` — read directly this session) tabulates our
companion-file magic numbers:

| File | Magic (LE u32) | Checksum |
|---|---|---|
| `<name>.dict` | `0x44544f43` ('COTD') | none |
| `<name>.presence` | `0x50544f43` ('COTP') | none |
| `.p.offsets` | `0x4f544f43` ('COTO') | none |
| `.po.presence` | `0x4f504f43` ('COPO') | none |
| `.s.offsets` | `0x53544f43` ('COTS') | none |
| `data.deltalog` entry | `0x31454C44` ('DLE1') | additive `simple_checksum` |
| `data.deltalog` batch | `0x31424C44` ('DLB1') | additive `simple_checksum` |
| `data.deltalog` header | `0x474F4C44` ('DLOG') | none |
| `data.compacted-epoch` | `0x31504543` ('CEP1') | additive `simple_checksum` |

Framing (from the same skill, §3.1, `RDF.Store.Columnar.DeltaLog.fst`):

```
delta_entry:  [magic u32][version u32][length u32][tag+fields][checksum u32]
delta_batch:  [magic u32][version u32][length u32][db_seq u64][db_epoch u64]
              [op_count u32][N entries back-to-back][checksum u32]
```

This is precisely the shape LowParse's `VLData`/`FLData`/`Sum` (tagged
union) combinators, or a small 3D spec, are built for — a
fixed-width tagged header followed by a length-delimited payload and
a trailer checksum. §5 of `everparse.md` (2026-04-25 research)
independently reached the same conclusion for the Parquet footer's
Thrift-compact framing, so this isn't a new observation — it's the
same structural argument applied to a different (and simpler, no
varints) format.

**What we already have, VERIFIED:** the hash-witness round-trip
pattern (`docs/designissues/2026-05-07-io-verification-and-third-party.md`,
read this session):

```fstar
val serialize : data -> Tot (list u8)
val parse     : list u8 -> Tot (option data)
val serialize_parse_roundtrip (d:data) : Lemma (parse (serialize d) == Some d)
val expected_digest : data -> Tot sha256_digest
let expected_digest d = sha256 (serialize d)
assume val write_bytes : path:string -> bytes:list u8 -> ML unit
assume val read_bytes  : path:string -> ML (list u8)
```

with the CI gate being a unit test that hashes both sides. This is
functionally a manual re-derivation of exactly the property EverParse
proves as a theorem — but with a load-bearing difference: **our
version is one plain F\* module, `Tot`, extracting cleanly to all
four of our targets** (the delta log itself is stated in
`current-state.md`, read this session, to run "natively, as
KaRaMeL-extracted C (12/12 demo), and under js_of_ocaml + wasm_of_ocaml
with IndexedDB persistence" — meaning we already reach KaRaMeL/C for
this exact layer, from the *same* F\* source that also extracts to
OCaml/js/wasm, without EverParse). EverParse's LowParse `Low.*`
implementation layer, by contrast, is Low\*-typed (buffers, not lists)
and its proof only extracts through KaRaMeL to C/Rust — reaching our
other three targets from it would mean either (a) FFI-binding the
generated C from OCaml, js_of_ocaml, and wasm_of_ocaml separately (three
new binding efforts, not one), or (b) staying on the unverified-for-OCaml
`SLow` spec layer noted as speculative in §1.

**Would LowParse strengthen or complicate our pattern?** Both,
genuinely:

- **Strengthens:** our hash-witness check is a CI *test* (generate
  sample data, round-trip, compare hashes) — it is not a universal
  F\*-proved theorem over all inputs the way
  `serialize_parse_roundtrip` plus a LowParse-style *parser* proof
  would be. Our `serialize`/`parse` pair for the delta log does carry
  its own `lemma_delta_entry_roundtrip` (stage 1, `DeltaLog.fst` §5,
  cited in the disk-storage-format skill) — so we already have the
  F\*-proved half; what we lack that EverParse's C path adds is
  non-malleability (uniqueness of the accepted byte-string per value)
  and double-fetch freedom, neither of which our checksum-based
  crash-detection framing currently claims or needs (our framing's
  job is crash-torn-write rejection, not adversarial-input defense —
  the delta log is our own process's local durability mechanism, not
  a network-facing message format parsed from an untrusted peer).
- **Complicates:** a LowParse port would be a second, parallel
  byte-format spec for the same file (one in plain F\* `Tot` today,
  one in Low\*/Pulse if ported), doubling the surface to keep in
  sync, and — per the target-mismatch point above — narrowing where
  the *proof-bearing* version of the format actually runs to C/Rust
  only, while the CLI (`bin/factoidal-cli/factoidal_cli.ml`) and the
  browser/wasm delta-log consumers would still need the plain-F\*
  version or an FFI shim.

**Conclusion for this question:** EverParse would give a *stronger*
theorem for the *narrowest* part of the trust surface (companion-file
framing) at the cost of a *narrower* deployment (C/Rust only, vs. our
current four targets from one source). Not a clean win either way —
this is what makes it a genuine one-week-pilot question, not a
slam-dunk adopt or reject.

## 3. Fit — text parsers (N-Triples, Turtle, SPARQL)

**Poor fit, VERIFIED at the level of "no evidence found", not
exhaustively disproved.** LowParse's combinator inventory, per the
component map in `everparse.md` §2 (built from an actual GitHub
directory listing on 2026-04-25, not re-audited this session):
`Int.fst`, `BoundedInt.fst`, `Combinators.fst`, `Sum.fst`, `Enum.fst`,
`Array.fst`, `List.fst`, `FLData.fst`, `VLData.fst`, `BitFields.fst`,
`BCVLI.fst`, `DER.fst` — every name is binary/tag-length-value
shaped. A targeted web search this session for "LowParse UTF-8
string parser combinator" returned no EverParse-specific result. 3D's
own type system is fixed-width integers, bitfields, and byte-counted
arrays — no grammar/regex/character-class primitive of the kind a
Turtle or SPARQL tokenizer needs (PN_CHARS ranges, `\u` escapes,
`langtag`, numeric literal shapes).

Our own text-parser stack, read directly this session:

- `Parser.FastString.Spec.fst` — a from-scratch RFC 3629 UTF-8 codec
  over `list byte` (`utf8_decode_at`, `utf8_enc_char`), with a
  documented single-decoder finding (issue #374) about why
  `list_of_string` can't be fully eliminated without a new
  `assume val`, and a defensive clamp at the encode boundary against
  a confirmed extraction-time crash (`BatUChar.Out_of_range`).
- `Parser.NTriples.Locality.fst` — the 2026-08-11 pilot of a
  "parser-locality induction program": proving `scan_iri_end` and
  friends behave identically on a substring embedded at an arbitrary
  offset inside a larger buffer, stated over **byte-position facts**
  rather than string equalities, specifically because (documented in
  the same file's banner, citing `RDF.NTriples.RoundTrip.fst`'s Part
  6) `"" ^ s == s` and associativity of `FStar.String.strcat` for
  symbolic strings both fail to discharge via plain `()` — "Z3 has no
  native associativity/identity theory for `FStar.String.strcat` over
  symbolic operands."

That last point is the crux of the comparison: this project already
independently discovered that byte-position arithmetic is the
register Z3 can chain, and string-identity is the register it can't —
which is functionally the same insight LowParse is built around
(everything indexed by buffer offset, nothing by string-splicing).
The difference is that LowParse gets there through Low\*'s
buffer-pointer discipline (extraction-enforced), while
`Parser.NTriples.Locality.fst` gets there through explicit
`fs_byte_index`/`fs_byte_length` lemmas over a `list byte`-backed
abstraction that still extracts to OCaml. **Migrating the text
parsers to LowParse would mean re-deriving properties we already
have, in a framework whose combinator vocabulary has no term for
"IRI", "PN_CHARS", or "language tag", and whose implementation layer
does not reach OCaml/js/wasm.** The honest cost/benefit: migration
cost is real (rewrite four parsers + their KaRaMeL wiring) against a
benefit we've already captured by other means for the properties that
matter here (locality, termination, round-trip). Not recommended.

## 4. Unicode/byte utilities

**VERIFIED (absence), UNVERIFIED (not an exhaustive re-search this
session).** No EverParse component in `everparse.md`'s component map
or this session's searches names a UTF-8 codec, grapheme handling, or
general Unicode utility module. LowParse's `Endianness.fst` handles
byte-order (BE/LE) for fixed-width integers — not character encoding.
`Parser.FastString.Spec.fst`'s RFC 3629 codec (§3 above) therefore has
no EverParse counterpart to adopt or compare against on this specific
question — the owner's earlier ask ("does EverParse ship reusable
byte/UTF-8 facts") comes back negative on current evidence, but this
session did not walk the full `src/lowparse/` file tree byte-by-byte
to rule out a narrowly-named module; that would be part of the
one-week pilot's due diligence if a pilot is run.

## 5. Vendoring

- **License: VERIFIED.** Apache License 2.0, Microsoft Corporation.
  Same license family as our HACL\* precedent (also Apache 2.0, per
  `docs/designissues/2026-05-07-io-verification-and-third-party.md`),
  so no new license-compatibility question versus our existing
  crypto-vendoring policy.
- **Size: VERIFIED.** `everparse.md` §2 (GitHub-API-derived, 2026-04-25):
  `src/lowparse/` alone is ~80 `.fst` files; `LowParse.Low.Base.fst`
  is 64KB, `LowParse.Low.Sum.fst` 76KB; `src/3d/Binding.fst` is 96KB.
  This is not a small vendor-in on the scale of our RFC-4122 UUID
  module — it is a framework, closer in scale to vendoring a second
  standard library.
- **Maintenance activity: VERIFIED.** Release history fetched this
  session: v2025.12.10, v2026.02.04, v2026.02.25, v2026.03.21,
  v2026.07.02 (most recent — five weeks before this evaluation's
  2026-08-11 date). Actively maintained, not abandoned.
- **F\*/z3 version coupling: partially VERIFIED, partially
  UNVERIFIED.** We pin F\* `2025.12.15` exactly and z3 `4.13.3`
  exactly (`skills/fstar-env/SKILL.md`, iron rule #12). The same skill
  records a real incident, quoted directly: "2026-07-03 (opam default
  gave 2026.03.24 vs CI's 2025.12.15" — i.e., this project has already
  been bitten once by an F\* version drift of exactly this kind, four
  months apart. EverParse's v2026.03.21 changelog entry reads "Upgrade
  to F\* Universes" (VERIFIED via GitHub releases fetch) — a stated
  F\* dependency bump whose exact minimum version this session could
  not pin down: `https://project-everest.github.io/everparse/build.html`
  returned HTTP 404 twice this session (not a network block — the page
  does not exist at that path; the correct build-instructions location
  was not located in the time available). Given F\*'s own latest
  stable release is v2026.04.17 (WebSearch, this session) and
  EverParse's latest release postdates that, it is a reasonable but
  **UNVERIFIED** inference that EverParse's current `master` requires
  an F\* newer than our pinned 2025.12.15 — anti-pattern #5 in this
  project's own list is explicitly "Symlinks/hacks for version
  mismatches (esp. z3) — fix the env", so an EverParse adoption would
  need either bumping our pin (untested blast radius across ~55 `.fst`
  modules) or vendoring an EverParse commit old enough to match
  2025.12.15 (untested whether one exists with the guarantees we'd
  want).
- **Third-party policy fit: VERIFIED.** `2026-05-07-io-verification-
  and-third-party.md` already names EverParse explicitly under
  "keep an eye on, don't depend on yet" and proposes the vendoring
  directory shape (`formal/third_party/everparse/`) that would apply.
  The actual vendored-dependency precedent in this repo today is
  HACL\*, at `third_party/hacl/` (VERIFIED — `ls` confirms the
  directory this session), one level shallower than the design doc's
  proposed `formal/third_party/` path — worth reconciling if a real
  EverParse vendoring effort starts, so the two third-party
  dependencies live at the same tree depth.

## 6. Recommendation

**Do not adopt now.** The three strongest facts driving this:

1. **Extraction-target mismatch is structural, not a version hiccup.**
   EverParse's proof-bearing implementation layer (LowParse `Low.*`
   Low\*/Pulse code) ships to C and Rust only, via KaRaMeL — never
   OCaml, js_of_ocaml, or wasm_of_ocaml (VERIFIED, §1). Factoidal
   needs all four targets for nearly everything, per `ocaml-boundary`
   and confirmed concretely for the delta log specifically, which
   already reaches all four *without* EverParse, from one plain-F\*
   `Tot` module (VERIFIED, §2, `current-state.md` quote). Adopting
   EverParse for a companion-file format would not replace that
   four-target module — it would add a fifth, C/Rust-only, parallel
   spec of the same bytes, which is a net increase in surface for a
   net decrease in reach, unless the OCaml/js/wasm consumers are
   changed to FFI-bind the KaRaMeL output instead (untested, and a
   nontrivial build-system addition per target).
2. **The properties we're missing (non-malleability, double-fetch
   freedom) aren't the ones our current gaps are in.** Our delta log
   already has an F\*-proved round-trip lemma
   (`lemma_delta_entry_roundtrip`) plus a crash-safety argument
   measured at 320 kill/recovery trials across three stages (VERIFIED,
   `disk-storage-format` skill §3.2, read this session) — the risk
   this format defends against is a torn write from our own process
   crashing, not an adversarial network peer forging a message. The
   properties EverParse adds beyond what we have (non-malleability,
   TOCTOU/double-fetch freedom) matter most for kernel-mode parsers
   validating untrusted network input (the Hyper-V case study,
   `everparse.md` §4) — a threat model factoidal's local on-disk
   companion files don't currently face. The gap that *would* matter —
   the SPARQL Protocol-over-HTTP surface, an actually untrusted-input
   boundary — is the one place `2026-05-07-io-verification-and-
   third-party.md` already flagged EverParse as "the right tool for
   ... the SPARQL Protocol-over-the-wire stack," and that surface is
   out of this evaluation's scope (task #50 is about the parser/
   storage question, not Protocol).
3. **Text parsers are the wrong shape for LowParse's vocabulary, and
   we've already independently solved the hard part.** LowParse's
   combinators are binary/TLV-typed with no string-grammar primitive
   (VERIFIED absence, §3); our own `Parser.NTriples.Locality.fst`
   pilot (landed the same day as this evaluation, 2026-08-11) already
   proves the exact byte-position-vs-string-identity distinction that
   makes LowParse's approach work, using a `list byte`-backed
   abstraction that keeps our OCaml/js/wasm extraction intact. There
   is no case here for touching the text-parser stack.

**Concrete first step, if a pilot is ever run (not this task):** run
the one-week-timeboxed 3D pilot `everparse.md` §6 already proposed —
express the delta-log entry/batch framing (the simplest fixed
magic+version+length+payload+checksum shape in our tree, no varints,
no recursion, four fields) as a 3D spec, compile it through the real
EverParse toolchain against our pinned F\* version (first checking
whether that version compiles EverParse `master` at all — a fast,
cheap first probe that resolves the biggest UNVERIFIED claim in §5
before spending the rest of the week), and write up a report — not
merged code. This is the same recommendation the 2026-04-25 research
already reached for the Parquet footer; it has not been actioned in
the four months since, and this evaluation finds no new fact that
changes the "pilot before commit" shape of that answer, only a
sharper picture of exactly which companion file is the best pilot
subject.

**What we would explicitly NOT get from adopting EverParse today:**
reach into text/Turtle/SPARQL parsing (wrong tool class, §3); a free
path to OCaml/js_of_ocaml/wasm_of_ocaml for any format ported to it
(§1, §2); resolution of any existing I/O `assume val` that isn't a
byte-layout question (e.g. `parquet_zstd_decompress_hex` has no
EverParse-adjacent answer — zstd is a compression algorithm, not a
format grammar); or a smaller third-party surface than we already
carry via HACL\* (EverParse is the larger of the two by file count,
§5).

**Rule #7 note, stated plainly per the task brief:** EverParse
generates F\* (and, via QuackyDucky, hand-finished F\*) — adopting it
would not violate iron rule #7 ("no cobbling... add functionality in
F\* first, then extract") the way a hand-written OCaml/Rust
reimplementation would. The blocker identified here is entirely the
extraction-target mismatch (§1, §2), not a source-of-truth objection.

## References

- [`everparse.md`](everparse.md) — the 2026-04-25 broad research doc
  this evaluation narrows and updates; read first for the full
  component map and the Narcissus/RecordFlux/Nail comparison table.
- [`2026-04-25-tav4-everparse-research-scratch.md`](2026-04-25-tav4-everparse-research-scratch.md)
  — that doc's reading log and raw quotes.
- [`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md)
  — the hash-witness round-trip pattern (§2 above) and the existing
  "keep an eye on, don't depend on yet" EverParse verdict this doc
  either confirms or revises per question.
- `skills/disk-storage-format/SKILL.md` — companion-file magic-number
  table and delta-log framing (§2's structural comparison).
- `skills/crypto-policy/SKILL.md`, `third_party/hacl/` — the HACL\*
  vendoring precedent (§5).
- `skills/fstar-env/SKILL.md` — the pinned F\*/z3 versions and the
  2026-07-03 version-drift incident (§5).
- `formal/fstar/Parser.FastString.Spec.fst`,
  `formal/fstar/Parser.NTriples.Locality.fst` — read directly this
  session for §3 and §4.
- `docs/claude-rules/current-state.md` — the KaRaMeL-pipeline-green
  status and the delta log's tri-target extraction claim (§2).
- EverParse project page: https://project-everest.github.io/everparse/
- EverParse README (raw):
  https://raw.githubusercontent.com/project-everest/everparse/master/README.md
- EverParse releases: https://github.com/project-everest/everparse/releases
- USENIX Security 2019 paper:
  https://www.usenix.org/system/files/sec19-ramananandro_0.pdf
- Microsoft Research abstract page (verified quote source, §1):
  https://www.microsoft.com/en-us/research/publication/everparse/
