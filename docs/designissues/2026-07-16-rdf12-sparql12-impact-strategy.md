# RDF 1.2 / SPARQL 1.2 — impact & upgrade strategy

**Status:** investigation (no engine code changed here — vendored suites,
measured baseline, strategy). **Epic:** [#305](https://github.com/danbri/factoidal/issues/305).
**Date:** 2026-07-16.

## Why now — the un-parking

Owner directive, 2026-07-16 (quoted verbatim, per CLAUDE.md "Reading
owner steers"):

> "Launch an rdf 1.2 sparql 1.2 everything (syntaxes…) 1.2 investigation
> into impact and strategy of upgrading our entire effort to support rdf
> 1.2isms."

This **explicitly un-parks** the earlier prioritization. The standing
ledger line (owner, 2026-07-09,
[`docs/claude-rules/w3c-completeness-ledger.md`](../claude-rules/w3c-completeness-ledger.md))
read:

> "**RDF 1.2 / RDF-star parked** for now."

and the 2026-07-11 north-star note carried "RDF 1.2/star parked;
protocols deprioritized". Per the CLAUDE.md rule that "'X deprioritized'
is an ordering decision, never a scope prohibition", the 2026-07-16
directive re-orders 1.2 back into active scope. Once this investigation
is accepted, the ledger's "parked" lines should be updated to "in
progress under #305" (obsolescence sweep).

Prior compatibility stub this supersedes:
[`rdf12-compatibility.md`](rdf12-compatibility.md) (a 25-line
hold-the-line policy — keep 1.1 normative, collect 1.2 examples). That
policy is now upgraded to an implementation roadmap.

## Part A — Spec landscape (as of 2026-07-16)

Stability drives the whole strategy: build confidently on the
**Candidate Recommendations**; build the still-**Working-Draft**
concrete syntaxes behind a version flag so churn doesn't regress 1.1.

| Document | Status (2026) | Notes |
|---|---|---|
| [RDF 1.2 Concepts & Abstract Data Model](https://www.w3.org/TR/rdf12-concepts/) | **CR Snapshot, 07 Apr 2026** (not advancing before 05 May 2026) | Triple terms as a 4th term kind; `rdf:dirLangString`; two conformance levels |
| [RDF 1.2 Semantics](https://www.w3.org/TR/rdf12-semantics/) | **CR Snapshot** (implementations invited alongside Concepts) | Transparent triple-term denotation |
| [RDF 1.2 N-Triples](https://www.w3.org/TR/rdf12-n-triples/) | **WD, 15 May 2026** | Minimal grammar; `<<( )>>` triple terms, `--ltr`/`--rtl` dir |
| [RDF 1.2 N-Quads](https://www.w3.org/TR/rdf12-n-quads/) | **WD, 28 May 2026** | N-Triples 1.2 + graph name |
| [RDF 1.2 Turtle](https://www.w3.org/TR/rdf12-turtle/) | **WD, 28 May 2026** | Reifying triple `<< s p o ~reifier >>`, triple term `<<( s p o )>>`, annotation syntax |
| [RDF 1.2 TriG](https://www.w3.org/TR/rdf12-trig/) | **WD, 28 May 2026** | Turtle 1.2 syntax + datasets |
| [RDF 1.2 XML Syntax](https://www.w3.org/TR/rdf12-xml/) | **WD** | Triple terms + reifier rules; processing model now emits terms/triples directly (not N-Triples) |
| [SPARQL 1.2 Query](https://www.w3.org/TR/sparql12-query/) | **WD, Jun 2026** | Triple-term patterns; `TRIPLE`/`isTRIPLE`/`SUBJECT`/`PREDICATE`/`OBJECT`; `VERSION` |
| [SPARQL 1.2 Update](https://www.w3.org/TR/sparql12-update/) | **WD** | Update over triple terms |
| [SPARQL 1.2 Protocol](https://www.w3.org/TR/sparql12-protocol/) | **CR, 07 Apr 2026** | Largely 1.1-compatible; version param |
| [SPARQL 1.2 Service Description](https://www.w3.org/TR/sparql12-service-description/) | **CR, Apr 2026** | Feature-advertisement vocabulary |
| [SPARQL 1.2 Federated Query](https://www.w3.org/TR/sparql12-federated-query/) | **WD** | SERVICE over 1.2 |
| [SPARQL 1.2 Results JSON](https://www.w3.org/TR/sparql12-results-json/) / [CSV-TSV](https://www.w3.org/TR/sparql12-results-csv-tsv/) | **WD** | Encoding of triple-term bindings |
| RDFC-1.0 canonicalization | **REC (2024)** | The rdf-canon suite is being extended for 1.2; the rdf12 c14n fixtures cover canonical NT/NQ form incl. dirlang + triple terms |
| JSON-LD | 1.1 is REC; triple-term story in progress | Listed as a concrete RDF syntax; JSON-LD's `@direction` already models base direction at context level |

### The load-bearing 1.2isms, precisely

1. **Triple terms / reifying triples.** A triple term is a **4th kind of
   RDF term** (alongside IRI, blank node, literal), usable **only in the
   object position** of another triple. It is written `<<( s p o )>>`.
   Reification is expressed by the `rdf:reifies` predicate: `<reifier>
   rdf:reifies <<( s p o )>> .` The **reifier** (the subject) denotes
   something about the triple term's proposition. Triple terms are
   **transparent** — the RDF terms inside a triple term have the same
   denotation as when they appear in an asserted triple.

   **How this differs from old RDF-star quoted triples** (the parked
   work): RDF-star's `<< s p o >>` quoted triple was **referentially
   opaque** and could occupy **subject or object**; it conflated the
   triple and the statement-about-it. RDF 1.2 splits these: `<<( )>>`
   (double-paren) is the transparent triple *term*, always in object
   position; the reification relationship is carried explicitly by
   `rdf:reifies`. **The old `<< s p o >>` subject-quoted form is now a
   syntax error** — our vendored rdf12 negative-syntax fixtures assert
   exactly this (`ntriples12-bad-reified-syntax-*`).

2. **Directional language-tagged strings.** New datatype
   `rdf:dirLangString`: a literal carrying a BCP47 language tag **and** a
   base direction (`ltr` or `rtl`), for bidirectional-text presentation.
   N-Triples lexical form: `"..."@en--ltr`. This breaks the RDF 1.1
   invariant "lang tag iff `rdf:langString`".

3. **Version announcement.** A media-type parameter plus an in-line
   `VERSION` production (Turtle/TriG/SPARQL) declaring the document's RDF
   version.

4. **Conformance levels.** Full (with triple terms) vs Basic (without).

5. **SPARQL 1.2 syntax + functions.** Triple-term patterns in graph
   patterns; new builtins `TRIPLE(s,p,o)` (constructs a triple term),
   `isTRIPLE(x)` (test), `SUBJECT`/`PREDICATE`/`OBJECT` (accessors);
   `VERSION` declaration; results-format encoding of triple-term
   bindings.

## Part B — Vendored suites + measured baseline

### Vendoring

The RDF 1.2 and SPARQL 1.2 W3C suites are **already vendored** — they
live in the `w3c` git submodule (`third_party/testing/w3c`), the same
`w3c/rdf-tests` upstream that carries the 1.1 suites. Provenance (commit
`35c503a`, 2026-02-26; W3C Test Suite License + W3C 3-clause BSD)
recorded in
[`third_party/testing/w3c-rdf12-PROVENANCE.md`](../../third_party/testing/w3c-rdf12-PROVENANCE.md).
No files were copied out of or edited in the submodule (vendoring
policy: never edit vendored files).

- `third_party/testing/w3c/rdf/rdf12/{rdf-n-triples,rdf-n-quads,rdf-turtle,rdf-trig,rdf-xml,rdf-semantics}/`
- `third_party/testing/w3c/sparql/sparql12/`

The rdf12 syntax/eval manifests use the **same `rdft:` test-type
vocabulary as rdf11** (`TestNTriplesPositiveSyntax`,
`TestTurtleEval`, …); sparql12 uses the **same `mf:` types as
sparql11** (`PositiveSyntaxTest`, `QueryEvaluationTest`, …). So the
committed `w3c_runner` reads them without a manifest-vocabulary change.

### How the baseline was measured (no engine change)

The runner's RDF/SPARQL base directories are compiled-in as
`third_party/testing/w3c/rdf/rdf11` and `.../sparql/sparql11`, and
`read_manifest` does **not** follow `mf:include` (the rdf12 suite-root
manifests are include-lists). So the census was taken by an
**invocation-layer symlink only**: a scratch working directory whose
`.../rdf/rdf11` symlinks to the rdf12 **leaf** manifests
(`.../rdf-n-triples/syntax`, `.../rdf-turtle/eval`, …) and whose
`.../sparql/sparql11` symlinks to `sparql12`. The committed
`bin/linux-x86_64/w3c_runner` was then run from that directory. No
binary rebuilt, no engine or runner source touched. This exercises the
**strict, in-process F\* parsers** (`parse_ntriples_strict`,
`parse_turtle_fstar`, eval-compare against expected N-Triples) — a truer
picture than the lenient `factoidal dump` CLI, which silently skips
unparseable lines.

### Census — current 1.1 engine vs W3C RDF/SPARQL 1.2 suites

| Suite | pass | fail | skip | out of |
|---|---|---|---|---|
| **RDF 1.2 syntax** (parse accept/reject) | **148** | **10** | 0 | **158** |
| &nbsp;&nbsp;rdf-n-triples/syntax | 25 | 4 | 0 | 29 |
| &nbsp;&nbsp;rdf-n-quads/syntax | 25 | 2 | 0 | 27 |
| &nbsp;&nbsp;rdf-turtle/syntax | 65 | 2 | 0 | 67 |
| &nbsp;&nbsp;rdf-trig/syntax | 33 | 2 | 0 | 35 |
| **RDF 1.2 eval** (parse → N-Triples compare) | **14** | **70** | 0 | **84** |
| &nbsp;&nbsp;rdf-turtle/eval | 4 | 25 | 0 | 29 |
| &nbsp;&nbsp;rdf-trig/eval | 0 | 25 | 0 | 25 |
| &nbsp;&nbsp;rdf-xml/eval | 10 | 20 | 0 | 30 |
| **RDF 1.2 canonicalization** (NT/NQ c14n) | — | — | — | 86 (no runner handler for `TestN*PositiveC14N`; unsupported) |
| **RDF 1.2 semantics** (entailment) | — | — | — | 74 (regime not exercised in this census) |
| **SPARQL 1.2** | **73** | **158** | **20** | **251** |
| &nbsp;&nbsp;syntax-triple-terms-positive | 0 | 95 | 18 | 113 |
| &nbsp;&nbsp;syntax-triple-terms-negative | 63 | 0 | 2 | 65 |
| &nbsp;&nbsp;eval-triple-terms | 1 | 40 | 0 | 41 |
| &nbsp;&nbsp;lang-basedir | 3 | 8 | 0 | 11 |
| &nbsp;&nbsp;version | 3 | 6 | 0 | 9 |
| &nbsp;&nbsp;codepoint-escapes | 2 | 6 | 0 | 8 |
| &nbsp;&nbsp;expression | 0 | 1 | 0 | 1 |
| &nbsp;&nbsp;syntax | 0 | 2 | 0 | 2 |
| &nbsp;&nbsp;grouping | 1 | 0 | 0 | 1 |

### What the split means (the impact measurement)

- **Two failure modes.** The RDF **line-parsers silently drop** lines
  they can't parse — a positive-syntax triple-term file returns success
  with **0 triples emitted**, so it "passes" the positive-syntax test by
  *not erroring* while losing all triple-term content. The **eval**
  suites strip that mask: "Triples mismatch: expected N, got 0". The
  **SPARQL** parser is the opposite — it **hard-rejects** the new
  syntax, so **0 of 113** triple-term positive-syntax tests pass.
  ⚠️ Read the 148/158 RDF-syntax number with this caveat: it overstates
  real support. Eval (14/84) and SPARQL (73/251) are the honest floors.

- **All 10 RDF-syntax failures are base-direction negatives** the parser
  fails to reject: `undefined base direction`, `upper case LTR`, `bad
  language tag`, `missing language tag and direction`. The parser
  accepts `"..."@en--ltr` lexically but does **not** validate the
  direction token — an early, cheap correctness win.

- **The eval failures are uniform** — "got 0" / partial-graph: reifiers,
  annotation blocks, and nested triple terms all vanish.

- **rdf-xml eval 10/30** — the 10 passing are 1.1-compatible fixtures;
  the 20 fails need the RDF/XML 1.2 triple-term + reifier productions.

### Latent 1.2 / star artifacts in our tree (grep census)

> **HISTORICAL (pre-landing census).** This section captured the tree
> BEFORE the Wave 2/3 landings in this same doc (and commits
> `ee3ea837`/`9ceaa1c4`). The "no real triple-term or dirLangString
> support exists" line below is no longer true — `RDF.Term.T_TripleTerm`
> and `text_direction` shipped and are verified (RDF 1.2 212/0). Kept for
> provenance; read the Wave 2 landing section further down for current state.

Original census text (minimal — no real triple-term or dirLangString support existed at the time):

- `formal/fstar/RML.Mapping.fst:54` — "RML-star (Stage 11, blocked on an
  RDF-star term type)." The term-model gap is already a known blocker
  for another suite.
- `formal/fstar/Parser.RDFXML.fst:697` — comment: "RDF 1.2 is
  introducing triple terms as a cleaner [mechanism]".
- `formal/fstar/JSONLD.Context.fst:221` — JSON-LD context `@direction`
  (ltr/rtl) is already parsed at the JSON-LD layer, but the RDF term
  model it lowers into carries no direction, so it cannot round-trip.
- Other `reifies` hits (`RIF.Core.Translation`, `Parser.ShExC`) are
  generic prose, not RDF reification.

## Part C — Per-component impact

### Term model — the deepest cut

`formal/fstar/RDF.Term.fsti`:

- `:88` `noeq type literal = { lexical_form; datatype; lang_tag }` — **no
  base-direction field**.
- `:96` `well_formed` invariant: lang tag present **iff** datatype is
  `rdf:langString`. `rdf:dirLangString` breaks this two-way rule.
- `:115` `noeq type rdf_term = T_IRI | T_BNode | T_Literal` — **no
  triple-term constructor**.
- `:122` `subject`, plus `rdf_term_eq` / decidable-equality &
  reflexivity lemmas (`:397+`).

**Blast radius:** **59** `.fst`/`.fsti` files pattern-match `T_IRI` /
`T_BNode` / `T_Literal` directly (the `RDF.Term.fst` header itself notes
"RDF.Indexed.fsti: 53+ modules pattern-match directly"). Adding
`T_TripleTerm` makes every one of those matches **non-exhaustive** — F\*
will refuse to verify until each is handled. This is a feature: the
verifier is the exhaustive change-tracker, so there is no silent
fall-through, but it means P0 touches dozens of files and their proofs
(equality, canonical ordering, hashing).

Design choice to settle in P0: represent the triple term as a nested
`(subject, predicate, object)` — which makes `rdf_term` mutually
recursive — and add `direction : option dir` to `literal` (with
`well_formed` extended to the three-way rule). The recursion touches
every totality/termination proof over terms.

### Parsers (all in F\*, per iron rule #4)

- `Parser.NTriples` — smallest grammar: add `<<( )>>` object production,
  `@lang--dir` direction token + **validation** (fixes the 10 negative
  fails), reject legacy `<< >>`. Currently **silently skips** bad lines;
  1.2 negative tests need real rejection in the strict path.
- `Parser.Turtle` / `Parser.TriG` — reifying triple `<< s p o ~reifier
  >>`, triple term `<<( )>>`, annotation syntax, `VERSION`. Largest
  grammar delta.
- `Parser.NQuads` — N-Triples 1.2 delta + graph label.
- `Parser.RDFXML` — 1.2 triple-term elements + reifier rules; the
  processing model shifts to emitting terms directly.

### Serializers

N-Triples / N-Quads / Turtle pretty-printer / dump-* must emit `<<( )>>`
and `@lang--dir`. Canonical NT/NQ form (the 86 c14n fixtures) needs a
canonical serializer covering dirlang + triple terms.

### SPARQL — `SPARQL11.Parser` + `SPARQL11.Algebra`

- Parser: triple-term graph patterns, `TRIPLE`/`isTRIPLE`/`SUBJECT`/
  `PREDICATE`/`OBJECT`, `VERSION`. Watch anti-patterns #7/#8 (parser↔AST
  mismatch; grep `SPARQL11_Parser.ml` first).
- Algebra: triple terms as bindable values; the accessor/constructor
  functions; matching semantics for triple-term patterns; interaction
  with the existing promoted-type handling (anti-pattern #6).
- Results formats (SRJ/SRX/CSV/TSV): encode triple-term bindings.

### COTTAS on-disk format

`skills/disk-storage-format` — the base file + 11 sidecars use a term
dictionary. Triple terms (nested terms) and dirlang literals need a
dictionary encoding + a **format-version story**: a magic/version bump
(`COTD`/`COTP`/… families) and a read-path that refuses or migrates
older files. This is a compatibility surface of its own; keep it in a
late phase so the term model is settled first.

### RDFC-1.0 canonicalization

`RDF.Canonical.fst` — canonicalizing triple terms means the
hash-per-term and quad-ordering must recurse into nested terms; dirlang
literals get a canonical lexical form. The rdf-canon WG is still
extending the spec for 1.2, so treat as **WD-tracking**.

### Insulated-but-verify layers

OWL / SHACL / ShEx / RIF / CSVW operate above the term model and should
be **mostly insulated** — but each pattern-matches `rdf_term`, so P0's
non-exhaustive-match wave reaches them. They need a `T_TripleTerm` arm
(most plausibly: treat as opaque / not-applicable) to keep verifying.
RML-star (`RML.Mapping.fst`) is explicitly waiting on the term type and
**unblocks** once P0 lands. Confirm no OWL/SHACL semantics silently
depend on the closed-world "three term kinds" assumption.

### Extraction targets

OCaml native, js_of_ocaml, wasm_of_ocaml, KaRaMeL C all re-extract from
the same F\*; a recursive `rdf_term` is fine for OCaml/JS but the
KaRaMeL C path needs a heap representation for the recursion (no
`inline_for_extraction` flattening) — a C-build risk to note, not block.

### Test-suite / scoring / dashboard wiring

`w3c_runner` needs a real rdf12/sparql12 mode (today it is rdf11/
sparql11 hardcoded + no `mf:include` following). Add rdf12 suite
discovery, `mf:include` resolution, and `TestN*PositiveC14N` +
dirlang-eval handlers; wire scores into `docs/test-results` and the
dashboard as separate 1.2 rows so 1.1 floors stay legible.

## Phased strategy

Ordering principle: **term model first** (everything roots there), then
the **minimal grammar** (N-Triples) to shake out the model cheaply, then
richer syntaxes, then SPARQL, then storage, then semantics. dirLangString
validation is an **orthogonal early win** folded into P0/P1.

**Compat stance (the regression net).** 1.1 documents MUST keep parsing
**byte-identically**. The floors below are the net: **RDF 1.1 = 1031
pass, 0 fail; SPARQL 1.1 = 631 pass, 0 fail** (combined 1662, 0 fail;
`docs/test-results/latest.json`, 2026-07-16). Every phase gate includes
"1.1 floors unchanged". 1.2 features ship behind a version flag while
their spec is WD, so WD churn cannot move a 1.1 number.

Per-suite 1.1 floors (RDF): n-triples 70, n-quads 87, turtle 313, trig
356, rdf-xml 166, rdf-mt 39.

| Phase | Scope | Commit-sized units | Gate |
|---|---|---|---|
| **P0** Term model | `RDF.Term.fsti`: add `T_TripleTerm` (recursive) + `literal.direction`; extend `well_formed`; fix eq/ord/hash lemmas; add `T_TripleTerm` arm to the ~59 match sites | ~6–10 (term type + lemmas; then batches of match-site fixes by module cluster: parsers, canonical, OWL/SHACL/ShEx, storage) | Whole tree verifies (no `--lax`); **1.1 floors unchanged**; RML-star unblocks |
| **P1** N-Triples 1.2 + dirlang | `Parser.NTriples` strict: `<<( )>>` object, `@lang--dir` + **direction validation**, reject legacy `<<>>`; NT serializer | ~4–6 | nt-syntax **29/29**; 10 base-dir negatives now rejected; nt 1.1 floor 70 held |
| **P2** Turtle + TriG 1.2 | Reifier `~`, annotation, `<<( )>>`, `VERSION`; serializers | ~6–10 | turtle-syntax 67→67, turtle-eval 29, trig-eval 25 climbing; 1.1 turtle 313 / trig 356 held |
| **P3** N-Quads 1.2 | `Parser.NQuads` delta + serializer | ~2–3 | nq-syntax 27/27; nq 1.1 floor 87 held |
| **P4** RDF/XML 1.2 | `Parser.RDFXML` triple-term + reifier; term-emitting model | ~4–6 | rdf-xml-eval 30 climbing; 1.1 rdf-xml 166 held |
| **P5** Serializers + c14n + RDFC | Canonical NT/NQ (86 c14n fixtures); RDFC-1.0 triple-term recursion + dirlang canonical form | ~4–6 | c14n 86 exercised; RDFC-1.0 REC suite floor held |
| **P6** SPARQL 1.2 syntax | `SPARQL11.Parser`: triple-term patterns, `VERSION` | ~4–6 | sparql12 syntax-triple-terms-positive 113 climbing; **SPARQL 1.1 631 floor held** |
| **P7** SPARQL 1.2 functions + algebra | `TRIPLE`/`isTRIPLE`/`SUBJECT`/`PREDICATE`/`OBJECT`; matching semantics; results-format encoding | ~5–8 | eval-triple-terms 41 + version 9 + lang-basedir 11 climbing |
| **P8** COTTAS format-version | Dictionary encoding of triple terms + dirlang; magic/version bump; refuse/migrate old files | ~4–6 | on-disk round-trip suite; old-file read path defined |
| **P9** RDF 1.2 semantics | Entailment over triple terms; rdf-semantics regime | ~4–6 | rdf-semantics 74 exercised |

### Risks

- ⚠️ **Spec instability.** Most concrete syntaxes and all of SPARQL 1.2
  Query are still **WD** — grammar can move. Mitigation: build behind a
  version flag; pin fixtures to the recorded submodule commit; only
  Concepts/Semantics/Protocol/Service-Description (CR) are safe to treat
  as settled.
- ⚠️ **Term-type blast radius in proofs.** A recursive `rdf_term` re-opens
  every totality/termination/equality proof over terms across ~59 files.
  P0 is the schedule risk; sequence it as one focused arc, not
  interleaved.
- ⚠️ **COTTAS format migration.** A term-dictionary change is a durable
  on-disk compatibility surface; get the term model final before P8.
- ⚠️ **KaRaMeL C extraction** of a recursive term needs a heap rep — a
  C-build risk, not a blocker for OCaml/JS/wasm.
- ⚠️ **Masked-pass illusion.** The lenient RDF line-parsers make
  positive-syntax numbers look healthy while dropping data. Gate 1.2
  positive-syntax on **eval**, not parse-success, or the census will lie
  (anti-pattern #3, #25).

## Wave 2 landing — processing-mode architecture + Turtle/TriG/N-Quads 1.2 grammars (2026-07-17)

Owner directive, 2026-07-17 (quoted verbatim, per the CLAUDE.md
"Reading owner steers" rule): full 1.2 build-out with a **"1.1
compatibility mode"** usable **"in whole or part, thoughtfully"**.

### Processing-mode mechanism

A two-constructor F\* type `rdf_syntax_mode = Mode_11 | Mode_12`
(defined in `Parser.NTriples.fst`, the lowest-level line-parser module
every syntax parser already opens) is threaded as a **parameter** — not
a global — through the concrete-syntax parsers and serializers:

- **N-Triples / N-Quads:** distinct `_12` entry points +
  `parse_ntriples_mode` / `parse_nquads_mode` /
  `parse_nquads_strict_mode` dispatchers.
- **Turtle / TriG:** the mode is a field `ts_mode` on the already-
  threaded `turtle_state`, so every production sees it; `Mode_11`
  behaviour is byte-identical (the field defaults to `Mode_11` in
  `empty_turtle_state`). `empty_turtle_state_12` +
  `parse_turtle_*_12` / `parse_trig_*_12` +
  `parse_turtle_with_base_mode` / `parse_trig_with_base_mode` seed
  Mode_12. TriG inherits triple-term + dirlang support for free
  (it threads a `turtle_state`).
- **Serializers are emit-minimal:** `RDF.NQuads.Serialize`'s
  `nq_term_to_string` already renders `<<( )>>` and `--ltr`/`--rtl`
  only for terms that carry a triple term / base direction, so a
  purely-1.1 term is byte-identical in both modes.
  `nq_term_to_string_mode` adds the honest-failure half: under Mode_11
  a term that requires 1.2 syntax returns `None` (a typed error) rather
  than being silently emitted.

**Default everywhere is Mode_11.** Rationale (the "thoughtfully" part
of the directive): the 1.2 concrete-syntax specs are still W3C Working
Drafts (N-Triples 2026-05-15, N-Quads/Turtle/TriG 2026-05-28), so 1.1
stays normative and no WD grammar churn can move a 1.1 score. Consumers
opt in: `w3c_runner --rdf12`, the `factoidal` CLI `--rdf12` flag.

### Scope of this wave

Landed: object-position triple terms `<<( s p o )>>` (incl. nesting) +
directional language strings `"x"@lang--dir` (with tag/direction
validation) across N-Triples/N-Quads/Turtle/TriG, their serializer
counterparts, and rejection of the retired RDF-star `<< s p o >>`
quoted-triple form in **both** modes.

**Deferred to a later wave (honest disposition):** the RDF 1.2 Turtle/
TriG **reifying triple** `<< s p o >>`, the `~` reifier, the `{| |}`
annotation block, and the `VERSION` directive. These need reifier-
blank-node generation + `rdf:reifies` materialisation (a semantic
feature), which is why every remaining Turtle/TriG positive-syntax and
eval failure is a "should parse but didn't" on exactly those
productions — **zero** false-accepts (all negative-syntax tests pass).

### Measured (gate on eval, not masked parse-success)

| Suite | before (baseline census, lenient-masked) | after (wave 2, strict) |
|---|---|---|
| rdf12 n-triples/syntax | 29 pass, 0 fail (of 29) | **29 pass, 0 fail** |
| rdf12 n-quads/syntax | 25 pass, 2 fail (of 27) | **27 pass, 0 fail** |
| rdf12 turtle/syntax | 65 pass, 2 fail (of 67) *(masked)* | **36 pass, 31 fail** (31 = reifier/annotation/`VERSION` positives) |
| rdf12 turtle/eval | 4 pass, 25 fail (of 29) | **4 pass, 25 fail** (25 need reification) |
| rdf12 trig/syntax | 33 pass, 2 fail (of 35) *(masked)* | **14 pass, 21 fail** (21 = reifier/annotation positives) |
| rdf12 trig/eval | 0 pass, 25 fail (of 25) | **0 pass, 25 fail** (all need reification) |

The turtle/trig-syntax numbers *drop* against the census because the
census counted lenient parse-success (dropping content silently); the
wave-2 runner parses strictly and compares eval output to the expected
N-Triples/N-Quads parsed with the 1.2 parser. This is the anti-pattern
#3/#25 correction the strategy insisted on: eval is the true gate.

1.1 floors held byte-identical: RDF six suites 1031 pass, 0 fail;
SPARQL 1.1 631 pass, 0 fail; tinc 124/3-of-127; tcon 352/0; csvw
267/3; jsonld-tordf 466/0; tests/unit 46/46.

## Cross-references

- Epic: [#305](https://github.com/danbri/factoidal/issues/305).
- Provenance:
  [`third_party/testing/w3c-rdf12-PROVENANCE.md`](../../third_party/testing/w3c-rdf12-PROVENANCE.md).
- Supersedes the hold-the-line policy in
  [`rdf12-compatibility.md`](rdf12-compatibility.md).
- Ledger "parked" lines to update on acceptance:
  [`docs/claude-rules/w3c-completeness-ledger.md`](../claude-rules/w3c-completeness-ledger.md).
