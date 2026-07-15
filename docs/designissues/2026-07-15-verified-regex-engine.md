# Verified regex engine — Brzozowski derivatives over codepoint ranges

Issue [#304](https://github.com/danbri/factoidal/issues/304). This document
covers Phase 1: the research/design decision and the verified core engine
(`Regex.Syntax`, `Regex.Derivative`, `Regex.Exec`). Parser flavor (Phase 2)
and consumer integration (Phase 3) are scoped here but not built yet.

The owner directive (2026-07-15): "Research and build us a pure F\* (or Low\*)
standard regex engine that integrates properly with the F\* abstractions we
have used in rdf, csvw, xslt/xml/xpath. It should be complete, fast and
efficient." One engine unblocks the last-mile of three specs plus one
assume-val elevation — see the integration audit (§2).

---

## Part A — Research and integration audit

### 1. Survey

**Brzozowski derivatives (1964).** Janusz Brzozowski, *Derivatives of Regular
Expressions*, Journal of the ACM 11(4):481–494, 1964. The derivative
`D_c(r)` of a regular expression `r` with respect to a character `c` denotes
the language `{ w | c·w ∈ L(r) }`. Membership reduces to `nullable(D_w(r))`:
fold the derivative over the input word, then test whether the residual
accepts the empty string. Derivatives are total and purely functional, and
`D_c` distributes over every operator — including the boolean operators
**intersection** and **complement**, which a Thompson/NFA construction cannot
express. Brzozowski's other contribution is that, *modulo* the similarity
laws (associativity, commutativity, idempotence of union — "ACI"), a regular
expression has only finitely many dissimilar derivatives, which is what makes
the derivative-to-DFA construction terminate.

**Owens, Reppy & Turon — the practical blueprint.** Scott Owens, John Reppy,
Aaron Turon, *Regular-expression derivatives re-examined*, Journal of
Functional Programming 19(2):173–190, 2009
([DOI 10.1017/S0956796808007090](https://doi.org/10.1017/S0956796808007090)).
This is the design we follow. Two contributions matter here:

- **Charset (codepoint-range) alphabet.** Rather than one derivative per
  character, character classes are represented as sets of intervals, and the
  alphabet is partitioned into *derivative classes* — maximal sets of
  characters with the same derivative — computed from the interval endpoints
  in the expression. A transition is computed once per class, not once per
  Unicode codepoint. This is exactly what makes a codepoint-correct engine
  (alphabet size 1.1 million) tractable.
- **Smart constructors realizing the ACI similarity relation.** Union and
  intersection are kept in a canonical sorted/deduplicated flattened form;
  concatenation and star apply the absorption/unit laws (`∅·r = ∅`,
  `ε·r = r`, `∅* = ε`, …). With these, the set of reachable derivatives is
  finite and small in practice, so the DFA is finite and matching is linear
  in the input.

The paper explicitly extends the operator set with `&` (intersection) and
`~` (complement) and notes the derivative rules are trivial for them —
`D_c(r & s) = D_c(r) & D_c(s)`, `D_c(~r) = ~D_c(r)`. That is the operation the
OWL facet-emptiness check (§2, [#299](https://github.com/danbri/factoidal/issues/299))
needs, and the reason the extended AST is committed from day one.

**Antimirov partial derivatives (1996) — the alternative we did not take.**
Valentin Antimirov, *Partial derivatives of regular expressions and finite
automaton constructions*, Theoretical Computer Science 155(2):291–319, 1996.
Partial derivatives return a *set* of expressions whose union is the
Brzozowski derivative; the construction yields an NFA (the "partial
derivative automaton") that is often smaller than the DFA, and it sidesteps
the need for ACI normalization to get finiteness. We chose plain Brzozowski
derivatives + smart constructors instead because:

1. **Complement.** Antimirov partial derivatives are defined for the positive
   fragment; complement (`~r`) has no clean partial-derivative treatment
   because complementing a nondeterministic set of residuals is not a union
   of partial derivatives. The OWL facet case needs complement, so the NFA
   advantage evaporates.
2. **Determinism for free.** The Brzozowski derivative is a *function*
   (one residual), which is what the correctness proof (`deriv_correct`)
   and the deterministic DFA both want. Smart constructors recover finiteness
   without the set machinery.

**Mechanized-verification precedent.** Derivative-based matchers have been
verified before, which de-risks the proof obligations:

- *Coq/Ssreflect.* A complete formalization of Brzozowski derivatives with a
  decidable equivalence procedure (Coquand & Siles; also the Braibant &
  Pous relation-algebra line). Coqlex (Sofiane Ndjeka et al.,
  [arXiv:2306.12411](https://arxiv.org/pdf/2306.12411)) generates verified
  lexers from a Coq derivative implementation proven to form a Kleene
  algebra.
- *Agda.* Firsov & Uustalu formalized Brzozowski (and Antimirov) derivative
  parsing with soundness and completeness against an inductive RE semantics,
  producing a certified match/no-match decision.
- *Isabelle/HOL.* Ausaf, Dyckhoff & Urban, *POSIX Lexing with Derivatives of
  Regular Expressions* (proof pearl) — a full derivative correctness
  development.

Our `deriv_correct` / `matches_correct` (§3) prove the same soundness and
completeness statement these developments do, against a boolean denotational
semantics, for the FULL AST including `&`/`~`, with no admit.

### 2. Integration audit (current regex touchpoints)

Every place the tree touches regular expressions today, with file:line, and
what Phase 3 would rewire.

**The single host-engine seam (`regex_match` / `regex_replace`).**

- [`formal/fstar/SPARQL11.Algebra.fst:1149`](../../formal/fstar/SPARQL11.Algebra.fst)
  — `assume val regex_match : string -> string -> option string -> bool`.
- [`formal/fstar/SPARQL11.Algebra.fst:1139`](../../formal/fstar/SPARQL11.Algebra.fst)
  — `assume val regex_replace : string -> string -> string -> option string -> string`.
- [`formal/fstar/SPARQL11.Algebra.fst:1808`](../../formal/fstar/SPARQL11.Algebra.fst)
  — `fn_regex_spec s pattern flags = regex_match s (unescape_sparql_string pattern) flags`
  (SPARQL `REGEX()`, XPath/XQuery `fn:matches` semantics).
- Realisation:
  [`formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/63_regex_hash_uuid_stubs.sh`](../../formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/63_regex_hash_uuid_stubs.sh)
  patches `SPARQL11_Algebra.ml` with an OCaml `Str`-based `regex_match` plus a
  hand-written `xpath_to_str_regex` translator (XPath/ECMAScript → OCaml `Str`
  syntax). This is the `assume val regex_match` line of issue
  [#63](https://github.com/danbri/factoidal/issues/63), and it is
  anti-pattern #10 in the flesh: `Str` matches **bytes, not codepoints**, so
  character classes split multi-byte UTF-8, and the translator carries a long
  tail of escape-convention fixes (`#276`, `#277` are quantifier/`{n,m}` and
  control-escape bugs pinned in
  [`tests/unit/regex_match_unit.ml`](../../tests/unit/regex_match_unit.ml)).

**Consumers that call `regex_match` today** (all would move to the engine's
`matches` in Phase 3, gaining codepoint correctness):

- [`formal/fstar/SHACL.Validation.fst:1848`](../../formal/fstar/SHACL.Validation.fst)
  — `sh:pattern` constraint: `Alg.regex_match lex re (flags)`.
- [`formal/fstar/ShEx.Validation.fst:399`](../../formal/fstar/ShEx.Validation.fst)
  — ShEx node-constraint `pattern`: `Alg.regex_match lex re flags_opt`.
- [`formal/fstar/RIF.Core.Builtins.fst:1056`](../../formal/fstar/RIF.Core.Builtins.fst)
  and `:1060` — RIF `pred:matches` builtin: `Alg.regex_match sv pv ...`.

**XSD pattern facet — not yet implemented, engine unblocks it.**

- [`formal/fstar/XSD.Facets.fst:13`](../../formal/fstar/XSD.Facets.fst)
  scope note: "no pattern/length facets, **no general regex intersection** —
  none of those are needed by the target tests". The facet-satisfiability
  machinery (`facets_to_interval`, `interval_intersect`) handles numeric/date
  intervals only. `xsd:pattern` is absent.
- [`formal/fstar/XSD.Datatypes.fst`](../../formal/fstar/XSD.Datatypes.fst)
  `literal_ill_formed` validates lexical spaces but does no pattern-facet
  matching.

**CSVW duration `format` regex — the permanently-blocked test194.**

- [`formal/fstar/CSVW.Formats.fst:605`](../../formal/fstar/CSVW.Formats.fst)
  — "A duration `format` facet is a REGULAR EXPRESSION per tabular-metadata —
  no regex engine here, so a format-carrying duration is left untouched
  (`FO_NoFormat`; test194 stays enumerated)." This is
  [#297](https://github.com/danbri/factoidal/issues/297)'s one permanently
  blocked test; the engine moves the CSVW ceiling 269 → 270.

**XSLT/XPath `fn:matches` residue.**

- [`formal/fstar/XPath.Eval.fst`](../../formal/fstar/XPath.Eval.fst)'s
  `matches_node_test` / `name_test_matches_elem` (`:623`, `:585`) are XPath
  **node/name tests**, not regex. XPath/XSLT `fn:matches`/`fn:replace`
  currently have no F\*-native regex; the residue is
  [#302](https://github.com/danbri/factoidal/issues/302).

**The OWL `Inconsistent String Pattern` fixture (#299).**

[`third_party/testing/owl/all.rdf:3026`](../../third_party/testing/owl/all.rdf),
test case `Inconsistent-pattern-disjointness` ("Inconsistent String Pattern
with Disjoint Dataproperties", Birte Glimm). The premise ontology:

```
DisjointDataProperties(:dp1 :dp2)
DataPropertyAssertion(:dp1 :a "ab"^^xsd:string)
DataPropertyAssertion(:dp1 :a "ac"^^xsd:string)
SubClassOf(:A DataSomeValuesFrom(:dp2
             DatatypeRestriction(xsd:string xsd:pattern "a(b|c)")))
ClassAssertion(:A :a)
```

The reasoner must see that the pattern-restricted datatype
`xsd:string ∩ pattern("a(b|c)")` has language exactly `{ab, ac}`, that both
`ab` and `ac` are already `dp1` fillers for `a`, and that the `dp2`
filler `:A` forces on `a` must therefore collide with a `dp1` filler —
contradicting `DisjointDataProperties`. The regex operations needed:

- **The pattern:** `a(b|c)` — in the engine, `R_Cat (lit 'a') (R_Alt (lit 'b') (lit 'c'))`.
- **The enumeration (dp1 fillers):** `{ab, ac}` — `R_Alt (lit "ab") (lit "ac")`.
- **Intersection-emptiness needed:** the pattern language is *subsumed by* the
  enumeration, i.e. `L(pattern) \ L(enum) = ∅`, which is
  `is_empty (R_And pattern (R_Not enum))` — `Regex.Exec.subsumes enum pattern`.
  It returns `true` (the pattern admits nothing outside `{ab, ac}`), so every
  `dp2` filler is a `dp1` filler and the disjointness is violated. The dual
  check `L(pattern) ∩ L(enum) ≠ ∅` (`intersection_empty` = `false`) witnesses
  that the collision set is non-empty. Both are exercised in
  [`tests/unit/regex_engine_unit.ml`](../../tests/unit/regex_engine_unit.ml)
  (`subsumes: {ab,ac} covers a(b|c)`, `intersection_empty: a(b|c) & 'ab' is
  NON-empty`).

**Codepoint conventions (`Parser.FastString`).** The engine's alphabet must
match the repo's UTF-8 decoding.
[`formal/fstar/Parser.FastString.fst:101`](../../formal/fstar/Parser.FastString.fst)
defines `fs_cp_at : s:string -> pos:nat -> nat & nat`, which decodes the
UTF-8 codepoint beginning at byte `pos` and returns `(codepoint, byte_length)`;
invalid UTF-8 maps to `(0xFFFD, 1)`. Codepoints are plain `nat`. The engine
therefore models a word as `list nat` of codepoints in `0 .. 0x10FFFF`, and a
Phase-3 consumer bridges a `string` to a `list nat` by iterating `fs_cp_at`
(codepoint semantics), retiring the byte-level `Str` bugs. `fs_byte_at`
(`:53`) is the byte-oriented primitive — deliberately NOT what the engine
consumes.

### 3. Architecture

**Module layout** (three flat modules, wired into all three `build-ocaml.sh`
lists + `tests/unit/run-all.sh`):

| Module | Tier | Contents |
|---|---|---|
| `Regex.Syntax` | semantic core | AST; `size` measure; codepoint ranges; `mem` denotational semantics; `nullable` + `nullable_correct`; smart constructors + `*_ok` lemmas |
| `Regex.Derivative` | semantic core | `deriv`; `deriv_correct`; `matches`; `matches_correct` |
| `Regex.Exec` | pragmatics | normalized `nderiv` + ACI flatten; `matches_norm`; unanchored `search`/`find_match`; codepoint-class partition; fuel-bounded `is_empty` / `intersection_empty` / `subsumes` |

**The AST** (`Regex.Syntax.regex`) is over codepoint *ranges*, extended with
the boolean operators from day one:

```
R_Empty | R_Eps | R_Ranges (list (nat & nat))
| R_Cat r r | R_Alt r r | R_Star r
| R_And r r | R_Not r
```

Negated character classes are `R_Ranges` of the complement interval set over
`[0, 0x10FFFF]` (`complement_ranges`); whole-language complement/intersection
are `R_Not` / `R_And`.

**API signatures** (extracted names in parentheses):

```
Regex.Derivative.matches : regex -> list nat -> Tot bool      (proven-correct reference)
Regex.Exec.matches_norm  : regex -> list nat -> Tot bool      (ACI-normalized fast path)
Regex.Exec.search        : regex -> list nat -> Tot bool      (unanchored, .* r .*)
Regex.Exec.find_match    : regex -> list nat -> option nat    (leftmost start index)
Regex.Exec.is_empty      : regex -> Tot bool                  (fuel-bounded emptiness)
Regex.Exec.intersection_empty : regex -> regex -> Tot bool    (L(p) ∩ L(q) = ∅)
Regex.Exec.subsumes      : regex -> regex -> Tot bool         (L(q) ⊆ L(p))
```

**The correctness statement.** The denotational semantics is a TOTAL boolean
membership `mem : regex -> list nat -> Tot bool` (not an inductive `Prop`).
The standard inductive language relation has `R_Not` in a negative position,
so it is not a well-formed inductive with complement in the AST — the
"And/Not make the semantics non-inductive" trap. A boolean recursive function
sidesteps it entirely: `R_And`/`R_Not` are ordinary boolean combinators over
strictly-smaller sub-regexes, so they cost nothing. The only real termination
work is concatenation and star, whose membership quantifies over word splits;
`mem` enumerates splits with `take_n`/`drop_n` and a four-component
lexicographic measure `%[|w|; size; split-index; tag]`. Given that,
**all three lemmas are proven for the full AST, no admit, no `--lax`, no
`assume val`, no fragment carve-out**:

```
nullable_correct : nullable r        <==> mem r []              -- Regex.Syntax
deriv_correct    : mem (deriv c r) w <==> mem r (c :: w)        -- Regex.Derivative
matches_correct  : matches r w       <==> mem r w               -- Regex.Derivative
```

`deriv_correct` is proven by relating the boolean split-enumeration functions
`cat_try`/`star_try` on the word `(c :: w)` *directly* to a derivative on `w`,
by induction on the split index (`cat_shift`, `star_shift`) — not by
manipulating existential quantifiers, which SMT discharges poorly. `R_And`,
`R_Not`, `R_Alt` fall out of the inductive hypothesis plus the smart-
constructor language lemmas (`smart_alt_ok`, `smart_and_ok`, `smart_not_ok`).

**DFA-construction plan.** `Regex.Exec.nderiv` applies full ACI normalization:
`R_Alt`/`R_And` are flattened into sorted, deduplicated leaf lists
(`alt_flatten`/`and_flatten` + `rebuild_alt`/`rebuild_and`), `R_Cat`/`R_Star`
apply the absorption/unit laws (`smart_cat`/`smart_star`). This makes the set
of reachable derivatives finite (Owens-Reppy-Turon similarity). The
codepoint-class alphabet is `class_reps r`: the range endpoints in `r` plus
`0` and `max_codepoint`, one representative per derivative class. `is_empty`
does a fuel-bounded breadth-first exploration of the derivative closure over
`class_reps`, returning `true` only when the worklist drains with no nullable
state. A memoized lazy DFA (state cache keyed on the normalized AST,
transition table per class) is the natural next step; `matches_norm` already
recomputes the same deterministic transition, so adding a cache is
transparent.

**Verified vs. Phase-2 proof obligations.** `matches_norm`/`is_empty` live in
the pragmatics tier because they rest on the smart-constructor language
lemmas for the *normalized* derivative — `smart_cat_ok`, `smart_star_ok`, and
an ACI-flatten language lemma — which are NOT yet proven. So today:

- `Regex.Derivative.matches` is machine-checked correct (`matches_correct`),
  but the plain derivative is exponential on adversarial nullable-heavy
  patterns (no normalization).
- `Regex.Exec.matches_norm`/`is_empty` are linear / state-finite in practice
  but their language-equality to the proven path is
  **sound-by-construction, not machine-checked**. The unit test cross-checks
  the two on small inputs (`proven==norm`), and `is_empty`'s precise
  guarantee (conservative under fuel; `true` only after the closure drains)
  is documented at its definition. Closing `smart_cat_ok`/`smart_star_ok` +
  a class-coverage lemma to make `matches_norm`/`is_empty` fully verified is
  Phase-2 work.

This matches iron rule #11's standing qualifier: parser and algebra spec
verified in F\*; the performance layer carries stated, tracked proof debt.

**Phase 2 — XSD-flavor parser.** Parse XML Schema Part 2 Appendix F regex
syntax (+ XPath `fn:matches` `i`/`s`/`m`/`x` flags and anchors) to the
`Regex.Syntax` AST, in F\* (iron rule #4). No backreferences ever (out of the
regular fragment; no target spec needs them). Measure before building Unicode
general-category tables — build only the `\d`/`\w`/`\s`/`\p{...}` escapes the
fixtures actually use.
*Acceptance:* the escapes exercised by the ShEx/SHACL/RIF pattern fixtures
and the CSVW duration `format` of test194 parse and match.

**Phase 3 — consumer integration**, each behind an existing seam with a
suite-flip gate:

| Consumer | Seam | Gate |
|---|---|---|
| SPARQL `REGEX`/`REPLACE` | replace `assume val regex_match`/`regex_replace` realisation (#63) | sparql11-query stays 338 pass, 0 fail; the codepoint cases in `regex_match_unit.ml` now pass by codepoint, not byte |
| SHACL `sh:pattern` | `SHACL.Validation:1848` | SHACL suite unchanged |
| ShEx `pattern` | `ShEx.Validation:399` | shex suite unchanged |
| RIF `pred:matches` | `RIF.Core.Builtins:1056` | RIF conformance unchanged |
| XSD `xsd:pattern` facet | new, `XSD.Facets` / `XSD.Datatypes` | facet-carrying literals validate |
| CSVW duration `format` | `CSVW.Formats:605` | test194 flips; CSVW 269 → 270 |
| OWL facet emptiness | new, uses `Regex.Exec.subsumes`/`intersection_empty` | `Inconsistent-pattern-disjointness` reported inconsistent |
| XPath/XSLT `fn:matches` | `XPath.Eval` (#302) | XPath matches/replace residue |

---

## Part B — the core engine (built, this commit)

Three modules, all verifying under z3 4.13.3 with no `--lax`, no
`--admit_smt_queries`, no admit, no `assume val`. Unit tests in
[`tests/unit/regex_engine_unit.ml`](../../tests/unit/regex_engine_unit.ml)
(48 pass, 0 fail): literals, classes, star, alternation, `And`/`Not`,
intersection-emptiness (the OWL `a(b|c)` shape), the classic `(a?)^n a^n`
pathological case (no blow-up), non-ASCII/astral codepoint ranges, unanchored
search, and proven-vs-normalized cross-checks.

**Perf smoke** (1 MB ASCII input, native; order-of-magnitude only, not a
gate): `matches_norm` a\* ≈ 36 ms, [a-z]+ ≈ 18 ms; OCaml `Str` a\* ≈ 17 ms,
[a-z]+ ≈ 16 ms. The derivative engine is within ~1–2× of `Str` on simple
patterns even with `nat`→zarith codepoints, and it has no catastrophic-
backtracking exposure (`Str` does). A byte/int32 codepoint representation is a
Phase-3 optimization once a consumer needs the throughput.
