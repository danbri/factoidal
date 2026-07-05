# 2026-07-05 — XSD.Datatypes reusable foundation module (slice 1)

Tracks: current-state.md "Standing priorities" item 4 / #235, owner
directive 2026-07-04 ("the split's FIRST-CLASS deliverables are
reusable foundation modules ... `XSD.Datatypes` (value spaces,
canonical forms, numeric promotion; today embedded in
SPARQL11.Algebra)").

## What moved

`formal/fstar/XSD.Datatypes.fst` (new module) now owns, moved
verbatim from `SHACL.Validation.fst`:

- Numeric comparison for `sh:minInclusive`/`maxInclusive`/`minExclusive`/
  `maxExclusive`: `literal_to_scaled`, `scaled_cmp`.
- xsd:dateTime ordering: `days_from_civil`, `dt_parse_tail`,
  `dt_parse_ms`, `dt_cmp`, `both_datetimes`, `numeric_cmp_le`,
  `numeric_cmp_lt`.
- XSD ill-formed-literal detection (SHACL `sh:datatype`): `is_ascii_digit`,
  `is_integer_lexical`, `is_decimal_lexical`, `int_lexical_in_range`,
  `literal_ill_formed`.

`SHACL.Validation.fst` now imports these as `module XSD =
XSD.Datatypes` and keeps thin re-export `let`s
(`literal_to_scaled`/`scaled_cmp`/`numeric_cmp_le`/`numeric_cmp_lt`/
`literal_ill_formed`) so every existing call site (the aggregate
constraint helpers in section "11h", `term_lt`) is unchanged. `term_lt`/
`term_le` themselves stayed in `SHACL.Validation.fst` — they also need
`rdf_term_eq`/`string_lt` from `RDF.Graph.Executable`, which
`SHACL.Validation` already opens directly; there was no reason to
relocate them.

`XSD.Datatypes.fst` also re-exports (not reimplements) the canonical
numeric-lexical parsers from `SPARQL11.Algebra`: `parse_int_string`,
`parse_to_scaled`, `parse_double_to_scaled`, `pow10`, plus the
`xsd_dateTime` IRI constant (defined in Algebra, not
`RDF.Graph.Executable`). **`SPARQL11.Algebra.fst` itself is
untouched** — XSD.Datatypes only adds a read-only import edge onto it.

## What did NOT move (documented follow-ups)

1. **`SPARQL11.Algebra.fst`'s own copies** of `parse_int_string` /
   `parse_to_scaled` / `parse_double_to_scaled` / `pow10` / the
   `ER_Num`/`ER_Dec`/`ER_Dbl` numeric-promotion machinery are
   untouched. Algebra is ~5,800 lines with ~40+ internal call sites
   for these parsers threaded through FILTER/BIND evaluation,
   aggregate arithmetic, and casting (`xsd_cast`); migrating every
   call site to `XSD.Datatypes` in one slice was judged higher risk
   than the consolidation was worth, per the brief's explicit
   "do not attempt if risky" guardrail. Concretely: Algebra carries
   no `--admit_smt_queries` of its own, but its sheer call-site count
   means a botched migration would silently change FILTER/BIND
   numeric semantics across all 631 SPARQL query/update W3C tests,
   not just the 22 SHACL sh:sparql ones. Follow-up slice: once a
   subagent has grepped every call site and can show each one keeps
   identical behavior post-migration, invert the dependency —
   `XSD.Datatypes` becomes the canonical definition site, `Algebra`
   re-exports from it (mirroring the direction this slice used for
   the SHACL migration, just flipped).
2. **`RDF.Graph.Executable.fst`'s `datatype_value_eq`**
   (xsd:integer/xsd:decimal value-space equality, ~line 4663,
   including its `normalize_integer_lexical`/`normalize_decimal_lexical`
   helpers) is untouched. `RDF.Graph.Executable` is the class-F
   foundational module (fires every suite: OWL closure,
   `is_inconsistent`, every parser/serialiser) — recently touched for
   the `is_inconsistent` relocation. Migrating its one caller into
   `XSD.Datatypes` in the same slice as the SHACL migration would have
   put OWL PE/NE/Consistency/Inconsistency floors and the full RDF
   1031-test suite on the same gate as the SHACL 98+22, for a module
   that isn't this slice's chosen consumer. Follow-up slice: move
   `datatype_value_eq` + its two normalize helpers into
   `XSD.Datatypes.fst` (they only need `literal`/`wf_iri` from
   `RDF.Graph.Executable`, which is already `XSD.Datatypes`'s lowest
   dependency, so no cycle), then have `RDF.Graph.Executable` call
   into `XSD.Datatypes` — this is the one direction that would need
   `RDF.Graph.Executable` to gain a *new* import, so budget a careful
   re-verify of the whole foundational tier when attempting it.

## Migration order for the rest

1. `RDF.Graph.Executable.datatype_value_eq` (cleanest remaining pick —
   self-contained, only needs types already available to
   `XSD.Datatypes`, but gate on the full OWL+RDF suite matrix, not
   just SHACL).
2. `SPARQL11.Algebra`'s `xsd_cast` and the `ER_Num`/`ER_Dec`/`ER_Dbl`
   promotion helpers around it (`promote_numeric_pair`,
   `numeric_result`, etc. — grep `ER_Num` in `SPARQL11.Algebra.fst`
   for the full call-site list before starting; anti-pattern #6:
   promoted-type blindness bites here first). Gate on all 631 SPARQL
   tests, not a subset.
3. Once (1)+(2) land, invert the parser re-export direction so
   `XSD.Datatypes` is the sole canonical definition site and
   `SPARQL11.Algebra` imports from it instead of the other way
   around.

## How RDF.LanguageTag / RDF.Unicode relate

Per current-state.md item 4, `XSD.Datatypes` is one of four sibling
reusable-foundation modules the owner named together:

- `RDF.IRI` (RFC 3986/3987 — today scattered across
  `SPARQL11.IRI.Resolve` + `Parser.IRI` + per-parser fragments).
- `XSD.Datatypes` (this module).
- `RDF.Unicode` (UTF-8/codepoints/escapes — today `assume val`s +
  per-parser char logic; the new `Parser.JSON` escape handling should
  consume it once it exists).
- `RDF.LanguageTag` (BCP47 well-formedness + case-insensitive
  comparison — fixes the known `literal_eq` gap where `@en-US` and
  `@en-us` compare unequal).

These four are independent extraction targets, not a dependency
chain: `XSD.Datatypes` needs none of the other three (it only opens
`RDF.Graph.Executable` and re-exports from `SPARQL11.Algebra`), and
none of the other three need `XSD.Datatypes`. The one place they will
eventually touch is `datatype_value_eq` (follow-up 1 above), which
already calls `lang_tag_option_eq` from `RDF.Graph.Executable` — once
`RDF.LanguageTag` exists as its own module, `lang_tag_option_eq`
should move there and `XSD.Datatypes`'s migrated `datatype_value_eq`
would import it, giving XSD value-equality and language-tag equality
their own single-purpose homes instead of the current
`RDF.Graph.Executable` scatter. Per current-state.md, JSON-LD phases
3-4 need `RDF.IRI` + `RDF.Unicode` specifically, so those two should
extract before `RDF.LanguageTag`; `XSD.Datatypes` (this slice) has no
ordering dependency on any of them and could equally have gone first
or last.

## Verification

- `XSD.Datatypes.fst` and `SHACL.Validation.fst` verify clean under
  z3 4.13.3, no `--lax`, no `--admit_smt_queries` (both modules were
  already free of it; unchanged here).
- `shacl_runner` (default core manifest): 98 pass, 0 fail (of 98) —
  unchanged from baseline.
- `shacl_runner` sparql manifest: 17 pass, 5 fail (of 22) — unchanged
  from baseline (the 5 fails are the pre-existing custom
  constraint-component gap, not touched by this slice).
- W3C SPARQL: 631 pass, 0 fail (of 631). W3C RDF: 1031 pass, 0 fail
  (of 1031). OWL 2 RL: PositiveEntailment 27 pass, 2 fail (of 29);
  NegativeEntailment 4 pass, 2 fail (of 6); Consistency 75 pass, 1
  fail (of 76); Inconsistency 11 pass, 0 fail, 3 skipped (of 14) — all
  unchanged from baseline, as expected since neither
  `RDF.Graph.Executable.fst` nor `SPARQL11.Algebra.fst` were edited.
