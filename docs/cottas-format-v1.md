# COTTAS-on-Parquet v1 (factoidal)

**Status:** Draft v1, 2026-04-25.
**Scope:** the on-disk container layout that factoidal currently **reads**
when given a `.cottas` file, written by version 1.1.0 of the upstream
`pycottas` tool. v1 fixes that contract so future upstream changes do not
silently break our F\*-extracted readers.

> **Note on identity.** "COTTAS-on-Parquet v1 (factoidal)" is a
> factoidal-side stability label. It is **not** the same thing as
> pycottas's own internal format-version string (pycottas does not
> currently expose one as a Parquet KV-metadata key — see §10). v1
> therefore describes a *shape* of file, not a producer-stamp.
> A file is "v1-shaped" if it satisfies §2–§7 below.

This document is a contract a third-party producer or reader can
implement against without consulting pycottas internals. Where a claim
is grounded in F\* code, the line numbers in
[`formal/fstar/Parquet.Footer.fst`](../formal/fstar/Parquet.Footer.fst)
are cited so future readers can audit it directly.

Companion design notes:

- [`docs/designissues/cottas-native-backend.md`](designissues/cottas-native-backend.md)
- [`docs/designissues/sparql-store-backend.md`](designissues/sparql-store-backend.md)
- [`docs/designissues/2026-04-19-cottas-parquet-wiring-plan.md`](designissues/2026-04-19-cottas-parquet-wiring-plan.md)

## 1. Format identity

A v1 file is an Apache Parquet file whose schema, column ordering,
encodings, compression, and term-token convention all match §2–§7 of this
document. **factoidal v1 readers MUST refuse a file that is not
v1-shaped.** v1 is the only format factoidal reads today.

This spec applies equally to files factoidal might *write* in the
future. At present (2026-04-25) factoidal does not have an F\*-extracted
COTTAS writer; production of v1 files is delegated to `pycottas` via
[`tools/corpus_pipeline.py`](../tools/corpus_pipeline.py) (see
`materialize_nq_cottas_corpus` at line 1015 — it shells out to
`pycottas.rdf2cottas(input_nq, output_cottas, index="spog", disk=...)`).
Building an F\*-only writer is tracked separately and is **out of scope
for v1**; if added, it MUST emit files satisfying this spec.

## 2. Container

- **File format:** Apache Parquet.
- **Parquet logical version:** observed `2.6` (pycottas 1.1.0 routes
  through DuckDB ≥ 1.5; DuckDB writes Parquet 2.6 by default). v1
  readers MUST accept any Parquet version that produces equivalent
  encoded column chunks (i.e. compatibility is by encoding, not by
  format-version string).
- **Compression:** every column chunk is compressed with **ZSTD**
  (Parquet codec id `6`; see `parquet_compression_codec_name` at
  [`Parquet.Footer.fst:765-774`](../formal/fstar/Parquet.Footer.fst)).
  No other codec is permitted in v1.
- **Row-group size:** observed default of **122,880 rows per row group**
  (DuckDB Parquet writer default, inherited via pycottas). v1 does
  **not** mandate this exact number: a v1 reader MUST handle any
  positive row-group size, including the final (typically smaller)
  row group. v1 producers SHOULD use 122,880 unless there is a reason
  not to.
- **Column statistics, dictionary statistics, Bloom filters, page
  indexes:** OPTIONAL. v1 readers MUST tolerate their presence and
  MUST tolerate their absence.

## 3. Column schema

Exactly four required columns, in this order. Column names are the
single ASCII letters shown.

| Idx | Name | Parquet physical type | Logical / converted type | Encoding(s) observed | Notes |
|----:|:-----|:----------------------|:-------------------------|:---------------------|:------|
| 0   | `s`  | `BYTE_ARRAY`          | `STRING` (UTF-8)         | `DELTA_LENGTH_BYTE_ARRAY` | subject token (§4) |
| 1   | `p`  | `BYTE_ARRAY`          | `STRING` (UTF-8)         | `DELTA_LENGTH_BYTE_ARRAY` | predicate token (§4) |
| 2   | `o`  | `BYTE_ARRAY`          | `STRING` (UTF-8)         | `DELTA_LENGTH_BYTE_ARRAY` | object token (§4) |
| 3   | `g`  | `BYTE_ARRAY`          | `STRING` (UTF-8)         | `DELTA_LENGTH_BYTE_ARRAY` | graph token (§4, §6) |

Schema requirements for a v1-shaped file:

- The four columns MUST be physical `BYTE_ARRAY` and MUST be marked as
  the Parquet `STRING` logical/converted type.
- Names MUST be exactly `s`, `p`, `o`, `g` (lowercase, single letter,
  in that order). Position order is normative; names are how the F\*
  reader displays them via
  [`probe_parquet_column_name`](../formal/fstar/Parquet.Footer.fst).
- Columns MAY be marked `optional` at the Parquet schema level, but in
  practice every cell is present in v1 — there are no nulls (an absent
  graph is the literal token `DEFAULT`, see §6).
- v1 readers MUST treat unknown / extra columns as a parse error: a
  conformant v1 file has exactly four columns. (This is a deliberate
  tightening relative to "tolerate extra columns"; see §10 — extras
  belong in v2, not silently in v1.)

### Allowed encodings

Parquet permits a column chunk to use multiple encodings across pages.
v1 producers SHOULD use the encodings shown above. v1 readers MUST
support at least:

- `DELTA_LENGTH_BYTE_ARRAY` (Parquet encoding id `6`) on any of the
  four columns. The factoidal reader's miniblock-aware DLBA decoder
  lives at
  [`Parquet.Footer.fst:1456`–`1700`](../formal/fstar/Parquet.Footer.fst)
  (per-miniblock `bit_width`; issue #97).
- `RLE_DICTIONARY` (Parquet encoding id `8`) on any of the four columns,
  paired with a `DICTIONARY_PAGE` of `PLAIN`-encoded entries. The
  factoidal RLE_DICTIONARY decoder lives at
  [`Parquet.Footer.fst:1786`–`2167`](../formal/fstar/Parquet.Footer.fst)
  (issue #98).

The combined per-column dispatcher
[`probe_parquet_column_decode_all`](../formal/fstar/Parquet.Footer.fst:2173)
tries `DELTA_LENGTH_BYTE_ARRAY` first and falls back to
`RLE_DICTIONARY`. **Empirical note:** the reference parliament
fixture at `tmp/ukparliament/.../v1/data.cottas` (3,143,406 rows,
26 row groups, 122,880 row-group default) uses
`DELTA_LENGTH_BYTE_ARRAY` for **all four columns**. Some upstream
DuckDB / pycottas configurations emit `RLE_DICTIONARY` on the
high-cardinality columns (`p`, `g`); both shapes are v1-conformant.

### File-level KV metadata

The following Parquet file-level metadata key is recognised in v1:

| Key       | Value example | Meaning |
|-----------|---------------|---------|
| `index`   | `spog`        | Logical key permutation supplied by the producer to indicate the row sort order. v1 readers MAY use it as a hint; readers MUST NOT rely on it for correctness (a row-group-bound producer may sort within row groups but not globally). |

All other key-value metadata (e.g. DuckDB's `duckdb_schema` group
wrapper) MUST be ignored by v1 readers.

## 4. Term encoding (the value bytes in `s`, `p`, `o`)

The cell value of `s`, `p`, `o` is a UTF-8 string carrying an N-Quads
*token* for one RDF term. The token grammar is a subset of N-Quads
(W3C Recommendation 25 February 2014, §4) restricted to the form
needed to round-trip a single term:

```
iri      ::= '<' IRI-as-bytes '>'
bnode    ::= '_:' [A-Za-z0-9_]+
literal  ::= '"' lex '"'
           | '"' lex '"' '@' lang
           | '"' lex '"' '^^' iri
lex      ::= UCHAR | ECHAR | <any byte except '"' or '\\'>
```

where:

- `lex` is the N-Quads-escaped lexical form, with the standard
  six-character `\\"`, `\\\\`, `\\t`, `\\r`, `\\n`, `\\b`, `\\f`
  escapes plus `\\uXXXX` and `\\UXXXXXXXX` per N-Quads §7.4.
  Unescaping is the responsibility of the consumer; the bytes on
  disk are the pre-escaped form.
- `lang` is a BCP-47 language tag (e.g. `en`, `en-GB`).
- The literal datatype IRI is wrapped in `<...>` and follows the
  `^^` token (no whitespace, exactly the bytes shown).

### Per-column term mapping

| Column | Allowed token shapes |
|:------:|:---------------------|
| `s`    | `iri` or `bnode`     |
| `p`    | `iri` only           |
| `o`    | `iri`, `bnode`, or `literal` |
| `g`    | `iri` (i.e. `<...>`) **or** the literal ASCII string `DEFAULT` (see §6) |

Subject blank nodes carry the bare `_:label`; F\* reads back the
label by stripping the `_:` prefix (see
[`cottas_runtime.sh:147–171`](../formal/fstar/experimental_ocaml_glue/cottas_runtime.sh)).
Object blank nodes follow the same shape.

A literal **without** datatype or language tag is the bare
`"lex"` form. Per RDF 1.1, such a literal has datatype
`xsd:string`; v1 readers MUST treat it as such on read (the
factoidal OCaml glue does this at
[`cottas_runtime.sh:122–128`](../formal/fstar/experimental_ocaml_glue/cottas_runtime.sh)).

A language-tagged literal `"lex"@en` has datatype `rdf:langString`
per RDF 1.1; v1 readers MUST set the datatype slot accordingly
([`cottas_runtime.sh:129–134`](../formal/fstar/experimental_ocaml_glue/cottas_runtime.sh)).

### Most format-fragile claim

The literal-token grammar is the **most format-fragile** part of v1.
N-Quads §7.4 permits `\\u`/`\\U` escapes inside `lex`; the factoidal
OCaml glue currently performs a *naive* unescape (`\\X → X` for any
single byte X — see `unescape_literal` at
[`cottas_runtime.sh:90–103`](../formal/fstar/experimental_ocaml_glue/cottas_runtime.sh))
which round-trips correctly only for the simple `\\\\`, `\\"`
escapes, NOT for `\\n`, `\\t`, `\\uXXXX`, `\\UXXXXXXXX`. If a
pycottas writer emits, say, `\\u00E9` for `é`, today's reader
will read back the **eight-byte ASCII** `é`, not `é`. The
parliament fixture happens not to exercise this (its literal
samples are ASCII or pre-decoded UTF-8), so the gap has not
manifested. v1 nominally requires full N-Quads §7.4 unescaping;
factoidal's reader does not yet meet that bar — see
"known reader gaps" in §10.

## 5. Token examples (parliament fixture)

```
s : <http://albertowenmp.org/>
p : <https://id.parliament.uk/schema/personWebLinkHasPerson>
o : <https://id.parliament.uk/krGtkX0n>
g : DEFAULT
```

```
s : _:115161184861629af182dafdbb0eaf23
p : <https://id.parliament.uk/schema/personHasGender>
o : <https://id.parliament.uk/...>
g : DEFAULT
```

```
o : "2018-04-15+00:00"^^<http://www.w3.org/2001/XMLSchema#date>
o : "Well-known text"
o : "2"^^<http://www.w3.org/2001/XMLSchema#integer>
```

(Source: `tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas`,
3,143,406 rows, inspected 2026-04-25.)

## 6. Default-graph sentinel

A row that belongs to the unnamed (default) graph MUST have the
literal ASCII string `DEFAULT` (seven bytes, no quotes, no `<>`,
no language tag) in column 3 (`g`). It is **not** the empty string,
**not** a NULL, and **not** an IRI.

This is a true sentinel: since `DEFAULT` is not a valid IRI token
(no surrounding `<...>`), a v1 reader can disambiguate
"default-graph row" from "named-graph row whose IRI happens to be
`DEFAULT`" purely by leading character (`<` ⇒ named, otherwise ⇒
default). v1 explicitly forbids any other sentinel string.

The factoidal OCaml glue parses this at
[`cottas_runtime.sh:167–171`](../formal/fstar/experimental_ocaml_glue/cottas_runtime.sh):

```
let parse_graph s =
  if s = "DEFAULT" then Some None
  else match parse_iri_token s with
    | Some iri -> Some (Some iri)
    | None -> None
```

`Some None` here means "row exists, graph is default"; `Some (Some
iri)` means "row exists, graph is the given IRI". Anything else is a
malformed v1 file.

## 7. Multi-row-group semantics

A v1 file MAY have any positive number of row groups (the parliament
fixture has 26). Within each row group, the four columns have the
**same `num_values`** equal to that row group's `num_rows`; a row
is the i-th cell of column 0 + the i-th cell of column 1 + … +
the i-th cell of column 3 within the same row group. **No row group
sees a partial quad.**

The logical row sequence is the concatenation, in row-group-index
order, of each row group's per-column streams. v1 readers MUST
iterate every row group; reading only row group 0 is a v1 conformance
failure.

## 8. Reading model in F\*

The verified read path is rooted at:

- [`probe_parquet_footer`](../formal/fstar/Parquet.Footer.fst:102) —
  locates and parses the Parquet footer (Thrift compact-encoded
  `FileMetaData`).
- [`probe_parquet_row_group_count`](../formal/fstar/Parquet.Footer.fst:433),
  [`probe_parquet_first_row_group_num_rows`](../formal/fstar/Parquet.Footer.fst:450),
  [`probe_parquet_first_row_group_column_count`](../formal/fstar/Parquet.Footer.fst:480) —
  row-group navigation.
- [`probe_parquet_column_compression_codec`](../formal/fstar/Parquet.Footer.fst:776) —
  must return `"ZSTD"` (§2). Zstd block decompression is delegated to
  the `parquet_zstd_decompress_hex` C stub (`assume val` at
  [`Parquet.Footer.fst:33`](../formal/fstar/Parquet.Footer.fst); see
  `experimental_ocaml_glue/parquet_zstd_stubs.c`).
- [`probe_parquet_column_decode_all`](../formal/fstar/Parquet.Footer.fst:2173) —
  per-column-chunk dispatcher: tries DLBA, falls back to RLE_DICTIONARY,
  returns the row's bytes as `option string` cells.

## 9. Conformance checklist

A producer claims v1 conformance iff it emits a file satisfying
**all** of the following:

- [ ] valid Apache Parquet file
- [ ] every column chunk compressed with ZSTD
- [ ] exactly four columns named `s`, `p`, `o`, `g`, in that order
- [ ] each column physical `BYTE_ARRAY`, logical `STRING`
- [ ] each column encoded with `DELTA_LENGTH_BYTE_ARRAY` or
      `RLE_DICTIONARY` (no other encoding)
- [ ] each cell is a non-empty UTF-8 string
- [ ] `s`-cells are IRI tokens or bnode tokens (per §4)
- [ ] `p`-cells are IRI tokens
- [ ] `o`-cells are IRI tokens, bnode tokens, or literal tokens
- [ ] `g`-cells are IRI tokens or the literal `DEFAULT`
- [ ] within any row group, all four columns have the same row count
- [ ] no NULL cells

A reader claims v1 conformance iff it can read every such file and
return the original quad sequence (modulo blank-node label scope —
labels are file-local, not globally fresh).

## 10. What is NOT in v1

The following were considered and deliberately excluded:

- **Producer-stamped format version.** pycottas 1.1.0 does not write
  a `cottas:format` or `factoidal:format` KV-metadata key. v1 is
  identified structurally (§3, §4, §6). A future v2 SHOULD add a
  KV-metadata key (provisional name `factoidal:cottas-format` =
  `"v2"`).
- **Index columns and secondary indexes.** Some upstream COTTAS
  variants ship per-permutation Parquet files (e.g. POSG, OSPG).
  v1 is single-permutation; the `index` KV-metadata key (§3) is
  advisory only.
- **Alternate compression.** Snappy, Brotli, LZ4 — explicitly out.
- **Bloom filters / column statistics.** Producers MAY emit them;
  v1 readers MUST treat them as advisory only.
- **Quoted triples / RDF-star.** Out of scope for v1. The token
  grammar in §4 has no production for `<<...>>` triple terms.
- **An F\*-only writer.** factoidal does not yet emit v1 files
  without going through pycottas. Future work — see
  `docs/designissues/cottas-native-backend.md`.

### Known reader gaps

The factoidal v1 reader at this commit (2026-04-25) has the
following honest gaps relative to this spec; they are acknowledged
deltas, not relaxations of the spec:

- **Multi-row-group iteration.** The current dispatcher
  [`probe_parquet_column_decode_all`](../formal/fstar/Parquet.Footer.fst:2173)
  decodes only the **first row group** of each column. A v1
  file with N > 1 row groups is currently truncated to row group 0
  on read. The 26-row-group parliament fixture therefore loads
  ~122,880 of 3,143,406 quads. A multi-row-group dispatcher is
  required for full v1 reader conformance and is the next item
  in this stack (working name `probe_parquet_column_decode_all_row_groups`
  in OCaml glue comments — not yet present in F\*).
- **N-Quads §7.4 escape decoding.** The OCaml-glue
  `unescape_literal` is naïve (§4 above). Full unescaping must
  move into F\* (e.g. `Parser.NQuads.unescape_lex`) and be wired
  into the cottas reader.

These gaps live in the **reader**, not the format. Files written
by pycottas are v1-shaped; factoidal's reader is partially v1.

## 11. Compatibility with pycottas

| pycottas version | v1-compatible? | Notes |
|:----------------:|:--------------:|:------|
| 1.1.0            | yes (last tested) | Parliament fixture 2026-04-25; column order `s,p,o,g`; encoding DLBA across all 4; sentinel `DEFAULT`; KV-metadata `{index: spog}`. |
| < 1.1.0          | unknown         | Not retested under v1 framing; column ordering and encoding choice may differ. |
| > 1.1.0          | unknown         | Forward-compatibility depends on pycottas's release notes. If pycottas adds e.g. additional columns or changes the default-graph sentinel, the resulting file is **not** v1; factoidal readers MUST reject it. |

If pycottas drifts, the migration path is:

1. Update factoidal's `tools/corpus_pipeline.py` to pin a known-good
   pycottas version (it currently does not pin).
2. If the new pycottas writes a different shape, define **v2** in a
   new file (`docs/cottas-format-v2.md`); leave this v1 spec
   untouched. v1 files keep working with v1 readers.

## 12. Forward-compatibility commitment

- factoidal v0.X+ readers MUST refuse a file whose schema does not
  match §3 exactly (column count, names, types, encoding allowlist).
- A future v2 of this spec, when defined, will be a new file
  (`docs/cottas-format-v2.md`) introducing a `factoidal:cottas-format`
  KV-metadata key; existing v1 files will continue to be accepted
  by v1 readers, and v2 readers will accept both v1 and v2.
- The on-disk byte layout of a v1 file is frozen by this document
  and will not be revised. Errata to this spec (clarifications, not
  format changes) are tracked as edits to this file with a
  `Last-revised:` line at the top.

---

**Last-revised:** 2026-04-25 (initial draft).
