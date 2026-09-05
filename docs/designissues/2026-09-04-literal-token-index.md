# A literal search index for block storage (LGI1)

Date: 2026-09-04.
Owner steer, 2026-09-04, verbatim: "the OWL thing is important but scaling
our database is much more important."

## 1. The problem, measured

A SKOS chat bot asks one question of a 141-graph store: which concepts carry
a label that contains a word. The store handle is held open, so the manifest
verification and the block decode are paid once.

| step | time |
|---|---|
| open the handle | 2,670 ms, once |
| search "water" | 252 ms |
| search "bicycle" | 177 ms |
| search "glacier" (0 rows) | 179 ms |

A miss costs the same as a hit. `CONTAINS` is evaluated per row, so the cost
is O(rows) and no storage change moves it.

| store | `skos:prefLabel` rows | search |
|---|---|---|
| today, a 60 MB subset | 45,806 | about 180 ms |
| the full skosdex corpus, about 9.2x | about 421,000 | about 1.7 s |

The corpus has not been repacked because repacking makes search nine times
slower. An index is what makes corpus size stop mattering.

## 2. The decision: character n-grams, not tokens

### 2.1 Why not tokens

`CONTAINS(LCASE(STR(?l)), "water")` is a SUBSTRING test. An index over
whitespace-separated tokens does not answer it. "underwater" contains "water"
and is not the token "water"; "waters" likewise. A token index that answered
this query would drop rows, and it would drop them silently. The only way to
use a token index here is to change what the query means, which is not
available: the queries are written by a chat bot against SPARQL 1.1, and
`CONTAINS` has a fixed definition in section 17.4.3.11.

The repository already has a token construction — `SPARQL/FullText.lean`, the
`text:query` extension. It stays where it is. It answers a DIFFERENT question
and it is reached through a different syntax.

### 2.2 What is indexed

**Character 3-grams of the case-folded lexical form of every literal term in
the block dictionary.**

* The unit is a CHARACTER (Unicode codepoint), not a byte, because
  `Expr.strContains` compares `List Char`. A byte n-gram index would be a
  second, disagreeing notion of substring.
* The fold is `String.toLower`, the SAME function `Expr` evaluates for
  `LCASE`. It is reused, not restated, so the index fold and the query fold
  cannot drift apart. In the current toolchain `Char.toLower` maps `A`-`Z`
  and nothing else; that fact is not relied on, only the identity of the two
  functions is.
* `n = 3`. A needle of fewer than 3 characters falls back to the scan.
* Every literal in the block dictionary is indexed. Coverage is therefore
  total for the block: if the sidecar is present and its
  `targetIBKSha256` matches the block, every literal the block can produce in
  object position is in the index. A query never has to ask whether the index
  covers what it needs; it asks whether the sidecar is present.

### 2.3 The index is a CANDIDATE FILTER, and that is the soundness argument

The index never decides a row. It returns a SUPERSET of the matching literal
terms, and the planner then evaluates the original, unmodified `FILTER`
expression on each candidate row. Rows are therefore identical to the scan by
construction, not by resemblance: the scan evaluates the filter on every row,
the index path evaluates the same filter on a subset that provably contains
every row the filter accepts.

The superset property is the theorem, in `Storage/LiteralGramIndex.lean`:

    fold is applied per character, so
      strContains s k  ->  strContains (fold s) (fold k)
    and a contiguous window of a contiguous sublist is a contiguous window
    of the whole, so
      strContains (fold s) (fold k)
        ->  every gram of (fold k) is a gram of (fold s)

so a literal the filter accepts carries every gram of the folded needle, and
is present in every posting list the lookup intersects.

`STRSTARTS` and `STRENDS` imply `CONTAINS`, so they use the same posting
lists with the same re-check.

### 2.4 Exactly which SPARQL expressions use the index

Admissible, for a variable `?o` bound by a single triple pattern
`?s <P> ?o` (bare, or under one `GRAPH` layer):

| expression | uses the index |
|---|---|
| `CONTAINS(?o, "k")` | yes |
| `CONTAINS(STR(?o), "k")` | yes, and see the `STR` rule below |
| `CONTAINS(LCASE(STR(?o)), "k")` | yes, and see the `STR` rule below |
| `CONTAINS(LCASE(?o), "k")` | yes |
| `STRSTARTS`/`STRENDS` in the same four shapes | yes |
| any of the above as a conjunct of `&&` | yes, on that conjunct |

**The `STR` rule, added 2026-09-05 when the planner was written.** The table
above was wrong for the two `STR` shapes as first stated. `STR` of an IRI is
that IRI's string, so `CONTAINS(STR(?o), "water")` is TRUE for an IRI whose
text contains `water`; LGI1 indexes LITERALS only, because `foldedOfTerm`
gives a non-literal no gram. Restricting to candidates alone would therefore
DROP those rows. A shape that applies `STR` must additionally keep every row
whose object is not a literal. A shape without `STR` drops them, because
`CONTAINS` on an IRI is a type error and the filter excludes the row anyway.
This is `LiteralIndexPlan.Plan.keepNonLiterals`.

Falls back to the scan, silently and correctly:

| expression | why |
|---|---|
| `"k"` shorter than 3 characters | no 3-gram to look up |
| `"k"` not a plain string literal, or a variable | the needle is not known at plan time |
| `REGEX(...)` | a regular expression is not a substring test |
| `UCASE(...)` | folds the wrong way; a `UCASE` index is a separate decision |
| `!CONTAINS(...)` | the complement is not a superset of anything useful |
| `CONTAINS(...)` under `\|\|` | one disjunct being false does not exclude the row |
| a filter on a variable the pattern does not bind in object position | no posting list applies |
| the block has no `.lgi1` sidecar | fall back, so old generations keep working |

The fallback is always correct, exactly as `StoreFastPath`'s detectors are:
matching a shape the index cannot serve is the only failure mode, so every
rejection above is load-bearing.

## 3. The wire format

A new sidecar beside `.tli1`, `.sri2` and `.oli2`, in the same framing:
fixed prefix, then a sorted directory, then a payload area, then CRC-32C.

    file  <block>.lgi1
    magic "LGI1", 0x3149474C little endian
    version 1

    prefix (fixed, 61 bytes)
      u32   magic
      u8    version
      [32]  targetIBKSha256
      u32   gramLength      -- 3
      u32   literalCount    -- indexed literal terms
      u32   gramCount       -- distinct grams
      u32   directoryBytes
      u32   postingsBytes

    directory (gramCount entries, sorted by gram bytes, ascending)
      u32   gramByteLength
      [..]  gram, UTF-8 of the gramLength folded characters
      u32   offset          -- into the postings area
      u32   length          -- bytes
      u32   postingCount

    postings (per gram, ascending local term IDs)
      the first ID as a u32; each later ID as a u32 gap from the previous

    u32   crc32c(payload)

The directory is one entry per gram rather than a page directory, because a
lookup wants one posting run and nothing else: a range reader fetches the
prefix, the directory, and then only the runs its needle names.

Local term IDs are the same PTD1 dictionary positions TLI1 uses, so a
candidate ID reaches rows through the existing OLI2 object index without a
second identity scheme.

The encoder and decoder are `Storage/LiteralGramIndexWire.lean`, with the
same spec/impl pair the rest of the family has: `decodeSpec?` over
`List UInt8` states what LGI1 admits, `decode?` reads the artifact by
byte-array index, and `decode?_eq_spec` proves the two agree on every input.
Encoder admission equals decoder admission.

Version 1 stores gaps as fixed u32. A variable-length gap encoding is a
version 2 decision; it needs a round-trip theorem of its own and it is not
worth delaying the format for.

## 4. Size and speed, measured

`l4block-literal-gram` (`formal/lean4/Harness/LiteralGramProbe.lean`) on the
`skos:prefLabel` block of the SKOS store, `predicate-7.ibk4`.

| part | measured |
|---|---|
| block | 5,571,302 bytes, 45,806 rows |
| dictionary | 60,856 terms, 41,619 of them literals |
| distinct grams | 21,843 |
| postings | 641,709 |
| LGI1 bytes, u32 gaps | 3,018,145, **54% of the block** |
| index build | 5.6 s, at pack time only |

Answering `CONTAINS(LCASE(STR(?o)), needle)` over that block. Best of five;
the measurement machine was at load 149, so both columns are inflated and
their ratio is the reading that carries.

| needle | rows | scan | index | ratio |
|---|---|---|---|---|
| water | 265 | 211,990 us | 566 us | 375x |
| bicycle | 4 | 272,443 us | 50 us | 5,449x |
| **glacier (miss)** | 0 | 241,348 us | **58 us** | **4,161x** |
| climate change | 14 | 252,200 us | 219 us | 1,152x |
| ab | 805 | 192,045 us | index not used, falls back | 1x |

The rows returned through the index equal the rows returned by the scan for
every needle, compared as row lists.

The 54% is the price of version 1's fixed-width gaps and is the reason
version 2 wants a variable-length encoding: the same postings at a
gap-weighted 1.3 bytes come to about 1.2 MB, about 22% of the block.

## 5. Manifest

SBM6 carries three sidecar roles: `subjectIndex`, `termIndex`, `objectIndex`.
SBM7, the IBK4 quad manifest the SKOS store uses, carries none.

**Landed 2026-09-05 as manifest wire version 8**, layout label
`quad-ibk4-ptd1-lgi1-merkle-v0`. The entry gains `literalIndex : Option
ArtifactRef`, carrying the sidecar's key, extent, SHA-256 and its own Merkle
chunk commitment exactly as the other three roles do. It is written where
SBM6 writes its object index, before the quad tail, so the decoder reads one
field sequence and not a version-dependent reordering.

**Why a version bump was unavoidable.** The role is a new per-entry FIELD, so
either form of it changes SBM7's bytes: mandatory at 7 makes every existing
SBM7 manifest undecodable, and optional at 7 needs a presence byte that
existing SBM7 manifests do not carry. Encoder admission equals decoder
admission and a byte change means a new wire version. (This is a different
question from how many entries a predicate may have, which
`ShardManifest.valid` already permits above version 1 through
`uniquePredicates`.)

The role is MANDATORY at 8 and must be ABSENT below it, for the same reason
SBM7's three additions are: a manifest below 8 carrying one would encode to
bytes that drop it and the round trip would lose data silently. A block whose
dictionary holds no literal carries an LGI1 with no gram rather than no
sidecar, so an SBM8 reader never asks whether the role is present; it asks
whether the manifest is SBM8.

Old generations are unaffected. `decode?` still admits SBM0 to SBM7,
`isIbk4Layout` names both labels, and `l4block-quad-query` accepts 7 and 8.
`ShardManifestTheorems.decode?_encode?` covers version 8 with the same
statement and the same three axioms (`propext`, `Classical.choice`,
`Quot.sound`).

**What activation checks, and what it does not.** `GenerationVerify`
checks the sidecar's declared SHA-256 like any artifact, then decodes it and
requires that it names THIS block by `targetIBKSha256` and is sized for this
block's dictionary (`dictCount` and `literalCount` recomputed from the
block). It does NOT recompute the posting lists: building the index of the
`skos:prefLabel` block costs 5.6 s, and an activation that rebuilt every
block's index would pay that per block. What that leaves uncaught is a PACKER
fault that wrote a self-consistent index of the wrong content; tampering
after the pack is caught by the digest. The consequence is bounded — the
index is a candidate filter and the planner re-evaluates the original
expression, so a wrong index can only DROP rows, never add them — but it is
weaker than the TLI1 and OLI2 checks, which do recompute. Open work.

## 6. Staging

1. **Landed.** This record.
2. **Landed.** `Storage/LiteralGramIndex.lean` — the fold, the grams, the
   index and its lookup, and the superset theorem. This is the semantic core;
   nothing downstream may restate a fold or a gram.
3. **Landed.** `Storage/LiteralGramIndexWire.lean` — LGI1 bytes, with
   encoder admission equal to decoder admission and `#guard`s over the round
   trip and four rejections. There is one decoder, so no `decodeSpec?` pair
   and no equality theorem is claimed; a byte-indexed reader beside a list
   reader, with the proof that the two agree, is a later optimisation.
4. **Landed.** `Harness/LiteralGramProbe.lean` — the row-identity gate and
   the measurement of section 4.
5. **Open.** The packer writes `.lgi1`; manifest version 8 commits its
   SHA-256. SBM7, which the SKOS store uses, has no sidecar role at all, so
   this is a manifest version, not a field.
6. **Open.** The planner detects the admissible shapes of section 2.4,
   intersects posting lists, re-evaluates the original filter on the
   candidates, and falls back otherwise. Until this lands the shipped query
   path still scans, and the numbers in section 4 are the mechanism measured
   through the probe, not through `storeHandleQuery`.

## 7. The gate

Identical answers. For every shape in the section 2.4 admissible table, the
ROWS returned with the index equal the rows returned by the scan, compared as
rows and not as counts (anti-pattern 34). The comparison runs over the real
SKOS store, and it is built before any measurement is taken.

The measurement to report is the MISS: an index that does not make
`CONTAINS(..., "glacier")` fast on a store that has no such label has not
indexed anything.

## 8. Out of scope here

The query caps, the IBK4 wire version, and block splitting. Each is separate
work.
