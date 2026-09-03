# RDF parsing strategy in the Lean tree: layers, entry points, proofs, costs

Status: record of the design as it stands on 2026-09-03, written because the
owner asked for it to live somewhere findable (2026-09-03: "this and similar
ought to be recorded properly somewhere I can find it. Ephemeral coding logs
aren't that place"). Update this file when a layer, an entry point or a
proof changes; the worknote index and the `factoidal-lean-basics` skill link
here.

## 1. The shape: one meaning, several executions, proofs between them

Every concrete syntax has ONE reference parser that is the meaning, ported
from the F\* source production by production. Faster or streaming executions
are added beside it, never instead of it, and each one carries a theorem (or,
until the theorem lands, a differential test) that it computes the same
function as the reference on the inputs it accepts. The W3C syntax suites
gate the reference parser; byte-identity of packed artifacts and the
theorems gate the other executions.

## 2. Turtle

### 2.1 Reference parser: `L4Factoidal/Syntax/Turtle.lean`

- Entry points: `parseTurtle text base mode : Except ParseError Graph`
  and `parseTurtleFold step init text` (folds completed statements
  without building a second graph). Both turn the whole document into a
  `List Char` and run a fuel-bounded recursive descent that follows the
  W3C Turtle grammar (productions numbered in comments, `[16]
  NumericLiteral`, `[17] String`, `[26] UCHAR`, ...). RDF 1.1 and 1.2 modes
  (triple terms, reifiers, annotations, `VERSION`, base direction).
- Consumers: `l4factoidal parse` (`Harness/Run.lean`), the W3C runner
  (`Harness/Manifest.lean`), the WASM `parse` and `datasetOpen` Turtle path
  (`Wasm/Ops/Parse.lean`), and every probe and pack tool other than the
  shard packer.
- Fuel: each bounded loop takes a fuel argument as the F\* source does. The
  statement-level fuel is `cs.length + 2` computed ONCE per document. The
  literal loops (`readShortStringBody`, `readLongStringBody`, `collectNum`)
  take the constant `literalFuel = 2^32` since 2026-09-02; the per-token
  forms are kept as `readTurtleStringSpec` / `readNumericLiteralSpec`.
  Computing `cs.length` per token was quadratic (20,019 lines: 6.16 s, now
  0.74 s).
- Gates: W3C RDF 1.1 Turtle (313) and TriG (356); RDF 1.2 Turtle syntax
  (67) and eval (29), TriG syntax (35) and eval (25); all 0 fail on
  2026-09-02.

### 2.2 Streaming execution for the shard packer

Modules, in data order:

1. `Utf8Stream.lean`: bounded incremental UTF-8 decoding of 64 KiB byte
   chunks; keeps at most the final three undecoded bytes; rejects invalid
   interior data; never chooses a statement boundary.
2. `TurtleStatementScan.lean`: a per-character mode machine (`normal`,
   `iri`, `comment`, short string, long string, opening-quote run) that
   proposes candidate statement texts. A candidate ends at a `.` in normal
   mode followed by whitespace or `#`, or at a line end when the current
   text starts with `PREFIX`, `BASE` or `VERSION` (the SPARQL-style
   directives have no dot). It keeps `head`, the first seven characters
   after leading whitespace, so the directive test is O(1) per line end.
   The scanner never decides syntax; the grammar accepts or rejects every
   candidate.
3. `TurtleChunkFold.lean`: hands each candidate to `readStatement` from
   the reference grammar with the fuel `text.length + 2` computed once per
   candidate, carrying `TurtleState` (prefixes, base, blank-node prefix,
   mode) across candidates and chunks; retains only the unfinished
   candidate.
4. `Harness/PredicateShardPack.lean`: a first pass over the file computes
   the SHA-256 and the blank-node prefix; the second pass feeds chunks to
   the fold and publishes the completed triples as `IBK3` blocks every 64
   chunks (about 4 MiB), so a predicate whose rows span several windows
   gets several blocks (the 309 blocks over 232 predicates of the UK
   Parliament dump).

The scanner is used only by the shard packer; the WASM mirrors do not
contain it.

### 2.3 Proofs

- `TurtleFuelTheorems.lean` (2026-09-02): the three literal loops are the
  same function for every fuel above the remaining length
  (`*_fuel_indep`), so the constant-fuel readers equal the specification
  forms for every input shorter than 2^32 characters
  (`readTurtleString_eq_spec`, `readNumericLiteral_eq_spec`).
- `TurtleStatementScanTheorems.lean` (2026-09-03): `head_eq_spec`, the
  scanner's head field equals `directiveHeadSpec currentRev` (the old
  reverse-and-drop-whitespace form) after any run from `init`.
- `TurtleTheorems.lean`, `SyntaxTheorems.lean`: earlier properties of the
  reference parser (see the files).
- Not yet proved: that the streaming execution (2.2) equals `parseTurtle`
  on the same text. The gate today is byte identity of packed generations
  across scanner changes (378 artifacts on a 370,355-triple slice,
  2026-09-03) and the five committed hub blocks under
  `docs/web/hub/assets/blocks/lifesci-crossgraph/`. The N-Quads tree has
  the theorem this one still needs (`NQuadsStreaming.lean`, section 3).

### 2.4 Costs paid and costs open

| Date | Cost | Cause | Fix |
| --- | --- | --- | --- |
| 2026-04 | stack overflow on large Turtle | non-tail recursion | `docs/2026-04-21-large-turtle-stack-overflow-fix-sketch.md` |
| 2026-09-02 | quadratic `parseTurtle` | per-token `cs.length + 1` fuel in two literal readers | constant `literalFuel` + proofs |
| 2026-09-02/03 | UK Parliament pack 6,134 s | scanner reversed the whole candidate at every line end; a 134 MB, 4,211-line statement group | seven-character `head` + proof; pack 254 s |
| open | 19 s user + 9 s system to parse 134 MB | `List Char` representation: about 16 bytes and one allocation per character, built twice (scanner `currentRev`, then `text.toList` for the grammar) | a `String`/`ByteArray`-position lexer with its own equality proof against 2.1 |
| open | multi-megabyte literals cost seconds each in the packer | every literal goes through the term codec, PTD1 pages, TLI1 keys and Merkle leaves | large-literal policy (corpus ladder, `docs/20260902-persisted-query-ladder.md`) |

## 3. The other syntaxes, briefly

| Syntax | Reference | Other executions | Agreement |
| --- | --- | --- | --- |
| N-Triples | `NTriples.lean` `parseNTriples` | — | W3C suite; `NTriplesRoundTrip.lean` |
| N-Quads | `NQuads.lean` `parseNQuads` | `NQuadsFast.lean` `parseNQuadsFast` (bucketed accumulator; the WASM `datasetOpen` path); `NQuadsStreaming.lean` (chunk-boundary fold), `NQuadsFold.lean` | `parseNQuadsFast_eq_parseNQuads` proved 2026-09-02 (`NQuadsFastTheorems.lean`); the streaming module carries its own chunk-boundary theorem |
| TriG | `TriG.lean` `parseTriG` (shares the Turtle productions; the default graph is the unlabelled block) | none; the shard packer reads Turtle only (quad-aware layout: `2026-09-02-quad-aware-block-layout.md`) | W3C suites |
| RDF/XML | `RdfXml.lean` | — | W3C suite; `RdfXmlTheorems.lean` (blank-node label spaces disjoint by construction) |

Shared lexical pieces: `Lexing.lean` (the N-Triples string body and escape
table the Turtle `decodeEscape` mirrors), `IriResolve.lean` (RFC 3986),
`IriScan.lean`, the `Locality*.lean` family (chunk-locality lemmas used by
the N-Quads streaming proofs).

## 4. Rules that follow

1. A new fast path is added beside the reference parser with a theorem or,
   until the theorem lands, a differential tool named in this file.
2. Any per-character or per-line decision in a streaming scanner reads O(1)
   state, never the accumulated text (`skills/lean4-performance`).
3. Fuel is computed once per document or per candidate, never per token
   (`skills/lean4-proof-patterns` section 2 has the theorem shape).
4. Before reading code for a superlinear ingest, run a size ladder without
   the suspect inputs and isolate the region that misbehaves
   (`docs/20260902-persisted-query-ladder.md`, "Where the 6,134 s went").
