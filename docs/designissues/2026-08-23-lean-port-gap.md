# Lean 4 port: what is still absent

Generated 2026-08-23 by comparing `formal/fstar/*.fst` (220 modules)
against `formal/lean4/L4Factoidal/**/*.lean` (236 modules), with an
explicit alias table for the modules that were renamed on the way
across (`Parser.XML` to `XML.Parser`, `RDF.Term` to `RDF.Core`, and
so on). The script is `tools/lean-port-gap.py`.

## Summary

| Kind | Modules | F\* lines |
|---|---|---|
| Engine and specification code — to port | 56 | 39192 |
| Proofs about the F\* implementation — see below | 32 | 33861 |
| F\*-only machinery with no Lean counterpart by design | 7 | 2861 |
| **Total not covered** | **95** | **75900** |

125 of the 220 F\* modules have a Lean counterpart.

Updated 2026-08-23 after all three HDT modules and `XSD.IEEE754`
landed, and after ONE false negative was corrected: `DID.Key` has been
covered by `L4Factoidal/VC/DidKey.lean` all along — all 18 of its F\*
definitions have a Lean counterpart — but the alias table did not know
the module had been renamed on the way across. The HDT and XSD groups are now empty.

**CORRECTION, same day, later.** The first audit of the not-covered
list was by squashed MODULE NAME and concluded "no other false
negative". It was too weak and that claim was wrong. Name matching
cannot see a CONSOLIDATION — one Lean module covering two F\* modules
under a third name — and cannot see a rename that changes more than
punctuation.

A second audit compared DEFINITION NAMES: every `let` / `val` / `type`
of each not-covered F\* module against every `def` / `abbrev` /
`structure` / `inductive` / `theorem` in the Lean tree, normalised for
case and underscores. It found four more:

| F\* module | Lines | Actually covered by |
|---|---|---|
| `RDF.Entailment.Simple` | 182 | `L4Factoidal/RDF/Entailment.lean` |
| `RDF.Entailment.Regime` | 271 | the same file |
| `Parser.CSVResults` | 610 | `L4Factoidal/SPARQL/ResultsCsvTsv.lean` |
| `RDF.Pretty` | 235 | ported this session; alias added |

The first two are the consolidation case exactly: one Lean module covers
simple entailment AND the D / RDF / RDFS regimes, which the F\* tree
splits across two files. `Parser.CSVResults` is a rename the alias table
did not carry.

⚠️ **One narrow behavioural gap inside that coverage, recorded rather
than papered over.** The F\* `match_term` takes a POSITION-AWARE literal
comparison, `leq : inside_tt -> literal -> literal -> bool`, because a
directional language string is opaque — compared case-sensitively — only
INSIDE a triple term. Lean's `entailsWith` takes
`leq : Literal -> Literal -> Bool` with no position flag. The coverage is
substantive but not complete, and the difference is what the W3C
`opaque-dir-language-string` fixtures exercise.

`SPARQL11.IRI.Resolve` (38 lines) stays in the not-covered column on
purpose: it is a pure re-export shim for `RDF.IRI`'s `resolve_iri` /
`resolve_query_iri`, and `RDF.IRI` (530 lines) is not ported. Lean has
`Syntax.IriResolve.resolveIri` but no `resolveQueryIri`.

Second update the same day, after a batch of five more: `Dep.Reachability`,
`RDFS.Closure.SemiNaive`, `RDF.Dataset.Graphs`, `SPARQL.Update.Analysis`
and `SPARQL.Query.Analysis`. The `Dep` group is now empty and `RDFS` is
down to one module.

Third: `RDF.Canonical.Manifest`, `RDF.Dataset.Merge`, `RDF.Format` and
`SPARQL.JSON.Escape`. Fourth: `SPARQL.Eval.Limits`,
`SPARQL.Eval.TimeBudget` and `OWL.DirectMapping.Filter`. Fifth:
`RDF.Entailment.RDFSPlus`.

### `RDF.List.Helpers` is a by-design non-port

`RDF.List.Helpers` (195 lines) is tail-recursive replacements for
`FStar.List.Tot`'s `append` and `concatMap`, which are straightforward
structural recursions that overflow the OCaml stack on long lists —
issue #94 on the Turtle parser path, and the 2026-04-26 BGP filter-map
incident. Lean's `List.append` already carries a tail-recursive
`@[implemented_by]` version, so the module's reason for existing is
absent. It belongs with `Parser.FastString.*` in the "no Lean
counterpart by design" column rather than in the to-port column;
recorded here because a bare module count would otherwise read it as an
omission.

### On the proof column

These are F\* modules whose content is a proof about the F\*
implementation: `.Spec`, `.Refinement`, `.ModelTheory`,
`.Completeness`, `.Axioms`, `.RoundTrip`. The Lean tree carries its
own theorem modules (`*Theorems.lean`, `RLTheorems`,
`TableauTheorems`, `SyntaxTheorems`, and the `#guard` layer), so a
module-for-module port is not the right measure of this column. What
IS the right measure — which obligations the F\* discharges that the
Lean does not — has not been computed. Recording that as unknown
rather than as zero.

### On the F\*-only column

`Parser.FastString.*`, seven modules. The F\* parser indexes raw
UTF-8 bytes, so it needs machinery to rebuild codepoints from bytes
and reject invalid sequences. Lean's `String` and `Char` are
codepoint types and `Char` is a valid scalar value by construction,
so that machinery has no counterpart. `L4Factoidal/XML/Document.lean`
states this in its header.

## Engine modules, by area

### RDF.CottasStore + RDF.Store — 22 modules, 10440 lines

- `RDF.CottasStore` (2825)
- `RDF.CottasStore.BaseWriter` (1282)
- `RDF.Store.Columnar.DeltaMerge` (934)
- `RDF.CottasStore.DictWriter` (669)
- `RDF.Store.Capabilities` (504)
- `RDF.CottasStore.PageCache` (474)
- `RDF.CottasStore.OnDiskIndex` (425)
- `RDF.Store.Columnar.OffsetIndex` (408)
- `RDF.CottasStore.OffsetsWriter` (404)
- `RDF.CottasStore.CompoundPresenceWriter` (394)
- `RDF.CottasStore.CompoundPresenceBitmap` (362)
- `RDF.CottasStore.SubjectOffsetsWriter` (272)
- `RDF.Store.Columnar.SubjectOffsetIndex` (260)
- `RDF.CottasStore.PresenceBitmap` (257)
- `RDF.CottasStore.PresenceWriter` (242)
- `RDF.CottasStore.ColumnSeq` (163)
- `RDF.Store.Capabilities.Delta` (138)
- `RDF.Store.Capabilities.Cottas` (124)
- `RDF.Store.Combine` (85)
- `RDF.CottasStore.LazyDict` (83)
- `RDF.Store.LazyTermCache` (83)
- `RDF.CottasStore.LazyDictRegistry` (52)

### RDF — 13 modules, 7524 lines

- `RDF.NQuads.Streaming` (3438)
- `RDF.Entailment.RDFS.RhoDFClosure` (1996)
- `RDF.IRI` (530)
- `RDF.Entailment.Simple.Boundary` (332)
- `RDF.Entailment.Regime` (271)
- `RDF.Pretty` (235)
- `RDF.List.Helpers` (195)
- `RDF.Entailment.Simple` (182)
- `RDF.Format` (103)
- `RDF.Entailment.RDFSPlus` (93)
- `RDF.Dataset.Merge` (69)
- `RDF.Entailment.RegimeDispatch` (53)
- `RDF.Dataset.Graphs` (27)

### SPARQL11 — 4 modules, 4839 lines

- `SPARQL11.Algebra.BGPRefinement` (2234)
- `SPARQL11.Store` (1452)
- `SPARQL11.EntailmentRegime.RDFS` (1115)
- `SPARQL11.IRI.Resolve` (38)

### Parser — 7 modules, 4462 lines

- `Parser.JSONLD` (1459)
- `Parser.RIFXML` (1349)
- `Parser.CSVResults` (610)
- `Parser.BallyhooHDT` (352)
- `Parser.SRX` (291)
- `Parser.BallyhooCOTTAS` (241)
- `Parser.JSONResults` (160)

### Parquet — 1 modules, 3349 lines

- `Parquet.Footer` (3349)

### OWL — 4 modules, 2797 lines

- `OWL.QueryRewrite` (1799)
- `OWL.Semantics` (876)
- `OWL.DirectMapping.Filter` (71)
- `OWL.QueryEval` (51)

### SPARQL — 12 modules, 1984 lines

- `SPARQL.Update.Sandbox` (323)
- `SPARQL.Plan.Streamable` (301)
- `SPARQL.Plan.AccessPath` (257)
- `SPARQL.Plan.Pruning` (256)
- `SPARQL.FullText` (223)
- `SPARQL.Eval.TimeBudget` (133)
- `SPARQL.Eval.Limits` (128)
- `SPARQL.Explain` (104)
- `SPARQL.JSON.Escape` (97)
- `SPARQL.Diagnostics` (78)
- `SPARQL.Query.Analysis` (53)
- `SPARQL.Update.Analysis` (31)

### Tableau — 1 modules, 1663 lines

- `Tableau.CountingOracle` (1663)

### HDT — 0 modules (complete)

All three F\* modules are ported: `HDT.Container` (644 lines),
`HDT.Dictionary` (519) and `HDT.Triples` (316), 1,479 lines in total.

Four F\* definitions have no work to do in Lean and are absent: the
file-size probe (`hdt_file_size` and its two helpers), the hex decode
(`hdt_bytes_of_hex`, `collect_bytes`), `nat_xor`, and `nat_sub` —
Lean's `Nat` subtraction already truncates at zero. Each module's
header says which and why.

`tools/hdt-tree-differential.sh` runs both trees' probes over the two
vendored fixtures and diffs their output:

**HDT reader, F\* vs Lean 4: 2 agree, 0 differ (out of 2)** — 54
container, dictionary and triples lines identical per fixture. That
includes the strongest check either tree makes: enumerating every
triple out of the HDT file and comparing the result with the `.nt` the
file was built from, as sorted canonical N-Triples. Both fixtures
report MATCH (1 triple, and 343 triples).

### RDFS — 1 module, 808 lines

- `RDFS.SchemaSplit` (808)

`RDFS.Closure.SemiNaive` (421 lines) is ported as
`L4Factoidal/RDFS/SemiNaive.lean`. Agreement with the naive closure is
measured by `lake exe l4rdfs-semi`: **6 agree, 0 differ (out of 6)**
over subclass chains and property hierarchies at 20, 50 and 100 input
triples, with closures of 210 to 5,056 triples, and the delta loop
reached the fixed point without the fallback in all 6 — which is what
says the delta loop did the work rather than being bypassed.

⚠️ SPEED IS NOT MEASURED. The module exists for speed and three timing
attempts all read 0 ms while the run cost 90 s of CPU. See
https://github.com/danbri/factoidal/issues/554. `closureSemiNaiveChecked`
returns the naive answer whenever the delta loop is not a fixed point,
so a hole in the delta reasoning costs a slow run, never a wrong one —
which is what makes the module usable without that number.

### SHACL — 2 modules, 1151 lines

- `SHACL.NodeExpr` (713)
- `SHACL.Rules` (438)

### RML — 2 modules, 830 lines

- `RML.Sources` (455)
- `RML.VirtualSource` (375)

### OWL2 — 1 modules, 648 lines

- `OWL2.SyntaxDL` (648)

### RIF — 1 modules, 593 lines

- `RIF.Core.Translation` (593)

### JSONLD — 1 modules, 335 lines

- `JSONLD.Frame` (335)

### XSD — 0 modules (complete)

`XSD.IEEE754` (292 lines) is ported as `L4Factoidal/XSD/IEEE754.lean`:
decimal lexical to IEEE-754 value in exact big-integer rational
arithmetic, with no floating point in any definition.

`IEEE754Tests.lean` checks it against an INDEPENDENT correctly-rounded
implementation rather than a restatement of the same algorithm: 66
lexicals converted by CPython's `float()` (a correctly-rounded
`strtod`), with the bit patterns read out by `struct.pack`. **All 66
rows match, bit for bit, in binary64 and binary32.** The table is
chosen for the 2^53 and 2^24 boundaries, one-ulp neighbours, the
smallest subnormal and its halfway point, `2.2250738585072011e-308`
(the decimal that hung PHP's `strtod` in 2011), overflow to infinity,
underflow to zero, and signed zero / infinities / NaN.

### DID — 0 modules (was a false negative)

`DID.Key` is covered by `L4Factoidal/VC/DidKey.lean`. The alias table
in `tools/lean-port-gap.py` now records the rename.

### DID — 1 modules, 195 lines

- `DID.Key` (195)

### Dep — 0 modules (complete)

`Dep.Reachability` (170 lines) is ported. Its two theorems —
`closedSetCatchesAll` and `noRootReaches` — carry `[propext,
Quot.sound]` only. The F\* `reaches` is a `Type`-valued GADT because the
proof recurses on the derivation term; in Lean it is a `Prop`-valued
inductive proved by `induction`, and `no_root_reaches`'s
`FStar.Classical.impl_intro` disappears because `¬P` IS `P → False`.

