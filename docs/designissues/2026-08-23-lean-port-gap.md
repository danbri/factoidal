# Lean 4 port: what is still absent

Generated 2026-08-23 by comparing `formal/fstar/*.fst` (220 modules)
against `formal/lean4/L4Factoidal/**/*.lean` (236 modules), with an
explicit alias table for the modules that were renamed on the way
across (`Parser.XML` to `XML.Parser`, `RDF.Term` to `RDF.Core`, and
so on). The script is `tools/lean-port-gap.py`.

## Summary

| Kind | Modules | F\* lines |
|---|---|---|
| Engine and specification code — to port | 76 | 42501 |
| Proofs about the F\* implementation — see below | 32 | 33861 |
| F\*-only machinery with no Lean counterpart by design | 7 | 2861 |
| **Total not covered** | **115** | **79223** |

105 of the 220 F\* modules have a Lean counterpart.

Updated 2026-08-23 after all three HDT modules landed. The HDT group
is now empty; see the section below for what it cost and what it
measures.

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

### RDFS — 2 modules, 1229 lines

- `RDFS.SchemaSplit` (808)
- `RDFS.Closure.SemiNaive` (421)

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

### XSD — 1 modules, 292 lines

- `XSD.IEEE754` (292)

### DID — 1 modules, 195 lines

- `DID.Key` (195)

### Dep — 1 modules, 170 lines

- `Dep.Reachability` (170)
