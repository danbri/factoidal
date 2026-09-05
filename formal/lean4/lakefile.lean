import Lake
open System Lake DSL

/-!
Lake configuration for the Lean 4 port (library `L4Factoidal`).

This file was `lakefile.toml` until the VC Data Integrity stage
(2026-08-22). It became a Lean-DSL lakefile for ONE reason: the TOML
format has no `extern_lib` target, and the Ed25519 signature primitive
must be HACL*'s verified C compiled and linked by Lake itself
(`skills/crypto-policy/SKILL.md`, Lean 4 amendment — signatures via
HACL* FFI only). Everything else below is the mechanical
`lake translate-config lean` output of the former TOML, comments
carried over.
-/

package l4factoidal

/-! ## Native executable-edge externs

`L4Factoidal/Crypto/Ed25519.lean` declares three `opaque`s with
`@[extern "l4_hacl_ed25519_*"]`, and `L4Factoidal/Crypto/SHA2Native.lean`
one more with `@[extern "l4_hacl_sha256"]`. They are realised by
`ffi/hacl_ed25519.c`, a length-checking shim over the vendored,
F*/Low*-verified HACL* extracted C under `third_party/hacl/`
(Apache-2.0; provenance in `third_party/hacl/PROVENANCE.md`). The three
HACL* translation units are compiled UNMODIFIED, exactly as the F*
tree's `build-ocaml.sh` compiles them (`-O2 -fPIC -I include`), and
archived into `libl4hacl.a`, which Lake links into every executable of
this package. -/

/-- `third_party/hacl`, relative to this package (`formal/lean4`). -/
def haclDir (pkg : Package) : FilePath :=
  pkg.dir / ".." / ".." / "third_party" / "hacl"

/-- Compile one C translation unit with the package's HACL* include
path and Lean's include path. -/
def buildHaclO (pkg : Package) (oName : String) (src : FilePath) : SpawnM (Job FilePath) := do
  let oFile := pkg.buildDir / "ffi" / (oName ++ ".o")
  let srcJob ← inputTextFile src
  let weakArgs := #["-I", (← getLeanIncludeDir).toString,
                    "-I", (haclDir pkg / "include").toString]
  buildO oFile srcJob weakArgs #["-O2", "-fPIC"] "cc" getLeanTrace

target hacl_ed25519_shim.o pkg : FilePath :=
  buildHaclO pkg "hacl_ed25519_shim" (pkg.dir / "ffi" / "hacl_ed25519.c")

target Hacl_Ed25519.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Ed25519" (haclDir pkg / "src" / "Hacl_Ed25519.c")

target Hacl_Curve25519_51.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Curve25519_51" (haclDir pkg / "src" / "Hacl_Curve25519_51.c")

target Hacl_Hash_SHA2.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Hash_SHA2" (haclDir pkg / "src" / "Hacl_Hash_SHA2.c")

extern_lib libl4hacl pkg := do
  let shim ← hacl_ed25519_shim.o.fetch
  let ed ← Hacl_Ed25519.o.fetch
  let curve ← Hacl_Curve25519_51.o.fetch
  let sha2 ← Hacl_Hash_SHA2.o.fetch
  let name := nameToStaticLib "l4hacl"
  buildStaticLib (pkg.staticLibDir / name) #[shim, ed, curve, sha2]

/-- Build the deliberately small POSIX `pread` host adapter used only by the
    native IBK2 range-read probe. The pure planner/decoder remains in Lean;
    this C object is not part of the WASM closure. -/
target block_pread.o pkg : FilePath :=
  buildHaclO pkg "block_pread" (pkg.dir / "ffi" / "block_pread.c")

extern_lib libl4blockhost pkg := do
  let pread ← block_pread.o.fetch
  let name := nameToStaticLib "l4blockhost"
  buildStaticLib (pkg.staticLibDir / name) #[pread]

@[default_target] lean_lib L4Factoidal

-- The W3C harness's shared modules. They live in a lib rather than
-- hanging off an executable root because `Harness.Main` imports them
-- and Lake only builds modules a lib claims. NOT part of the verified
-- library: these do file I/O and print scores. The probes
-- (`Harness.TurtleProbe`, `Harness.CanonProbe`) stay executable roots.
@[default_target] lean_lib Harness where globs :=
  #[`Harness.Common, `Harness.Manifest, `Harness.Compare, `Harness.ProtocolRun, `Harness.Run, `Harness.HarnessTests,
    `Harness.NativeHasher,
    `Harness.PosixRangeIO, `Harness.CompactedEpoch, `Harness.GenerationPointer, `Harness.ShardMerkleMaterialize, `Harness.ShardMerkleProfile, `Harness.ShardPublish,
    `Harness.IndexedBlockV3Materialize]

-- The WebAssembly export surface: the JSON string-in / string-out ABI
-- (Wasm/Abi.lean) and the `@[export]` C symbols (Wasm/Exports.lean).
-- `lake build` compiles it, so the ABI is type-checked on every build
-- even when no wasm toolchain is present.
@[default_target] lean_lib l4wasm where
  srcDir := "."
  roots := #[`Wasm.Abi, `Wasm.Exports, `Wasm.Dispatch,
             `Wasm.Ops.Support, `Wasm.Ops.Parse, `Wasm.Ops.Query,
             `Wasm.Ops.Reason, `Wasm.Ops.Canon, `Wasm.Ops.CL,
             `Wasm.Ops.Block,
             `Wasm.Ops.Store,
             `Wasm.Ops.StoreHandles,
             `Wasm.Ops.Proof,
             `Wasm.Ops.Handles,
             `Wasm.Ops.Pack]

-- Runs the XML parser over real W3C XML Conformance Test Suite files:
-- reads paths from stdin, prints WF / NWF per file. See
-- L4Factoidal/XML/ConfProbe.lean for what a verdict does and does not
-- mean.
@[default_target] lean_exe «xmlconf-probe» where root := `L4Factoidal.XML.ConfProbe

-- Real-corpus probe for RDFC-1.0 (the W3C rdf-canon suite). Not part of
-- the verified library: it does file I/O and prints scores.
@[default_target] lean_exe «l4rdfc-probe» where root := `Harness.CanonProbe

-- Real-corpus probe for the Turtle / TriG parsers (Harness/TurtleProbe.lean).
-- Separate from the library so the library stays specification-only, per the
-- spec/pragmatics split recorded in PORT_NOTES.md.
@[default_target] lean_exe «l4turtle-probe» where root := `Harness.TurtleProbe

-- Real-corpus probe for JSON-LD 1.1 expansion + toRdf (the W3C
-- json-ld-api toRdf manifest). Same spec/pragmatics split: it reads the
-- manifest and fixtures from disk and prints scores, so it lives outside
-- the library.
@[default_target] lean_exe «l4jsonld-probe» where root := `Harness.JsonLdProbe

-- Real-corpus probe for the REST of the W3C json-ld-api suite: the
-- expand, compact, flatten, fromRdf and html manifests (Harness/
-- JsonLdApiProbe.lean). Same spec/pragmatics split as l4jsonld-probe,
-- which keeps toRdf and is left alone. Run the built binary from the
-- REPOSITORY ROOT: it resolves the corpus relative to the CWD.
@[default_target] lean_exe «l4jsonld-api» where root := `Harness.JsonLdApiProbe

-- Real-corpus runner for the W3C json-ld-framing suite (Harness/
-- JsonLdFrameRun.lean), the manifest neither probe above covers. Run
-- the built binary from the REPOSITORY ROOT.
@[default_target] lean_exe «l4jsonld-frame» where root := `Harness.JsonLdFrameRun

-- Corpus census for the W3C OWL 2 test catalogs (Harness/OwlProbe.lean):
-- reads the RDF/XML catalogs with the Lean XML parser and reports, with
-- denominators, how many test cases carry a serialisation the Lean tree
-- can turn into triples. Not part of the verified library: file I/O and
-- printed scores.
@[default_target] lean_exe «l4owl-probe» where root := `Harness.OwlProbe

-- Native driver for the same ABI, so it can be exercised without wasm.
@[default_target] lean_exe «l4wasm-cli» where
  srcDir := "."
  root := `Wasm.Main

-- `l4factoidal` — the real command-line interface (issue #466 ladder):
-- named verbs and flags over the SAME `Wasm/Ops/*.lean` functions
-- `l4wasm-cli`/the wasm build call, for people and scripts that do not
-- want to know the dispatch ABI. `Wasm/Cli.lean` is thin argument
-- parsing + JSON-envelope decoding; no RDF/SPARQL/OWL/CL logic lives
-- here. `l4wasm-cli` above is unchanged and stays the ABI smoke
-- driver `Wasm/native-smoke.sh` pins.
@[default_target] lean_exe «l4factoidal» where
  srcDir := "."
  root := `Wasm.Cli

-- Native executable for the first RDF block MVP. It exercises the total
-- `Storage.BlockMvp.scan` path over a small in-memory graph; it does not claim
-- protocol, persistence, or W3C conformance coverage.
@[default_target] lean_exe «l4block-mvp» where root := `Harness.BlockMvp

-- Real-Turtle corpus probe for the indexed block. It is outside the library
-- because file I/O and timing/corpus measurements are executable-edge concerns.
@[default_target] lean_exe «l4block-corpus» where root := `Harness.BlockCorpus

-- Transitional persistent-file vertical: pack supported Turtle as framed BLK0
-- then decode it into the indexed query block without reparsing Turtle.
@[default_target] lean_exe «l4block-pack» where root := `Harness.BlockPack
@[default_target] lean_exe «l4block-file-query» where root := `Harness.BlockFileQuery

-- Direct shared-dictionary/ID-row persistence and query vertical.
@[default_target] lean_exe «l4block-id-pack» where root := `Harness.IndexedBlockPack
@[default_target] lean_exe «l4block-id-file-query» where root := `Harness.IndexedBlockFileQuery
@[default_target] lean_exe «l4block-id-diff» where root := `Harness.IndexedBlockDiff
@[default_target] lean_exe «l4block-id-v2-diff» where root := `Harness.IndexedBlockV2Diff
@[default_target] lean_exe «l4block-id-v2-segment» where root := `Harness.IndexedBlockV2Segment
@[default_target] lean_exe «l4block-id-v2-pack» where root := `Harness.IndexedBlockV2Pack
@[default_target] lean_exe «l4block-id-v2-file-query» where root := `Harness.IndexedBlockV2FileQuery
@[default_target] lean_exe «l4block-id-v2-range-plan» where root := `Harness.IndexedBlockV2RangePlan
@[default_target] lean_exe «l4block-id-v2-pread» where root := `Harness.IndexedBlockV2Pread
@[default_target] lean_exe «l4block-id-v3-convert» where root := `Harness.IndexedBlockV3Convert
@[default_target] lean_exe «l4block-id-v3-merkle-scan» where root := `Harness.IndexedBlockV3MerkleScan
@[default_target] lean_exe «l4block-id-v3-query» where root := `Harness.IndexedBlockV3Query
@[default_target] lean_exe «l4block-paged-dictionary-probe» where root := `Harness.PagedDictionaryProbe
@[default_target] lean_exe «l4block-shard-merkle-pread» where root := `Harness.ShardMerklePread
@[default_target] lean_exe «l4block-shard-merkle-scan» where root := `Harness.ShardMerkleScan
@[default_target] lean_exe «l4block-shard-merkle-query» where root := `Harness.ShardMerkleQuery
@[default_target] lean_exe «l4block-shard-merkle-session» where root := `Harness.ShardMerkleSession
@[default_target] lean_exe «l4block-delta-log» where root := `Harness.DeltaLogTool
@[default_target] lean_exe «l4block-shard-compact» where root := `Harness.ShardDeltaCompact
@[default_target] lean_exe «l4block-shard-activate» where root := `Harness.ShardActivate
@[default_target] lean_exe «l4block-predicate-shards» where root := `Harness.PredicateBlocksProbe
@[default_target] lean_exe «l4block-predicate-query» where root := `Harness.PredicateBlocksQuery
@[default_target] lean_exe «l4block-shard-pack» where root := `Harness.PredicateShardPack
-- SPARQL over an activated SBM7 generation of IBK4 quad blocks: the quad
-- sibling of `l4block-id-v3-query`, which reads IBK3 generations and refuses
-- SBM7 by layout. `GRAPH <iri>`, `GRAPH ?g`, `FROM` / `FROM NAMED` and
-- default-graph patterns all run against the dataset the blocks denote.
@[default_target] lean_exe «l4block-quad-query» where root := `Harness.QuadQuery

-- Write an IBK4 generation's quads back out as N-Quads, so the SAME corpus
-- can be packed again under a changed format and the two compared.
@[default_target] lean_exe «l4block-quad-dump» where root := `Harness.QuadDump
@[default_target] lean_exe «l4block-literal-gram» where root := `Harness.LiteralGramProbe

-- The row-identity gate for the LGI1 literal search index, driven through
-- `storeHandleQuery` — the operation a host calls. It opens one handle with
-- the sidecars and one without, and compares the two answer envelopes.
@[default_target] lean_exe «l4block-literal-gate» where
  srcDir := "."
  root := `Harness.LiteralGate
@[default_target] lean_exe «l4block-shard-query» where root := `Harness.ShardManifestQuery
@[default_target] lean_exe «l4block-shard-session» where root := `Harness.ShardManifestSession

-- The MANIFEST-DRIVEN W3C conformance runner (issue #466, ladder rung
-- 3). Reads the real `manifest.ttl` files off disk with the Lean
-- Turtle parser and scores the Lean engine in the same score-line
-- grammar `bin/w3c-runner/w3c_runner.ml` uses, so the two trees'
-- numbers are directly comparable. Design:
-- docs/designissues/2026-08-22-lean4-w3c-harness.md
--   lake exe l4w3c ../../third_party/testing/w3c/rdf/rdf11/rdf-turtle/manifest.ttl
-- `Harness.HarnessTests` is imported so its `#guard`s run in the build.
@[default_target] lean_exe l4w3c where root := `Harness.Main

-- Real-corpus probe for the RDF/XML parser (Harness/RdfXmlProbe.lean).
-- Directory-driven, not manifest-driven, so it does not depend on the
-- Turtle parser. Separate from the library so the library stays
-- specification-only, per the spec/pragmatics split in PORT_NOTES.md.
@[default_target] lean_exe «l4rdfxml-probe» where root := `Harness.RdfXmlProbe

-- Reader-level probe over the vendored W3C csvw corpus. Named a
-- PROBE, not a conformance runner, because it measures whether the
-- dialect reader reads each .csv cleanly -- not whether the
-- conversion matches the suite's expected .ttl.
@[default_target] lean_exe «l4csvw-probe» where root := `Harness.CsvwProbe

-- A REAL csv2rdf conformance runner: full pipeline, compared against
-- the suite's expected .ttl by graph isomorphism. Restricted to the
-- no-metadata subset; every skip is reported with its reason.
@[default_target] lean_exe «l4csvw-rdf» where root := `Harness.CsvwRdfRun

@[default_target] lean_exe «l4csvw-json» where root := `Harness.CsvwJsonRun

@[default_target] lean_exe «l4jsonschema» where root := `Harness.JsonSchemaRun

@[default_target] lean_exe «l4mathml» where root := `Harness.MathMLRun

@[default_target] lean_exe «l4xmlconf» where root := `Harness.XmlConfRun

@[default_target] lean_exe «l4shex» where root := `Harness.ShExRun

-- ISO Schematron conformance runner: Schematron/FromXml reads the
-- .sch, XPath/Mini supplies Validate's `select` and `evalTest`.
@[default_target] lean_exe «l4schematron» where root := `Harness.SchematronRun

-- RML-Core test cases: mapping.ttl + source + output.nq, compared by
-- DATASET isomorphism (Harness/RmlRun.lean).
@[default_target] lean_exe «l4rml» where root := `Harness.RmlRun

-- RIF Core conformance: syntax and entailment cases from the W3C
-- suite (Harness/RifRun.lean).
@[default_target] lean_exe «l4rif» where root := `Harness.RifRun

-- XSLT 1.0 conformance over the vendored w3c/xslt30-test subset:
-- XSLT/Transform runs the stylesheet, the result tree is serialised
-- and compared with the suite's own assert-xml file (Harness/XsltRun.lean).
@[default_target] lean_exe «l4xslt» where root := `Harness.XsltRun

-- ShExC differential: every schemas/*.shex read by ShEx/Compact and
-- compared with the ShExJ twin the same directory ships
-- (Harness/ShExCRun.lean).
@[default_target] lean_exe «l4shexc» where root := `Harness.ShExCRun

-- GRDDL conformance over the vendored W3C GRDDL suite: GRDDL/Discovery
-- finds the transformations, XSLT/Transform runs them, RdfXml reads the
-- output, and graphs are compared by isomorphism (Harness/GrddlRun.lean).
@[default_target] lean_exe «l4grddl» where root := `Harness.GrddlRun

-- Real-corpus probe for the SPARQL query parser: walks the W3C sparql11
-- .rq files without a manifest, using the suites' naming convention.
-- See L4Factoidal/SPARQL/Parser.lean and Harness/SparqlSyntaxProbe.lean.
@[default_target] lean_exe «l4sparql-probe» where root := `Harness.SparqlSyntaxProbe

-- Verifiable Credentials Data Integrity (eddsa-rdfc-2022) + did:key
-- probe (Harness/VcProbe.lean): the RFC 8032 Ed25519 vectors through
-- the HACL* extern (which `#guard` cannot evaluate), the did:key
-- vectors `bin/did-runner` reads, the eddsa-rdfc-2022 roundtrip
-- `bin/vc-runner --crypto` runs, and the W3C vc-di-eddsa specification
-- test vectors end to end (JSON-LD -> RDFC-1.0 -> SHA-256 -> Ed25519).
@[default_target] lean_exe «l4vc-probe» where root := `Harness.VcProbe

-- SHACL Core probe over the W3C shacl test suite (Harness/ShaclProbe.lean).
@[default_target] lean_exe «l4shacl» where root := `Harness.ShaclProbe

-- SHACL 1.2 rules suite (Harness/ShaclRulesRun.lean, L4Factoidal/SHACL/Rules.lean).
@[default_target] lean_exe «l4shacl-rules» where root := `Harness.ShaclRulesRun

-- SHACL 1.2 node-expr suite (Harness/ShaclNodeExprRun.lean, L4Factoidal/SHACL/NodeExpr.lean).
@[default_target] lean_exe «l4shacl-nodeexpr» where root := `Harness.ShaclNodeExprRun

-- Property-based probe: seeded generators + algebra/round-trip invariants
-- (Harness/PropProbe.lean, L4Factoidal/Testing/).
@[default_target] lean_exe «l4prop» where root := `Harness.PropProbe

-- Differential harness: the same (data, query) through the F* native
-- binary and the Lean evaluator (Harness/Differential.lean).
@[default_target] lean_exe «l4diff» where root := `Harness.Differential

-- HDT v1 container reader over the vendored hdt-cpp fixtures
-- (Harness/HdtProbe.lean). Directory-driven, not manifest-driven: the
-- HDT format has no W3C test suite, so the corpus is the two files in
-- third_party/testing/hdt/ with their published SHA-256 digests. Run
-- from the REPOSITORY ROOT.
@[default_target] lean_exe «l4hdt» where root := `Harness.HdtProbe

-- Delta (semi-naive) RDFS closure against the naive one: agreement and
-- wall-clock, on the subclass-chain shape issue #340 is about
-- (Harness/RdfsSemiNaive.lean). The module exists for speed, so this
-- measures speed as well as agreement.
@[default_target] lean_exe «l4rdfs-semi» where root := `Harness.RdfsSemiNaive
