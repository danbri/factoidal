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

/-! ## HACL* Ed25519 (the Lean tree's single `@[extern]` family)

`L4Factoidal/Crypto/Ed25519.lean` declares three `opaque`s with
`@[extern "l4_hacl_ed25519_*"]`. They are realised by
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

@[default_target] lean_lib L4Factoidal

-- The W3C harness's shared modules. They live in a lib rather than
-- hanging off an executable root because `Harness.Main` imports them
-- and Lake only builds modules a lib claims. NOT part of the verified
-- library: these do file I/O and print scores. The probes
-- (`Harness.TurtleProbe`, `Harness.CanonProbe`) stay executable roots.
@[default_target] lean_lib Harness where globs :=
  #[`Harness.Common, `Harness.Manifest, `Harness.Compare, `Harness.ProtocolRun, `Harness.Run, `Harness.HarnessTests]

-- The WebAssembly export surface: the JSON string-in / string-out ABI
-- (Wasm/Abi.lean) and the `@[export]` C symbols (Wasm/Exports.lean).
-- `lake build` compiles it, so the ABI is type-checked on every build
-- even when no wasm toolchain is present.
@[default_target] lean_lib l4wasm where
  srcDir := "."
  roots := #[`Wasm.Abi, `Wasm.Exports]

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

-- Property-based probe: seeded generators + algebra/round-trip invariants
-- (Harness/PropProbe.lean, L4Factoidal/Testing/).
@[default_target] lean_exe «l4prop» where root := `Harness.PropProbe

-- Differential harness: the same (data, query) through the F* native
-- binary and the Lean evaluator (Harness/Differential.lean).
@[default_target] lean_exe «l4diff» where root := `Harness.Differential
