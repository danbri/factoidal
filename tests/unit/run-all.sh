#!/bin/bash
# tests/unit/run-all.sh — builds and runs every *.ml test file under
# tests/unit/ against the F*-extracted modules in
# formal/fstar/ocaml-output/.
#
# This suite is distinct from the W3C conformance runner
# (formal/fstar/ocaml-output/w3c_runner) and from the ad-hoc scripts
# in tests/local/. It is intentionally fast: every assertion runs
# natively against the already-extracted .cmx artifacts.
#
# Usage:
#   ./run-all.sh                  # run everything
#   ./run-all.sh utf8_roundtrip   # run a single test (no .ml suffix)
#
# Exit code is 0 iff every assertion in every test file matches its
# expected outcome (PASS or documented expected-FAIL).
#
# Rule anchors:
#   * CLAUDE.md rule #14 — we never use `|| true` to swallow failures;
#     we capture exit codes explicitly so the summary is truthful.
#   * CLAUDE.md rule #16 — we never truncate runner output with tail/head;
#     every per-assertion line is streamed, and the summary goes AT THE
#     END after the full run.
#   * CLAUDE.md rule #25 — the final summary line spells out
#     "N pass, N fail" in words, not a cryptic ratio.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OCAML_OUT="$REPO_ROOT/formal/fstar/ocaml-output"
BUILD_DIR="$SCRIPT_DIR/_build"

if [[ ! -d "$OCAML_OUT" ]]; then
  echo "ERROR: $OCAML_OUT does not exist — run" >&2
  echo "       'cd formal/fstar && ./build-ocaml.sh extract compile' first." >&2
  exit 2
fi

# Start from a clean scratch dir. Stale objects here (e.g. a $name.cmi from
# an earlier run against a different committed .cmx set) are a classic source
# of spurious "inconsistent assumptions" link errors, so we wipe rather than
# reuse.
rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR"

# COMMON_MODULES is the canonical link order taken verbatim from
# formal/fstar/build-ocaml.sh's $COMMON_MODULES (its native-binary
# compile step). Keep this list byte-for-byte in step with that one:
# regenerate with
#   sed -n '/^  COMMON_MODULES="/,/service_wrap_http.ml"/p' \
#     ../../formal/fstar/build-ocaml.sh | grep -oE '[A-Za-z0-9_]+\.ml' \
#     | sed 's/\.ml$//'
# Link order is a valid topological order for the full module set; any
# subsequence of it (after the present-.cmx filter below) is therefore
# still correctly ordered. Do NOT hand-curate a shorter list here — that
# drift (missing Math_Matrix/OWL_DirectMapping_Filter/Parser_OWLFunctional/
# RDF_Turtle_Serialize/... and wrong Parser_Turtle/SPARQL11_IRI_Resolve
# positions) is exactly what broke every link with "inconsistent
# assumptions over interface" / "Cannot find file *.cmx" (#82).
COMMON_MODULES=(
  Util_Log
  RDF_Format
  RDF_Vocabulary
  RDF_Term
  RDF_Triple
  RDF_Indexed
  RDF_Graph
  RDF_Vocabulary_Axioms
  RDFS_Closure
  OWL_Closure
  RDF_Graph_Executable
  RDF_List_Helpers
  RDF_Bytes
  RDF_Store_Loader
  Parquet_Footer
  OWL_Vocabulary
  OWL_DirectMapping_Filter
  Tableau
  Tableau_Refute
  Parser_FastString
  RDF_IRI
  SPARQL11_IRI_Resolve
  Parser_IRI
  RDF_NQuads_Serialize
  Parser_Combinators
  Parser_TurtleScanner
  Parser_NTriples
  Parser_Turtle
  HDT_Container
  HDT_Dictionary
  HDT_Triples
  RDF_Geo_Types
  RDF_Geo_BBox
  Parser_WKT
  RDF_Geo_Topology
  RDF_Geo_Functions
  Parser_OWLFunctional
  RDF_Turtle_Serialize
  Parser_NQuads
  Parser_TriG
  Parser_XML
  XML_Wellformedness
  XML_Namespaces
  Parser_XPath
  XPath_Eval
  XSLT_Transform
  Schematron_Validate
  Parser_RDFXML
  Math_Expr
  Math_Subst
  Math_Diff
  Math_Simplify
  Math_Matrix
  MathML_Content
  Math_Series
  MathML_Present
  Parser_SRX
  Parser_CSVResults
  Parser_JSONResults
  SPARQL_JSON_Escape
  Parser_JSON
  JSONLD_Loader
  JSONLD_Context
  JSONLD_Expand
  Parser_JSONLD
  JSONLD_FromRdf
  JSONSchema_Validate
  SPARQL_Eval_TimeBudget
  SPARQL_Eval_Limits
  SPARQL_HTTP_Response
  SPARQL_HTTP_Timing
  SPARQL_HTTP_BackendInfo
  SPARQL_HTTP_QueriesIndex
  SPARQL_HTTP_StaticFiles
  SPARQL_HTTP_Admin
  SPARQL_HTTP_Routes
  Parser_Ballyhoo
  Parser_BallyhooBloom
  Parser_BallyhooHDT
  Parser_BallyhooHDTQ
  Parser_BallyhooCOTTAS
  RDF_CottasStore_ColumnSeq
  RDF_CottasStore_PageCache
  RDF_CottasStore_OnDiskIndex
  RDF_CottasStore_DictWriter
  RDF_CottasStore_PresenceBitmap
  RDF_CottasStore_PresenceWriter
  RDF_CottasStore_CompoundPresenceBitmap
  RDF_CottasStore_CompoundPresenceWriter
  RDF_CottasStore_OffsetsWriter
  RDF_CottasStore_BaseWriter
  RDF_CottasStore_LazyDict
  RDF_CottasStore_LazyDictRegistry
  RDF_Store_LazyTermCache
  RDF_Store_HDTTermCacheRegistry
  RDF_Store_Columnar_OffsetIndex
  RDF_Store_Columnar_DeltaLog
  SPARQL_Plan_Pruning
  SPARQL_Plan_Estimate
  SPARQL_Plan_Loader
  SPARQL_Plan_AccessPath
  RDF_CottasStore
  RDF_CottasStore_OnDiskRuntime
  RDF_CottasInMem
  fstar_pure_hashes
  RDF_Dataset_Graphs
  RDF_Canonical
  RDF_Canonical_Manifest
  service_wrap_hook
  SPARQL_FullText
  SPARQL11_Algebra
  XSD_Datatypes
  XForms_Bind
  RDF_Pretty
  OWL_QueryRewrite
  OWL_QueryEval
  OWL_Tests_Manifest
  RIF_Core_Syntax
  Parser_RIFXML
  RIF_Core_Translation
  RIF_Core_Builtins
  RIF_Core_Conformance
  RIF_Core_Eval
  RIF_Core_Tests
  SPARQL11_Parser
  SHACL_Validation
  ShEx_Schema
  Parser_ShExC
  ShEx_SchemaEq
  ShEx_Validation
  VC_Credential
  VC_Multibase
  DID_Key
  fstar_hacl_crypto
  VC_DataIntegrity
  RML_Mapping
  RML_Sources
  RML_Eval
  CSVW_Metadata
  CSVW_URITemplate
  CSVW_Conversion
  RDF_Store_Columnar_DeltaMerge
  SPARQL_Plan_Streamable
  RDF_Store_Capabilities
  RDF_Store_Capabilities_Cottas
  RDF_Store_Capabilities_Delta
  RML_VirtualSource
  SPARQL11_Store
  RDF_Store_Combine
  RDF_Dataset_Merge
  SPARQL_Protocol
  SPARQL_HTTP_RunQuery
  SPARQL_Update_Sandbox
  SPARQL_Update_Analysis
  SPARQL_Diagnostics
  SPARQL_Explain
  SPARQL_Query_Analysis
  SPARQL_Plan_Explain
  SPARQL_HTTP
  SPARQL_HTTP_Client
  SPARQL_Protocol_Client
  SPARQL_ServiceDescription
  SPARQL_GraphStore
  SPARQL_Service_Wrap
  service_wrap_http
)

# Per-test dependency-closure linking.
#
# We do NOT link the whole module universe into every test. Two reasons:
#   1. The committed ocaml-output .cmx are snapshotted across several build
#      epochs (git shows SPARQL11_Algebra.cmx and RML_Eval.cmx landing in
#      different commits). A partial .cmx commit can leave a *dependent*
#      (RML_Eval) referencing an older *implementation* digest of a
#      dependency (SPARQL11_Algebra) than the one now on disk. Linking both
#      into one binary then dies with "make inconsistent assumptions over
#      implementation SPARQL11_Algebra" — even for a test (geosparql) that
#      needs neither. Linking only each test's own transitive closure keeps
#      such stale, unrelated modules out of the link line.
#   2. Some canonical modules (Math_* / MathML_* / XForms_Bind / VC_* / the
#      XSLT/Schematron consumers) have no committed .cmx in this checkout.
#      A test that genuinely needs one fails at build with an honest
#      "Unbound module"; a test that does not is unaffected.
#
# The closure is computed with ocamlfind ocamldep over the committed .ml
# sources, then ordered by the canonical COMMON_MODULES order above (a valid
# global topological order, so any subsequence is correctly ordered too).
# We never recompile into $OCAML_OUT (hazard #8): committed .cmx are linked
# read-only; test objects and all scratch land in $BUILD_DIR.
PARQUET_STUB_OBJ="$OCAML_OUT/parquet_zstd_stubs.o"

# Which canonical modules actually have a committed .cmx on disk.
PRESENT_MODULES=()
ABSENT_MODULES=()
for m in "${COMMON_MODULES[@]}"; do
  if [[ -f "$OCAML_OUT/$m.cmx" ]]; then
    PRESENT_MODULES+=("$m")
  else
    ABSENT_MODULES+=("$m")
  fi
done
if [[ ${#ABSENT_MODULES[@]} -gt 0 ]]; then
  echo "note: ${#ABSENT_MODULES[@]} canonical module(s) have no committed .cmx in this checkout;" >&2
  echo "      a test whose closure needs one will fail with an honest Unbound-module build error:" >&2
  echo "      ${ABSENT_MODULES[*]}" >&2
  echo >&2
fi

# Canonical order + native dependency graph, materialised in $BUILD_DIR for
# the closure helper. ocamldep is run over the present .ml sources only.
printf '%s\n' "${COMMON_MODULES[@]}" > "$BUILD_DIR/canon.txt"
ocamlfind ocamldep -native -I "$OCAML_OUT" "$OCAML_OUT"/*.ml \
  > "$BUILD_DIR/dep.graph" 2>/dev/null

# closure.py: given a test .ml's ocamldep line(s) on stdin, print the
# canonical-ordered transitive closure of ocaml-output modules it needs.
cat > "$BUILD_DIR/closure.py" <<'PYCLOSURE'
import sys, os
build = sys.argv[1]
# graph: module -> set(deps)
graph = {}
raw = open(os.path.join(build, "dep.graph")).read().replace("\\\n", " ")
for line in raw.splitlines():
    if ':' not in line:
        continue
    lhs, rhs = line.split(':', 1)
    lm = os.path.basename(lhs.strip())
    if not lm.endswith('.cmx'):
        continue
    lm = lm[:-4]
    graph.setdefault(lm, set()).update(
        os.path.basename(x)[:-4] for x in rhs.split() if x.endswith('.cmx'))
# test's direct deps come in on stdin (its own ocamldep output)
direct = set()
tin = sys.stdin.read().replace("\\\n", " ")
for line in tin.splitlines():
    if ':' in line:
        for x in line.split(':', 1)[1].split():
            if x.endswith('.cmx'):
                direct.add(os.path.basename(x)[:-4])
seen = set(); stack = list(direct)
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    stack.extend(graph.get(m, ()))
canon = [l.strip() for l in open(os.path.join(build, "canon.txt")) if l.strip()]
print(' '.join(m for m in canon if m in seen))
PYCLOSURE

# Detect libzstd on the host so we can pass -cclib -lzstd if present.
# If zstd is unavailable we still try, since the parquet_zstd_stubs
# object contains only a thin wrapper; the symbol is referenced but
# not executed from our tests.
ZSTD_LIB_FLAGS=()
for dir in /opt/homebrew/lib /opt/homebrew/opt/zstd/lib \
           /usr/local/lib /usr/lib /usr/lib/x86_64-linux-gnu \
           /usr/lib/aarch64-linux-gnu; do
  if [[ -f "$dir/libzstd.a" || -f "$dir/libzstd.so" || -f "$dir/libzstd.dylib" ]]; then
    ZSTD_LIB_FLAGS=(-cclib "-L$dir" -cclib -lzstd)
    break
  fi
done

# Collect test files. Optional filter arg.
FILTER="${1:-}"
shopt -s nullglob
ALL_TESTS=()
for ml in "$SCRIPT_DIR"/*.ml; do
  name="$(basename "$ml" .ml)"
  if [[ -z "$FILTER" || "$name" == "$FILTER" ]]; then
    ALL_TESTS+=("$name")
  fi
done
shopt -u nullglob

if [[ ${#ALL_TESTS[@]} -eq 0 ]]; then
  echo "No unit tests matched filter '${FILTER}'." >&2
  exit 2
fi

TOTAL_FILES=${#ALL_TESTS[@]}
PASS_FILES=0
FAIL_FILES=0

echo "tests/unit runner: ${TOTAL_FILES} file(s) under $SCRIPT_DIR"
echo "                   ocaml-output at $OCAML_OUT"
echo

for name in "${ALL_TESTS[@]}"; do
  ml_file="$SCRIPT_DIR/$name.ml"
  bin_file="$BUILD_DIR/$name"

  echo "--- $name ---"

  # Compute this test's transitive module closure (its own ocamldep piped
  # through closure.py against the precomputed graph), then map to present
  # .cmx paths in canonical order. Modules whose .cmx is absent are dropped
  # here so the link line only carries files that exist; the resulting
  # "Unbound module" at compile is the honest signal that the test needs a
  # module not committed to this checkout.
  CLOSURE_MODS=$(ocamlfind ocamldep -native -I "$OCAML_OUT" "$ml_file" 2>/dev/null \
    | python3 "$BUILD_DIR/closure.py" "$BUILD_DIR")
  TEST_CMX=()
  for m in $CLOSURE_MODS; do
    [[ -f "$OCAML_OUT/$m.cmx" ]] && TEST_CMX+=("$OCAML_OUT/$m.cmx")
  done

  # Compile. We use the same ocamlfind + package list as build-ocaml.sh's
  # native binaries. -I $OCAML_OUT so .cmi files are discoverable. Test
  # objects are written into $BUILD_DIR (never $OCAML_OUT): we copy the
  # source in and compile from there so the emitted .cmi/.cmx/.o land beside
  # the binary, leaving both tests/unit/ and ocaml-output/ untouched.
  cp "$ml_file" "$BUILD_DIR/$name.ml"
  BUILD_RC=0
  BUILD_OUT=$(cd "$BUILD_DIR" && ocamlfind ocamlopt \
    -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp \
    -linkpkg -w -8-14-26 \
    -I "$OCAML_OUT" \
    "${TEST_CMX[@]}" \
    "$PARQUET_STUB_OBJ" \
    "${ZSTD_LIB_FLAGS[@]}" \
    "$BUILD_DIR/$name.ml" \
    -o "$bin_file" 2>&1) || BUILD_RC=$?

  if [[ $BUILD_RC -ne 0 ]]; then
    echo "  BUILD FAILED (rc=$BUILD_RC)"
    echo "$BUILD_OUT" | sed 's/^/    /'
    FAIL_FILES=$((FAIL_FILES + 1))
    echo "$name: FAIL (build)"
    echo
    continue
  fi

  # Run. The test binary itself exits 0 on clean, 1 on any unexpected
  # failure. Stream its output directly — no tail/head truncation.
  RUN_RC=0
  "$bin_file" || RUN_RC=$?

  if [[ $RUN_RC -eq 0 ]]; then
    PASS_FILES=$((PASS_FILES + 1))
    echo "$name: PASS"
  else
    FAIL_FILES=$((FAIL_FILES + 1))
    echo "$name: FAIL (rc=$RUN_RC)"
  fi
  echo
done

echo "============================================================"
echo "tests/unit summary: ${PASS_FILES} file(s) pass, ${FAIL_FILES} file(s) fail (out of ${TOTAL_FILES})"

if [[ $FAIL_FILES -eq 0 ]]; then
  exit 0
else
  exit 1
fi
