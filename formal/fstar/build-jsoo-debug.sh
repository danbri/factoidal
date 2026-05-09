#!/bin/bash
# Build a debug js_of_ocaml bundle of the factoidal CLI, with -g on
# ocamlc and --pretty --debug-info --no-inline --source-map on
# js_of_ocaml. Output:
#
#   docs/fstar-extracted/factoidal.debug.js
#   docs/fstar-extracted/factoidal.debug.map
#
# js_of_ocaml derives the source-map filename from the .byte input
# (factoidal.debug.byte → factoidal.debug.map), NOT from the -o
# output, so the .map sits next to the .js without a .js.map suffix.
# The bundle references it via //# sourceMappingURL=factoidal.debug.map.
#
# The production bundle (docs/fstar-extracted/factoidal.js) is NOT
# touched. The public demo (factoidal-sparql-client.js) opts into the
# debug bundle when ?jsoo-debug=1 is set in the URL — see #240, #243.
#
# Prereqs:
# - F* extraction must be present in formal/fstar/ocaml-output/
#   (run ./build-ocaml.sh extract first, or use a fresh tree where
#    extracted .ml files are committed).
# - js_of_ocaml + zarith_stubs_js installed in the active opam switch.
#
# Usage:
#   eval $(opam env)
#   cd formal/fstar
#   ./build-jsoo-debug.sh

set -euo pipefail
cd "$(dirname "$0")"

OUTDIR=ocaml-output
if [[ ! -d "$OUTDIR" ]]; then
  echo "error: $OUTDIR/ is missing. Run './build-ocaml.sh extract' first." >&2
  exit 1
fi

OUT_JS="../../../docs/fstar-extracted/factoidal.debug.js"

cd "$OUTDIR"

FSTAR_MODULES=(
  Util_Log.ml
  RDF_Format.ml RDF_Graph_Executable.ml RDF_List_Helpers.ml RDF_Bytes.ml RDF_Store_Loader.ml RDF_NQuads_Serialize.ml Parquet_Footer.ml OWL_Vocabulary.ml Tableau.ml
  Parser_FastString.ml Parser_IRI.ml
  Parser_Combinators.ml Parser_TurtleScanner.ml Parser_NTriples.ml Parser_Turtle.ml
  Parser_NQuads.ml Parser_TriG.ml Parser_XML.ml Parser_RDFXML.ml
  Parser_SRX.ml Parser_CSVResults.ml Parser_JSONResults.ml
  SPARQL_JSON_Escape.ml
  SPARQL_Eval_TimeBudget.ml
  SPARQL_Eval_Limits.ml
  SPARQL_HTTP_Response.ml
  SPARQL_HTTP_BackendInfo.ml
  SPARQL_HTTP_QueriesIndex.ml
  SPARQL_HTTP_StaticFiles.ml
  SPARQL_HTTP_Admin.ml
  Parser_Ballyhoo.ml Parser_BallyhooBloom.ml
  Parser_BallyhooHDT.ml Parser_BallyhooHDTQ.ml Parser_BallyhooCOTTAS.ml
  RDF_CottasStore_ColumnSeq.ml
  RDF_CottasStore_PageCache.ml
  RDF_CottasStore_OnDiskIndex.ml
  RDF_CottasStore_DictWriter.ml
  RDF_CottasStore_PresenceBitmap.ml
  RDF_CottasStore_PresenceWriter.ml
  RDF_CottasStore_CompoundPresenceBitmap.ml
  RDF_CottasStore_CompoundPresenceWriter.ml
  RDF_CottasStore_OffsetsWriter.ml
  RDF_Store_Columnar_OffsetIndex.ml
  SPARQL_Plan_Pruning.ml
  SPARQL_Plan_Estimate.ml
  SPARQL_Plan_Loader.ml
  SPARQL_Plan_AccessPath.ml
  RDF_CottasStore.ml
  RDF_CottasInMem.ml
  fstar_pure_hashes.ml
  RDF_Canonical.ml
  RDF_Canonical_Manifest.ml
  SPARQL11_Algebra.ml RDF_Pretty.ml OWL_QueryRewrite.ml OWL_QueryEval.ml OWL_Tests_Manifest.ml RIF_Core_Syntax.ml Parser_RIFXML.ml RIF_Core_Translation.ml RIF_Core_Eval.ml RIF_Core_Tests.ml SHACL_Validation.ml SPARQL11_Parser.ml SPARQL11_Store.ml RDF_Store_Combine.ml SPARQL_Protocol.ml
  SPARQL_Update_Sandbox.ml
  SPARQL_Update_Analysis.ml
  SPARQL_Diagnostics.ml
  SPARQL_Explain.ml
  SPARQL_Query_Analysis.ml
  SPARQL_Plan_Explain.ml
  SPARQL_HTTP.ml SPARQL_HTTP_Client.ml SPARQL_ServiceDescription.ml SPARQL_GraphStore.ml
)

echo "--- ocamlc factoidal.byte (-g, debug) ---"
cp ../../../bin/factoidal-serve/factoidal_serve_jsoo.ml factoidal_serve.ml
RC=0
ocamlfind ocamlc -g -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
  -custom parquet_zstd_stubs_jsoo.c \
  -I ../../../bin/factoidal-explain \
  "${FSTAR_MODULES[@]}" \
  ../../../bin/factoidal-explain/factoidal_explain.ml \
  factoidal_serve.ml \
  ../../../bin/factoidal-cli/factoidal_cli.ml \
  -o factoidal.debug.byte || RC=$?
rm -f factoidal_serve.ml
if [[ "$RC" -ne 0 ]]; then
  echo "  ERROR: ocamlc failed (rc=$RC)" >&2
  exit "$RC"
fi

echo "--- js_of_ocaml --pretty --debug-info --no-inline --source-map ---"
js_of_ocaml \
  --pretty --debug-info --no-inline --source-map \
  +zarith_stubs_js/biginteger.js \
  +zarith_stubs_js/runtime.js \
  fstar_int_stubs.js \
  fstar_hash_stubs.js \
  fstar_utf8_output_stubs.js \
  vendor/fzstd.umd.js \
  parquet_zstd_stubs.js \
  factoidal.debug.byte \
  -o "$OUT_JS"

OUT_MAP="$(dirname "$OUT_JS")/factoidal.debug.map"
echo "  Built: docs/fstar-extracted/factoidal.debug.js  ($(wc -c < "$OUT_JS") bytes)"
[[ -f "$OUT_MAP" ]] && echo "  Built: docs/fstar-extracted/factoidal.debug.map ($(wc -c < "$OUT_MAP") bytes)"
echo ""
echo "Reload the public demo with ?jsoo-debug=1 (e.g."
echo "  https://danbri.github.io/factoidal/?jsoo-debug=1 ) once this is pushed"
echo "and Pages has redeployed."
