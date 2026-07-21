#!/bin/bash
# Generate a W3C conformance report for docs/test-results/.
#
# Inputs  (cached from the w3c_runner invocation):
#   ocaml-output/sparql_results.log
#   ocaml-output/rdf_results.log
#
# Outputs:
#   docs/test-results/index.html            (human-readable)
#   docs/test-results/latest.csv            (one row per suite)
#   docs/test-results/latest.json           (totals + suites)
#   docs/test-results/history/<ts>.csv      (timestamped copy)
#   docs/test-results/history/<ts>.json     (timestamped copy)
#
# Usage:
#   ./generate-report.sh                    # re-generate from cached logs
#   ./generate-report.sh --run              # re-run the W3C tests first
#
# Portability: BSD/macOS + GNU/Linux. No grep -P.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
OCAML_DIR="$SCRIPT_DIR/ocaml-output"
OUTPUT_DIR="$SCRIPT_DIR/../../docs/test-results"
HISTORY_DIR="$OUTPUT_DIR/history"
SPARQL_LOG="$OCAML_DIR/sparql_results.log"
RDF_LOG="$OCAML_DIR/rdf_results.log"
# RDF 1.2 / SPARQL 1.2 (#305): w3c_runner --rdf12 / --sparql12. Same
# "Suite Results:" score-line format as the 1.1 suites above.
RDF12_LOG="$OCAML_DIR/rdf12_results.log"
SPARQL12_LOG="$OCAML_DIR/sparql12_results.log"
OWL_LOG="$OCAML_DIR/owl_profile_rl_results.log"
# Phase 2.3 DL catalog logs (added 2026-05-08). Per-catalog log
# path so we can score independently and surface separate dashboard
# rows. Loop-driven below.
OWL_TPE_LOG="$OCAML_DIR/owl_type_positive_entailment_results.log"
OWL_TNE_LOG="$OCAML_DIR/owl_type_negative_entailment_results.log"
OWL_TCON_LOG="$OCAML_DIR/owl_type_consistency_results.log"
OWL_TINC_LOG="$OCAML_DIR/owl_type_inconsistency_results.log"
OWL_EL_LOG="$OCAML_DIR/owl_profile_el_results.log"
OWL_QL_LOG="$OCAML_DIR/owl_profile_ql_results.log"
OWL_SEMDL_LOG="$OCAML_DIR/owl_semantics_direct_results.log"
# syntax-dl species-identification log (2026-07-10) — scored by the
# F*-extracted OWL2_SyntaxDL checker via `owl_runner --species`.
OWL_SYNDL_LOG="$OCAML_DIR/owl_syntax_dl_results.log"
RDFC10_LOG="$OCAML_DIR/rdfc10_results.log"
GRDDL_LOG="$OCAML_DIR/grddl_results.log"
# Wave (2026-07-05): SHACL / ShEx / JSON-LD / RML / RIF Core / VC —
# same "committed binary, no toolchain needed" pattern as owl_runner /
# rdfc10_runner above. Log paths match each suite's
# .github/test-suites/<suite>.yaml `log_path` field so the dashboard,
# tools/dispatch_test_suites.sh, and a human reading the manifest all
# agree on where the data lives.
SHACL_CORE_LOG="$OCAML_DIR/shacl_results.log"
SHACL_SPARQL_LOG="$OCAML_DIR/shacl_sparql_results.log"
SHEX_LOG="$OCAML_DIR/shex_results.log"
# ShEx negativeSyntax (grammar-reject) suite — Parser.ShExC must REJECT
# every fixture; scored by `shex_runner --negative-syntax` (2026-07-10).
SHEXNEG_LOG="$OCAML_DIR/shex_negative_syntax_results.log"
JSONLD_LOG="$OCAML_DIR/jsonld_results.log"
RML_LOG="$OCAML_DIR/rml_results.log"
RIFCORE_LOG="$OCAML_DIR/rif_results.log"
VC_LOG="$OCAML_DIR/vc_results.log"
# Track B1 (docs/designissues/2026-07-11-vc-canivc-eecc-plan.md):
# eecc_runner writes both a plain-text log (this) and, via --json, the
# flat JSON result file scrape_json_result reads (see EECCINTEROP
# scraping below).
EECC_LOG="$OCAML_DIR/eecc_interop_results.log"
# Wave (2026-07-09): the vendor/local runner binaries the project already
# ships (bin/linux-x86_64/) but that the dashboard never surfaced — every
# one is a committed binary or a committed shell script, same
# "no-toolchain-needed" pattern as owl_runner/rdfc10_runner above. Log
# paths match each suite's .github/test-suites/<suite>.yaml `log_path`
# field where a manifest exists.
XSLT_LOG="$OCAML_DIR/xslt_results.log"
XMLCONF_LOG="$OCAML_DIR/xml_conformance_results.log"
MATHML_LOG="$OCAML_DIR/mathml_results.log"
JSONSCHEMA_LOG="$OCAML_DIR/jsonschema_results.log"
SCHEMATRON_LOG="$OCAML_DIR/schematron_results.log"
QUDT_LOG="$OCAML_DIR/qudt_results.log"
CSVW_LOG="$OCAML_DIR/csvw_results.log"
DID_LOG="$OCAML_DIR/did_results.log"
JSONLD_FROMRDF_LOG="$OCAML_DIR/jsonld_fromrdf_results.log"
JSONLD_EXPAND_LOG="$OCAML_DIR/jsonld_expand_results.log"
JSONLD_COMPACT_LOG="$OCAML_DIR/jsonld_compact_results.log"
JSONLD_FLATTEN_LOG="$OCAML_DIR/jsonld_flatten_results.log"
# hdt-parity is a committed shell script (tests/local/hdt_stage4_parity.sh),
# not a runner binary; JS-side hub/npm suites run through node --test.
HDT_PARITY_LOG="$OCAML_DIR/hdt_parity_results.log"
HUB_LOG="$OCAML_DIR/hub_results.log"
NPM_LOG="$OCAML_DIR/npm_results.log"
# Wave (2026-07-09b, #82) — the F* native unit-regression harness
# (tests/unit/run-all.sh, now relinked per-test against the committed .cmx)
# plus two engine views the dashboard never surfaced: rml-io (the
# rml_runner --io source-tests section) and the npm-side toan/matrix +
# xforms engine tests. tests_unit_results.log carries the whole 41-file run;
# geosparql (37 assertions) and xpath (91) are scraped from that same log
# rather than re-run, so one harness pass feeds three rows.
TESTS_UNIT_LOG="$OCAML_DIR/tests_unit_results.log"
RML_IO_LOG="$OCAML_DIR/rml_io_results.log"
XFORMS_NPM_LOG="$OCAML_DIR/xforms_npm_results.log"
TOAN_MATRIX_LOG="$OCAML_DIR/toan_matrix_results.log"

mkdir -p "$OUTPUT_DIR"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/w3c_runner"
    OWL_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/owl_runner"
    RDFC10_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/rdfc10_runner"
    GRDDL_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/grddl_runner"
    SHACL_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/shacl_runner"
    SHEX_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/shex_runner"
    JSONLD_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/jsonld_runner"
    RML_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/rml_runner"
    RIF_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/rif_runner"
    VC_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/vc_runner"
    EECC_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/eecc_runner"
    XSLT_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/xslt_runner"
    XML_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/xml_runner"
    MATHML_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/mathml_runner"
    JSONSCHEMA_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/jsonschema_runner"
    SCHEMATRON_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/schematron_runner"
    QUDT_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/qudt_runner"
    CSVW_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/csvw_runner"
    DID_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/did_runner"
    JSONLD_FROMRDF_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/jsonld_fromrdf_runner"
    JSONLD_EXPAND_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/jsonld_expand_runner"
    JSONLD_COMPACT_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/jsonld_compact_runner"
    JSONLD_FLATTEN_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/jsonld_flatten_runner"
    ;;
  Linux-x86_64)
    RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/w3c_runner"
    OWL_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/owl_runner"
    RDFC10_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/rdfc10_runner"
    GRDDL_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/grddl_runner"
    SHACL_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/shacl_runner"
    SHEX_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/shex_runner"
    JSONLD_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/jsonld_runner"
    RML_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/rml_runner"
    RIF_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/rif_runner"
    VC_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/vc_runner"
    EECC_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/eecc_runner"
    XSLT_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/xslt_runner"
    XML_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/xml_runner"
    MATHML_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/mathml_runner"
    JSONSCHEMA_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/jsonschema_runner"
    SCHEMATRON_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/schematron_runner"
    QUDT_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/qudt_runner"
    CSVW_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/csvw_runner"
    DID_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/did_runner"
    JSONLD_FROMRDF_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/jsonld_fromrdf_runner"
    JSONLD_EXPAND_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/jsonld_expand_runner"
    JSONLD_COMPACT_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/jsonld_compact_runner"
    JSONLD_FLATTEN_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/jsonld_flatten_runner"
    ;;
  *)
    RUNNER="$OCAML_DIR/w3c_runner"
    OWL_RUNNER="$OCAML_DIR/owl_runner"
    RDFC10_RUNNER="$OCAML_DIR/rdfc10_runner"
    GRDDL_RUNNER="$OCAML_DIR/grddl_runner"
    SHACL_RUNNER="$OCAML_DIR/shacl_runner"
    SHEX_RUNNER="$OCAML_DIR/shex_runner"
    JSONLD_RUNNER="$OCAML_DIR/jsonld_runner"
    RML_RUNNER="$OCAML_DIR/rml_runner"
    RIF_RUNNER="$OCAML_DIR/rif_runner"
    VC_RUNNER="$OCAML_DIR/vc_runner"
    EECC_RUNNER="$OCAML_DIR/eecc_runner"
    XSLT_RUNNER="$OCAML_DIR/xslt_runner"
    XML_RUNNER="$OCAML_DIR/xml_runner"
    MATHML_RUNNER="$OCAML_DIR/mathml_runner"
    JSONSCHEMA_RUNNER="$OCAML_DIR/jsonschema_runner"
    SCHEMATRON_RUNNER="$OCAML_DIR/schematron_runner"
    QUDT_RUNNER="$OCAML_DIR/qudt_runner"
    CSVW_RUNNER="$OCAML_DIR/csvw_runner"
    DID_RUNNER="$OCAML_DIR/did_runner"
    JSONLD_FROMRDF_RUNNER="$OCAML_DIR/jsonld_fromrdf_runner"
    JSONLD_EXPAND_RUNNER="$OCAML_DIR/jsonld_expand_runner"
    JSONLD_COMPACT_RUNNER="$OCAML_DIR/jsonld_compact_runner"
    JSONLD_FLATTEN_RUNNER="$OCAML_DIR/jsonld_flatten_runner"
    ;;
esac

if [ "$1" = "--run" ]; then
  [ -x "$RUNNER" ] || { echo "Runner not found or not executable: $RUNNER" >&2; exit 2; }
  # Runner exits nonzero when any test fails (by design). `|| true` keeps
  # the log either way — the per-suite numbers are what we need.
  # Always run from repo root so the runner's relative third_party/ paths
  # resolve correctly regardless of caller CWD. Without this, rdf-xml
  # base-URI tests false-fail with "expected X, got X" mismatches.
  REPO_ROOT="$SCRIPT_DIR/../.."
  echo "Running SPARQL 1.1 suite…"
  ( cd "$REPO_ROOT" && "$RUNNER"       > "$SPARQL_LOG" 2>&1 ) || true
  echo "  done."
  echo "Running RDF 1.1 suite…"
  ( cd "$REPO_ROOT" && "$RUNNER" --rdf > "$RDF_LOG" 2>&1 ) || true
  echo "  done."
  echo "Running RDF 1.2 suite (--rdf12)…"
  ( cd "$REPO_ROOT" && "$RUNNER" --rdf12 > "$RDF12_LOG" 2>&1 ) || true
  echo "  done."
  echo "Running SPARQL 1.2 suite (--sparql12)…"
  ( cd "$REPO_ROOT" && "$RUNNER" --sparql12 > "$SPARQL12_LOG" 2>&1 ) || true
  echo "  done."
  if [ -x "$OWL_RUNNER" ]; then
    echo "Running OWL 2 RL profile suite (PositiveEntailmentTests)…"
    ( cd "$REPO_ROOT" && "$OWL_RUNNER" > "$OWL_LOG" 2>&1 ) || true
    echo "  done."
    # Phase 2.3d — OWL DL catalogs, now scored under the regime that
    # suits each catalog (2026-07-09; wires Tableau.tableau_materialise
    # into owl_runner via --regime dl, the same call shape w3c_runner.ml
    # uses for the SPARQL entailment-regimes OWL-Direct codepath).
    #
    #   Per-catalog regime, before (RL) -> after (chosen):
    #     type-positive-entailment  dl   RL PE 92p/112f -> DL 102p/102f (+10 sound)
    #     type-negative-entailment  dl   RL == DL (22p/1f NegEnt, 23p Cons)
    #     type-consistency          dl   (Tableau adds no unsound inconsistency)
    #     type-inconsistency        dl   RL 34p/83f -> DL 36p/81f (+2 sound)
    #     semantics-direct          dl   definitionally DL — Tableau is the
    #                                    right semantics for the DL catalog
    #     profile-EL / profile-QL   rl   EL/QL profiles, RL closure (not DL)
    #
    # DL = RL-closure -> Tableau.tableau_materialise -> RL-closure, and on
    # a per-test SIGALRM cap-trip the DL path falls back to the RL closure
    # (owl_runner.ml), so DL result >= RL result on every test — no DL row
    # can score below its RL baseline. Tableau is positive-sound (it only
    # emits entailed `i rdf:type CE` triples), so every RL/DL disagreement
    # observed was a DL gain, never a wrong answer (see the 2026-07-09
    # commit body for the full before->after table + disagreement audit).
    # DL runs the twin RL closures + Tableau, so it is slower than RL; the
    # budgets below are sized for DL incl. the Tableau.Refute satisfiability search (2026-07-10) and the heavy catalogs
    # (type-consistency, semantics-direct) stay off the dashboard hot path
    # per the extract_owl_scores note. Per-test cap keeps hard cases from
    # hanging the catalog (anti-pattern #17); a cap-trip is logged
    # [owl_closure_timeout] and scored on the RL fallback.
    export FACTOIDAL_OWL_CAP_SEC="${FACTOIDAL_OWL_CAP_SEC:-20}"
    for entry in \
        "type-positive-entailment.rdf $OWL_TPE_LOG    dl 3600" \
        "type-negative-entailment.rdf $OWL_TNE_LOG    dl  300" \
        "type-consistency.rdf         $OWL_TCON_LOG   dl 7200" \
        "type-inconsistency.rdf       $OWL_TINC_LOG   dl  900" \
        "profile-EL.rdf               $OWL_EL_LOG     rl  120" \
        "profile-QL.rdf               $OWL_QL_LOG     rl  120" \
        "semantics-direct.rdf         $OWL_SEMDL_LOG  dl 9000"; do
      IFS=' ' read -r catalog log_path regime budget <<< "$entry"
      echo "Running OWL 2 catalog $catalog (regime=${regime^^}, ${budget}s budget)…"
      ( cd "$REPO_ROOT" && timeout "$budget" "$OWL_RUNNER" \
          "third_party/testing/owl/$catalog" --regime "$regime" \
          > "$log_path" 2>&1 ) || true
      echo "  done."
    done
    # syntax-dl species identification (2026-07-10): DL-vs-FULL species
    # verdict per test case via the F*-extracted OWL2_SyntaxDL checker.
    # Purely syntactic (no closure, no tableau), so the budget is small.
    echo "Running OWL 2 catalog syntax-dl.rdf (species identification, 300s budget)…"
    ( cd "$REPO_ROOT" && timeout 300 "$OWL_RUNNER" \
        "third_party/testing/owl/syntax-dl.rdf" --species \
        > "$OWL_SYNDL_LOG" 2>&1 ) || true
    echo "  done."
  else
    echo "  owl_runner not found at $OWL_RUNNER — skipping OWL 2 RL suite." >&2
  fi
  if [ -x "$RDFC10_RUNNER" ]; then
    echo "Running RDFC-1.0 (RDF Dataset Canonicalization) suite…"
    ( cd "$REPO_ROOT" && "$RDFC10_RUNNER" > "$RDFC10_LOG" 2>&1 ) || true
    echo "  done."
  else
    echo "  rdfc10_runner not found at $RDFC10_RUNNER — skipping RDFC-1.0 suite." >&2
  fi

  # Wave (2026-07-05) — SHACL / ShEx / JSON-LD / RML / RIF Core / VC.
  # Same committed-binary pattern as owl_runner/rdfc10_runner above: each
  # runner is optional (guarded by -x), capped with `timeout` so a stuck
  # runner can't hang the dashboard refresh, and failure never aborts the
  # script (`|| true`) — the log is the source of truth either way, and a
  # missing/empty log means the scrape step below reports "not measured
  # this run" rather than fabricating a score.
  run_optional_suite () {
    local label="$1" runner="$2" log="$3" budget="$4"; shift 4
    if [ -x "$runner" ]; then
      echo "Running $label…"
      ( cd "$REPO_ROOT" && timeout "$budget" "$runner" "$@" > "$log" 2>&1 ) || true
      echo "  done."
    else
      echo "  $(basename "$runner") not found at $runner — skipping $label." >&2
    fi
  }
  run_optional_suite "SHACL Core suite"               "$SHACL_RUNNER"  "$SHACL_CORE_LOG"   60
  run_optional_suite "SHACL SPARQL-constraints suite" "$SHACL_RUNNER"  "$SHACL_SPARQL_LOG" 60 \
    "third_party/testing/shacl/data-shapes-test-suite/tests/sparql/manifest.ttl"
  run_optional_suite "ShEx validation suite"          "$SHEX_RUNNER"   "$SHEX_LOG"    180
  run_optional_suite "JSON-LD 1.1 toRdf suite"        "$JSONLD_RUNNER" "$JSONLD_LOG"   90
  run_optional_suite "RML rml-core suite"             "$RML_RUNNER"    "$RML_LOG"      90
  run_optional_suite "RIF Core suite"                 "$RIF_RUNNER"    "$RIFCORE_LOG"  90
  run_optional_suite "VC Data Model 2.0 stage-1 suite" "$VC_RUNNER"    "$VC_LOG"       60
  run_optional_suite "EECC VC/DID interop fixture suite" "$EECC_RUNNER" "$EECC_LOG"    60 \
    --json "$OUTPUT_DIR/by-suite/eecc-interop.json"

  # Wave (2026-07-09) — vendor/document suites the project already ships a
  # runner for but never surfaced on the public dashboard. Same guarded /
  # timeout-capped / fail-soft contract as the block above. Each runner is
  # optional (skips cleanly if the binary or its fixtures are absent), so a
  # checkout missing a given submodule degrades to a "not measured" row
  # rather than a fabricated score.
  run_optional_suite "XSLT 1.0 transform suite"      "$XSLT_RUNNER"       "$XSLT_LOG"       180 \
    "third_party/testing/xslt/manifest.json"
  # XML conformance (OASIS/W3C xmlconf) walks ~2600 fixtures — allow a
  # generous budget (~1-3 min observed).
  run_optional_suite "XML 1.0 conformance suite"     "$XML_RUNNER"        "$XMLCONF_LOG"    420 \
    "third_party/testing/xml/xmlconf"
  run_optional_suite "MathML 3 content suite"        "$MATHML_RUNNER"     "$MATHML_LOG"      90
  run_optional_suite "JSON Schema draft-07 suite"    "$JSONSCHEMA_RUNNER" "$JSONSCHEMA_LOG"  120
  run_optional_suite "ISO Schematron suite"          "$SCHEMATRON_RUNNER" "$SCHEMATRON_LOG"   60
  # QUDT: the integrity half validates the 131k-triple all-in-one
  # distribution shape-by-shape under the runner's own wall-clock
  # budget (default 420s), so the outer cap is the anti-pattern-#17
  # ceiling, not the expected runtime. A budget trip inside the runner
  # is a labelled skip + standing perf finding, not a hang.
  run_optional_suite "QUDT v3.4.0 SHACL suites"      "$QUDT_RUNNER"       "$QUDT_LOG"        600
  run_optional_suite "CSVW csv2rdf suite"            "$CSVW_RUNNER"       "$CSVW_LOG"        180
  run_optional_suite "DID did:key suite"             "$DID_RUNNER"        "$DID_LOG"          60
  run_optional_suite "JSON-LD 1.1 fromRdf suite"     "$JSONLD_FROMRDF_RUNNER" "$JSONLD_FROMRDF_LOG" 90
  run_optional_suite "JSON-LD 1.1 expand suite"      "$JSONLD_EXPAND_RUNNER"  "$JSONLD_EXPAND_LOG"  120
  run_optional_suite "JSON-LD 1.1 compact suite"     "$JSONLD_COMPACT_RUNNER" "$JSONLD_COMPACT_LOG" 120
  run_optional_suite "JSON-LD 1.1 flatten suite"     "$JSONLD_FLATTEN_RUNNER" "$JSONLD_FLATTEN_LOG" 120
  run_optional_suite "GRDDL Stage 1 (local subset)"  "$GRDDL_RUNNER"      "$GRDDL_LOG"       120

  # hdt-parity is a committed shell script, not a runner binary; it needs
  # the rml-core submodule ground-truth .nt. Guard on both so an
  # un-initialised submodule degrades to "not measured" instead of a
  # false-fail row.
  HDT_PARITY_SCRIPT="$REPO_ROOT/tests/local/hdt_stage4_parity.sh"
  HDT_GROUND_TRUTH="$REPO_ROOT/third_party/testing/rml-modules/rml-core/ontology/documentation/ontology.nt"
  if [ -f "$HDT_PARITY_SCRIPT" ] && [ -f "$HDT_GROUND_TRUTH" ]; then
    echo "Running HDT stage-4 backend parity…"
    ( cd "$REPO_ROOT" && timeout 300 bash tests/local/hdt_stage4_parity.sh > "$HDT_PARITY_LOG" 2>&1 ) || true
    echo "  done."
  else
    echo "  hdt-parity fixture (rml-core submodule) absent — skipping HDT parity." >&2
  fi

  # JS-side suites cover the browser/npm bundle (reactive cells, all engine
  # FP APIs, HDT-in-bundle, VC crypto via HACL* wasm). Optional: guarded by
  # `node` on PATH, timeout-capped, fail-soft. node --test prints a
  # `# tests / # pass / # fail / # skipped` summary block scraped below.
  if command -v node >/dev/null 2>&1; then
    echo "Running hub browser-bundle suite (node --test)…"
    ( cd "$REPO_ROOT" && timeout 600 node --test tests/hub/*.mjs > "$HUB_LOG" 2>&1 ) || true
    echo "  done."
    echo "Running npm package suite (node --test)…"
    ( cd "$REPO_ROOT" && timeout 600 node --test npm/factoidal/test/*.test.js > "$NPM_LOG" 2>&1 ) || true
    echo "  done."
    # Engine views scraped separately from the aggregate so each shows its
    # own row: toan+matrix (the F* CAS + Math.Matrix engines) and xforms
    # (the F* XForms bind/recalc model), both exercised through the JS bundle.
    echo "Running npm engine views (toan/matrix, xforms)…"
    ( cd "$REPO_ROOT" && timeout 300 node --test npm/factoidal/test/toan.test.js npm/factoidal/test/matrix.test.js > "$TOAN_MATRIX_LOG" 2>&1 ) || true
    ( cd "$REPO_ROOT" && timeout 300 node --test npm/factoidal/test/xforms.test.js > "$XFORMS_NPM_LOG" 2>&1 ) || true
    echo "  done."
  else
    echo "  node not found on PATH — skipping JS-side hub/npm suites." >&2
  fi

  # rml-io (rml_runner --io) — the RMLSTC0* source-tests section, a secondary
  # rml conformance view distinct from rml-core. Same guarded/fail-soft
  # contract as the runners above.
  run_optional_suite "RML rml-io source-tests" "$RML_RUNNER" "$RML_IO_LOG" 120 --io

  # F* native unit regressions (tests/unit/run-all.sh). Needs ocamlfind +
  # the committed .cmx; guard on ocamlfind so a checkout without the F* opam
  # switch degrades to a "not measured" row rather than a hard error. The run
  # relinks each test against its own dependency closure (see run-all.sh).
  if command -v ocamlfind >/dev/null 2>&1; then
    echo "Running F* unit regressions (tests/unit/run-all.sh)…"
    ( cd "$REPO_ROOT" && timeout 900 bash tests/unit/run-all.sh > "$TESTS_UNIT_LOG" 2>&1 ) || true
    echo "  done."
  else
    echo "  ocamlfind not on PATH — skipping F* unit regressions (activate the fstar opam switch to score them)." >&2
  fi
fi

if [ ! -f "$SPARQL_LOG" ] || [ ! -f "$RDF_LOG" ]; then
  echo "No cached test logs. Run with --run first." >&2
  exit 1
fi

# --- Scrape per-suite lines --------------------------------------------------
# Suite lines look like:   add  pass:8 fail:0 skip:0 unsupported:0
SPARQL_SUITES=$(grep '^  [a-z]' "$SPARQL_LOG" | grep 'pass:' || true)
RDF_SUITES=$(grep    '^  [a-z]' "$RDF_LOG"    | grep 'pass:' || true)

extract_field () {
  # $1 = field name, $2 = multi-line blob
  echo "$2" | sed -nE "s/.*${1}:([0-9]+).*/\\1/p" | awk '{s+=$1}END{print s+0}'
}

SPARQL_PASS=$(extract_field  pass        "$SPARQL_SUITES")
SPARQL_FAIL=$(extract_field  fail        "$SPARQL_SUITES")
SPARQL_SKIP=$(extract_field  skip        "$SPARQL_SUITES")
SPARQL_UNSUP=$(extract_field unsupported "$SPARQL_SUITES")
RDF_PASS=$(extract_field     pass        "$RDF_SUITES")
RDF_FAIL=$(extract_field     fail        "$RDF_SUITES")
RDF_SKIP=$(extract_field     skip        "$RDF_SUITES")
RDF_UNSUP=$(extract_field    unsupported "$RDF_SUITES")

# RDF 1.2 / SPARQL 1.2 (#305): same score-line parse as sparql/rdf. A row
# is PRESENT iff the runner produced at least one "  name  pass:N" line
# (an old binary without --rdf12/--sparql12, or a fixture-less run, yields
# an empty blob -> PRESENT 0 -> the suite is simply omitted, never a lying
# 0/0).
RDF12_SUITES=$(grep    '^  [a-z]' "$RDF12_LOG"    2>/dev/null | grep 'pass:' || true)
SPARQL12_SUITES=$(grep '^  [a-z]' "$SPARQL12_LOG" 2>/dev/null | grep 'pass:' || true)
RDF12_PASS=$(extract_field  pass        "$RDF12_SUITES")
RDF12_FAIL=$(extract_field  fail        "$RDF12_SUITES")
RDF12_SKIP=$(extract_field  skip        "$RDF12_SUITES")
RDF12_UNSUP=$(extract_field unsupported "$RDF12_SUITES")
RDF12_TOTAL=$((RDF12_PASS + RDF12_FAIL + RDF12_SKIP + RDF12_UNSUP))
RDF12_PRESENT=$([ -n "$RDF12_SUITES" ] && echo 1 || echo 0)
SPARQL12_PASS=$(extract_field  pass        "$SPARQL12_SUITES")
SPARQL12_FAIL=$(extract_field  fail        "$SPARQL12_SUITES")
SPARQL12_SKIP=$(extract_field  skip        "$SPARQL12_SUITES")
SPARQL12_UNSUP=$(extract_field unsupported "$SPARQL12_SUITES")
SPARQL12_TOTAL=$((SPARQL12_PASS + SPARQL12_FAIL + SPARQL12_SKIP + SPARQL12_UNSUP))
SPARQL12_PRESENT=$([ -n "$SPARQL12_SUITES" ] && echo 1 || echo 0)

# --- OWL 2 RL scoreboard (orthogonal to the SPARQL/RDF tables) --------------
# Score line in owl_runner stdout:
#   Profile-RL PositiveEntailmentTests: 3 pass, 27 fail (out of 30) in 0.39s
OWL_PASS=0; OWL_FAIL=0; OWL_TOTAL=0; OWL_PRESENT=0
OWL_NEG_PASS=0; OWL_NEG_FAIL=0; OWL_NEG_TOTAL=0; OWL_NEG_PRESENT=0
if [ -f "$OWL_LOG" ]; then
  OWL_LINE=$(grep -E '^Profile-RL PositiveEntailmentTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_LINE" ]; then
    OWL_PRESENT=1
    OWL_PASS=$(echo "$OWL_LINE"  | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_FAIL=$(echo "$OWL_LINE"  | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_TOTAL=$(echo "$OWL_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    OWL_PASS=${OWL_PASS:-0}
    OWL_FAIL=${OWL_FAIL:-0}
    OWL_TOTAL=${OWL_TOTAL:-0}
  fi
  # Phase 2.1 — NegativeEntailmentTest (added 2026-05-08).
  OWL_NEG_LINE=$(grep -E '^Profile-RL NegativeEntailmentTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_NEG_LINE" ]; then
    OWL_NEG_PRESENT=1
    OWL_NEG_PASS=$(echo  "$OWL_NEG_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_NEG_FAIL=$(echo  "$OWL_NEG_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_NEG_TOTAL=$(echo "$OWL_NEG_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    OWL_NEG_PASS=${OWL_NEG_PASS:-0}
    OWL_NEG_FAIL=${OWL_NEG_FAIL:-0}
    OWL_NEG_TOTAL=${OWL_NEG_TOTAL:-0}
  fi
  # Phase 2.2 — ConsistencyTest + InconsistencyTest (added 2026-05-08).
  OWL_CONS_LINE=$(grep -E '^Profile-RL ConsistencyTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_CONS_LINE" ]; then
    OWL_CONS_PRESENT=1
    OWL_CONS_PASS=$(echo  "$OWL_CONS_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_CONS_FAIL=$(echo  "$OWL_CONS_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_CONS_TOTAL=$(echo "$OWL_CONS_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
  fi
  OWL_INC_LINE=$(grep -E '^Profile-RL InconsistencyTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_INC_LINE" ]; then
    OWL_INC_PRESENT=1
    OWL_INC_PASS=$(echo  "$OWL_INC_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_INC_FAIL=$(echo  "$OWL_INC_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_INC_TOTAL=$(echo "$OWL_INC_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
  fi
fi
OWL_CONS_PRESENT=${OWL_CONS_PRESENT:-0}
OWL_CONS_PASS=${OWL_CONS_PASS:-0}; OWL_CONS_FAIL=${OWL_CONS_FAIL:-0}; OWL_CONS_TOTAL=${OWL_CONS_TOTAL:-0}
OWL_INC_PRESENT=${OWL_INC_PRESENT:-0}
OWL_INC_PASS=${OWL_INC_PASS:-0};   OWL_INC_FAIL=${OWL_INC_FAIL:-0};   OWL_INC_TOTAL=${OWL_INC_TOTAL:-0}

# Phase 2.3 — generic per-catalog parser. Reads one log file and
# extracts up to 4 score lines (Positive/NegativeEntailmentTests,
# Consistency/InconsistencyTests). Returns nothing; sets four
# 4-tuple variables prefixed by the caller-supplied prefix.
#
# Score-line shape (printed by owl_runner regardless of catalog):
#   Profile-RL <Type>Tests: N pass, M fail (out of K) in <s>s
extract_owl_scores () {
  local prefix="$1" log="$2"
  local t L p f tt
  # Regime label — owl_runner prints "Closure regime: RL|DL" as its first
  # stdout line (2026-07-09), so the dashboard can show which regime scored
  # each catalog instead of silently mixing RL and DL rows.
  local reg=""
  if [ -f "$log" ]; then
    reg=$(grep -E '^Closure regime:' "$log" | tail -1 | sed -nE 's/^Closure regime:[[:space:]]*([A-Za-z]+).*/\1/p')
  fi
  declare -g "${prefix}_REGIME=${reg:-RL}"
  for t in PositiveEntailmentTests NegativeEntailmentTests ConsistencyTests InconsistencyTests; do
    declare -g "${prefix}_${t}_PRESENT=0"
    declare -g "${prefix}_${t}_PASS=0"
    declare -g "${prefix}_${t}_FAIL=0"
    declare -g "${prefix}_${t}_TOTAL=0"
    declare -g "${prefix}_${t}_ORACLE=0"
    [ -f "$log" ] || continue
    L=$(grep -E "^Profile-RL ${t}:" "$log" | tail -1 || true)
    [ -z "$L" ] && continue
    p=$(echo  "$L" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    f=$(echo  "$L" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    tt=$(echo "$L" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    # Z33kr Phase 1: optional "; +K oracle-assisted" suffix (additive —
    # absent when the z3 oracle flipped nothing, so pre-oracle logs scrape
    # exactly as before). Captured as a SEPARATE field, never added into
    # PASS (which stays the pure-verified count).
    orc=$(echo "$L" | sed -nE 's/.*\+([0-9]+) oracle-assisted.*/\1/p')
    declare -g "${prefix}_${t}_PRESENT=1"
    declare -g "${prefix}_${t}_PASS=${p:-0}"
    declare -g "${prefix}_${t}_FAIL=${f:-0}"
    declare -g "${prefix}_${t}_TOTAL=${tt:-0}"
    declare -g "${prefix}_${t}_ORACLE=${orc:-0}"
  done
}

extract_owl_scores OWL_TPE   "$OWL_TPE_LOG"
extract_owl_scores OWL_TNE   "$OWL_TNE_LOG"
extract_owl_scores OWL_TCON  "$OWL_TCON_LOG"
extract_owl_scores OWL_TINC  "$OWL_TINC_LOG"
extract_owl_scores OWL_EL    "$OWL_EL_LOG"
extract_owl_scores OWL_QL    "$OWL_QL_LOG"
# semantics-direct.rdf — heaviest catalog (1127 tests). Runs in a
# separate scheduled workflow, not in the dashboard-refresh hot path.
extract_owl_scores OWL_SEMDL "$OWL_SEMDL_LOG"

# Catalog-level JSON aggregate (2026-07-13). extract_owl_scores gives four
# PER-TYPE tuples (PE/NE/Cons/Inc); the HTML dashboard already renders all
# four as separate bars via emit_catalog_rows (Phase 2.3, 2026-05-08), but
# latest.json never got a matching per-catalog key — profile-QL and
# profile-EL widened to full PE/NE/Cons/Inc scoring on the HTML side (87
# and 121 catalog test-type entries respectively) with no machine-readable
# counterpart. sum_owl_catalog_json folds the four PRESENT tuples into one
# PASS/FAIL/SKIP/TOTAL/PRESENT set (the shape emit_json_suite_obj expects)
# so the JSON total is the SAME scored denominator as the HTML bars, not a
# re-derived one. SKIP is the "functional-syntax-only" honest-skip count
# each score line already prints (Skip_functional_syntax_only in
# owl_runner.ml) — summed straight from the log text since
# extract_owl_scores' regex doesn't carry it, so pass+fail+skip is the
# catalog's true `test:TestCase` — err rather test-TYPE — denominator.
sum_owl_catalog_json () {
  local prefix="$1" log="$2"
  local pass=0 fail=0 total=0 present=0 oracle=0
  local t
  for t in PositiveEntailmentTests NegativeEntailmentTests ConsistencyTests InconsistencyTests; do
    local pv="${prefix}_${t}_PRESENT"
    if [ "${!pv:-0}" -eq 1 ]; then
      present=1
      local ppv="${prefix}_${t}_PASS" pfv="${prefix}_${t}_FAIL" ptv="${prefix}_${t}_TOTAL" pov="${prefix}_${t}_ORACLE"
      pass=$((pass + ${!ppv:-0}))
      fail=$((fail + ${!pfv:-0}))
      total=$((total + ${!ptv:-0}))
      # Z33kr Phase 1: oracle_assisted is a separate labelled count of
      # z3-flipped InconsistencyTests. It is NEVER added into pass/fail —
      # the pure-verified pass/fail split already includes these tests on
      # the fail side. It rides alongside for dashboard disclosure only.
      oracle=$((oracle + ${!pov:-0}))
    fi
  done
  local skip=0
  if [ -f "$log" ]; then
    skip=$(grep -oE '[0-9]+ skipped \(functional-syntax-only\)' "$log" | awk '{s+=$1} END{print s+0}')
    skip=${skip:-0}
  fi
  declare -g "${prefix}_AGG_PASS=${pass}"
  declare -g "${prefix}_AGG_FAIL=${fail}"
  declare -g "${prefix}_AGG_SKIP=${skip}"
  declare -g "${prefix}_AGG_TOTAL=$((total + skip))"
  declare -g "${prefix}_AGG_PRESENT=${present}"
  declare -g "${prefix}_AGG_ORACLE=${oracle}"
}
sum_owl_catalog_json OWL_QL "$OWL_QL_LOG"
sum_owl_catalog_json OWL_EL "$OWL_EL_LOG"
# Z33kr Phase 1 — fold the DL type-inconsistency catalog so the JSON can
# carry its oracle_assisted count (z3-flipped InconsistencyTests) as a
# separate labelled field, never inside pass.
sum_owl_catalog_json OWL_TINC "$OWL_TINC_LOG"

# syntax-dl species scores. Score-line shape (owl_runner --species):
#   OWL2-DL SpeciesTests: N pass, M fail (out of K), S skipped (functional-syntax-only) in Ts
OWL_SYNDL_PRESENT=0; OWL_SYNDL_PASS=0; OWL_SYNDL_FAIL=0; OWL_SYNDL_SKIP=0; OWL_SYNDL_TOTAL=0
if [ -f "$OWL_SYNDL_LOG" ]; then
  OWL_SYNDL_LINE=$(grep -E '^OWL2-DL SpeciesTests:' "$OWL_SYNDL_LOG" | tail -1 || true)
  if [ -n "$OWL_SYNDL_LINE" ]; then
    OWL_SYNDL_PRESENT=1
    OWL_SYNDL_PASS=$(echo "$OWL_SYNDL_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_SYNDL_FAIL=$(echo "$OWL_SYNDL_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_SYNDL_SKIP=$(echo "$OWL_SYNDL_LINE" | sed -nE 's/.* ([0-9]+) skipped.*/\1/p')
    OWL_SYNDL_PASS=${OWL_SYNDL_PASS:-0}
    OWL_SYNDL_FAIL=${OWL_SYNDL_FAIL:-0}
    OWL_SYNDL_SKIP=${OWL_SYNDL_SKIP:-0}
    OWL_SYNDL_TOTAL=$((OWL_SYNDL_PASS + OWL_SYNDL_FAIL + OWL_SYNDL_SKIP))
  fi
fi

# RIF Core scoring derived from sparql_results.log (the SPARQL
# entailment runner already executes RIF tests as part of the
# entailment regime sub-suite). We surface them on the dashboard
# as a dedicated row so RIF Core conformance is visible at a
# glance, not buried under a SPARQL row.
RIF_PRESENT=0; RIF_PASS=0; RIF_FAIL=0; RIF_TOTAL=0
if [ -f "$SPARQL_LOG" ]; then
  # `grep -c` always emits the count; exits non-zero on 0 matches.
  # Use `|| true` (NOT `|| echo 0`) so we don't double-echo the
  # zero count and end up with a multi-line value.
  RIF_PASS=$(grep -cE "^[[:space:]]+PASS: RIF " "$SPARQL_LOG" || true)
  RIF_FAIL=$(grep -cE "^[[:space:]]+FAIL: RIF " "$SPARQL_LOG" || true)
  RIF_PASS=${RIF_PASS:-0}
  RIF_FAIL=${RIF_FAIL:-0}
  RIF_TOTAL=$((RIF_PASS + RIF_FAIL))
  if [ "$RIF_TOTAL" -gt 0 ]; then
    RIF_PRESENT=1
  fi
fi

# --- RDFC-1.0 scoreboard (folded into the RDF table as suite "rdf-canon") ---
# Score line in rdfc10_runner stdout:
#   RDFC-1.0 tests: 0 pass, 67 fail, 22 stub (out of 89)
# STUB = Map / Negative entries that aren't wired in Phase 0; we report them
# in the `skip` column so they don't inflate the failure count, parallel to
# how the SPARQL runner uses skip for unsupported test types.
RDFC10_PASS=0; RDFC10_FAIL=0; RDFC10_SKIP=0; RDFC10_TOTAL=0; RDFC10_PRESENT=0
if [ -f "$RDFC10_LOG" ]; then
  RDFC10_LINE=$(grep -E '^RDFC-1\.0 tests:' "$RDFC10_LOG" | tail -1 || true)
  if [ -n "$RDFC10_LINE" ]; then
    RDFC10_PRESENT=1
    RDFC10_PASS=$(echo  "$RDFC10_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    RDFC10_FAIL=$(echo  "$RDFC10_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    RDFC10_SKIP=$(echo  "$RDFC10_LINE" | sed -nE 's/.* ([0-9]+) stub.*/\1/p')
    RDFC10_TOTAL=$(echo "$RDFC10_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    RDFC10_PASS=${RDFC10_PASS:-0}
    RDFC10_FAIL=${RDFC10_FAIL:-0}
    RDFC10_SKIP=${RDFC10_SKIP:-0}
    RDFC10_TOTAL=${RDFC10_TOTAL:-0}
  fi
fi

# --- Generic "last summary line" scraper -----------------------------------
# Shared by the SHACL / ShEx / JSON-LD / RML / RIF Core / VC suites added
# 2026-07-05. Each runner prints its own final tally line ending
# "(out of N)"; the label vocabulary differs per runner (pass/fail/
# mismatch/skip/skipped/deferred/stub/local-override) so we SUM matching
# tokens rather than hard-coding one shape — e.g. shex_runner's "N pass,
# N mismatch, N deferred, N skipped (out of N)" folds mismatch into the
# fail bucket and deferred+skipped into the skip bucket. `local-override`
# (a carefully-disputed vendored fixture scored against our own
# expectation — see tests/local-overrides/) folds into the coarse
# skip-side bucket too: on the 3-bucket dashboard it is neither a clean
# upstream pass nor a real fail, so the total reconciles while the
# runner's own output keeps it as a DISTINCT labelled count (the honesty
# invariant lives in the runner line, not this rollup). Missing log or no
# matching line => PRESENT stays 0 and every count stays 0, which the
# HTML/CSV/JSON emitters below render as "not measured this run" — never a
# fabricated number (CLAUDE.md anti-pattern #3/#25).
scrape_last_summary () {
  local prefix="$1" log="$2" anchor="${3:-}"
  declare -g "${prefix}_PRESENT=0"
  declare -g "${prefix}_PASS=0"
  declare -g "${prefix}_FAIL=0"
  declare -g "${prefix}_SKIP=0"
  declare -g "${prefix}_TOTAL=0"
  [ -f "$log" ] || return 0
  local line
  if [ -n "$anchor" ]; then
    line=$(grep -E "$anchor" "$log" 2>/dev/null | tail -1 || true)
  else
    line=$(grep -E '\(out of [0-9]+\)[[:space:]]*$' "$log" 2>/dev/null | tail -1 || true)
  fi
  [ -z "$line" ] && return 0
  local p f s t
  p=$(echo "$line" | grep -oE '[0-9]+ pass'                         | awk '{s+=$1} END{print s+0}')
  f=$(echo "$line" | grep -oE '[0-9]+ (fail|mismatch)'              | awk '{s+=$1} END{print s+0}')
  s=$(echo "$line" | grep -oE '[0-9]+ (skip|skipped|deferred|stub|local-override)' | awk '{s+=$1} END{print s+0}')
  t=$(echo "$line" | sed -nE 's/.*\(out of ([0-9]+)\).*/\1/p')
  declare -g "${prefix}_PRESENT=1"
  declare -g "${prefix}_PASS=${p:-0}"
  declare -g "${prefix}_FAIL=${f:-0}"
  declare -g "${prefix}_SKIP=${s:-0}"
  declare -g "${prefix}_TOTAL=${t:-0}"
}

# SHACL / ShEx / JSON-LD / RML: one final summary line each, no ambiguity.
scrape_last_summary SHACL_CORE   "$SHACL_CORE_LOG"
scrape_last_summary SHACL_SPARQL "$SHACL_SPARQL_LOG"
scrape_last_summary SHEX         "$SHEX_LOG"
# ShEx negativeSyntax: shex_runner --negative-syntax prints a TOTAL line
# and then a labelled "shex-negative-syntax: N pass, M fail (out of K)"
# line — anchor the labelled one explicitly.
scrape_last_summary SHEXNEG      "$SHEXNEG_LOG" '^shex-negative-syntax:'
scrape_last_summary JSONLD       "$JSONLD_LOG"
scrape_last_summary RML          "$RML_LOG"
scrape_last_summary VC           "$VC_LOG"
scrape_last_summary GRDDL        "$GRDDL_LOG"
# JSON-LD expand: jsonld_expand_runner prints one final "jsonld-expand: N
# pass, M fail, K skip (out of T)" line ending in "(out of T)", handled by
# the generic scrape_last_summary total regex (same as JSONLD toRdf above).
scrape_last_summary JSONLD_EXPAND "$JSONLD_EXPAND_LOG"
# JSON-LD compact: jsonld_compact_runner prints the same "(out of T)"
# final-line shape ("jsonld-compact: N pass, M fail, K skip (out of T)").
scrape_last_summary JSONLD_COMPACT "$JSONLD_COMPACT_LOG"
# JSON-LD flatten: jsonld_flatten_runner prints the same "(out of T)"
# final-line shape ("jsonld-flatten: N pass, M fail, K skip (out of T)").
scrape_last_summary JSONLD_FLATTEN "$JSONLD_FLATTEN_LOG"
# RIF Core: rif_runner prints THREE summary lines in one log (Part 1 —
# the 4 vendored SPARQL-manifest cases; Part 2 — the 46-test W3C
# Core_v1.22 corpus walk; and a combined total) — anchor each explicitly
# rather than taking "the last line", since all three coexist.
scrape_last_summary RIFCORE_PART1    "$RIFCORE_LOG" '^rif \(original'
scrape_last_summary RIFCORE_PART2    "$RIFCORE_LOG" '^rif-core-suite'
scrape_last_summary RIFCORE_COMBINED "$RIFCORE_LOG" '^rif TOTAL:'

# --- Added-suite tally scraper (2026-07-09) --------------------------------
# The vendor/document runners each print ONE final tally line, but the
# totals clause varies: "(out of N)", "(of N)", "(out of N cases)". This
# scraper handles all three (unlike scrape_last_summary, whose total regex
# is "(out of N)"-only — left untouched to keep the existing suites
# byte-compatible). It requires an explicit anchor because the tally is
# not always the last line (did:/csv2rdf/xml print a decorative rule after
# it) and because some runners emit a leading carriage-return before the
# tally (so a strict `^` line-anchor is avoided). Missing log / no match =>
# PRESENT stays 0 and every count 0 => the emitters render "not measured
# this run", never a fabricated number (CLAUDE.md anti-pattern #3/#25).
scrape_added_summary () {
  local prefix="$1" log="$2" anchor="$3"
  declare -g "${prefix}_PRESENT=0" "${prefix}_PASS=0" "${prefix}_FAIL=0" "${prefix}_SKIP=0" "${prefix}_TOTAL=0"
  [ -f "$log" ] || return 0
  local line
  line=$(grep -aE "$anchor" "$log" 2>/dev/null | tail -1 || true)
  [ -z "$line" ] && return 0
  local p f s t
  p=$(echo "$line" | grep -oE '[0-9]+ pass'                         | awk '{s+=$1} END{print s+0}')
  f=$(echo "$line" | grep -oE '[0-9]+ (fail|mismatch)'              | awk '{s+=$1} END{print s+0}')
  s=$(echo "$line" | grep -oE '[0-9]+ (skip|skipped|deferred|stub|local-override)' | awk '{s+=$1} END{print s+0}')
  # Accepts "(out of N)" and "(of N)" (and trailing words like "N cases").
  t=$(echo "$line" | sed -nE 's/.*\((out )?of ([0-9]+).*/\2/p')
  declare -g "${prefix}_PRESENT=1" "${prefix}_PASS=${p:-0}" "${prefix}_FAIL=${f:-0}" "${prefix}_SKIP=${s:-0}" "${prefix}_TOTAL=${t:-0}"
}

# --- node --test summary scraper -------------------------------------------
# `node --test <files>` prints an aggregate TAP summary block:
#   # tests N / # pass N / # fail N / # skipped N
# Requires a `# tests` line (present only when the run reached its summary),
# so a hung/killed run with no summary => PRESENT 0 => "not measured".
scrape_node_test () {
  local prefix="$1" log="$2"
  declare -g "${prefix}_PRESENT=0" "${prefix}_PASS=0" "${prefix}_FAIL=0" "${prefix}_SKIP=0" "${prefix}_TOTAL=0"
  [ -f "$log" ] || return 0
  local t p f s
  t=$(grep -aE '^# tests [0-9]+'   "$log" 2>/dev/null | tail -1 | sed -nE 's/^# tests ([0-9]+).*/\1/p')
  [ -z "$t" ] && return 0
  p=$(grep -aE '^# pass [0-9]+'    "$log" 2>/dev/null | tail -1 | sed -nE 's/^# pass ([0-9]+).*/\1/p')
  f=$(grep -aE '^# fail [0-9]+'    "$log" 2>/dev/null | tail -1 | sed -nE 's/^# fail ([0-9]+).*/\1/p')
  s=$(grep -aE '^# skipped [0-9]+' "$log" 2>/dev/null | tail -1 | sed -nE 's/^# skipped ([0-9]+).*/\1/p')
  declare -g "${prefix}_PRESENT=1" "${prefix}_PASS=${p:-0}" "${prefix}_FAIL=${f:-0}" "${prefix}_SKIP=${s:-0}" "${prefix}_TOTAL=${t:-0}"
}

scrape_added_summary XSLT           "$XSLT_LOG"           'XSLT 1.0 tests:'
scrape_added_summary XMLCONF        "$XMLCONF_LOG"        'xml-conformance:'
scrape_added_summary MATHML         "$MATHML_LOG"         'Content MathML evaluation:'
scrape_added_summary JSONSCHEMA     "$JSONSCHEMA_LOG"     'JSON Schema \(draft7\):'
scrape_added_summary SCHEMATRON     "$SCHEMATRON_LOG"     'Schematron: [0-9]+ pass'
scrape_added_summary QUDT_INTEGRITY "$QUDT_LOG"           'qudt-integrity: [0-9]+ pass'
scrape_added_summary QUDT_USER      "$QUDT_LOG"           'qudt-user-shapes: [0-9]+ pass'
scrape_added_summary CSVW2RDF       "$CSVW_LOG"           'csv2rdf: [0-9]+ pass'
scrape_added_summary DIDKEY         "$DID_LOG"            'did:key: [0-9]+ pass'

# Task #88 (canivc.com community-compatibility integration): these two
# suites are driven by tests/vc-di-eddsa/run.sh and tests/vc20-api/run.sh
# (mocha over bin/vc-api-shim/server.mjs), which write a small flat JSON
# result file directly rather than a TAP log — read pass/fail/skip/total
# straight out of it (no jq dependency, same grep/sed style as the rest
# of this script).
scrape_json_result() {
  local prefix="$1" json="$2"
  declare -g "${prefix}_PRESENT=0" "${prefix}_PASS=0" "${prefix}_FAIL=0" "${prefix}_SKIP=0" "${prefix}_TOTAL=0"
  [ -f "$json" ] || return 0
  local p f s t
  p=$(grep -E '"pass":'  "$json" 2>/dev/null | head -1 | sed -E 's/.*"pass": *([0-9]+).*/\1/')
  f=$(grep -E '"fail":'  "$json" 2>/dev/null | head -1 | sed -E 's/.*"fail": *([0-9]+).*/\1/')
  s=$(grep -E '"skip":'  "$json" 2>/dev/null | head -1 | sed -E 's/.*"skip": *([0-9]+).*/\1/')
  t=$(grep -E '"total":' "$json" 2>/dev/null | head -1 | sed -E 's/.*"total": *([0-9]+).*/\1/')
  [ -z "$t" ] && return 0
  declare -g "${prefix}_PRESENT=1" "${prefix}_PASS=${p:-0}" "${prefix}_FAIL=${f:-0}" "${prefix}_SKIP=${s:-0}" "${prefix}_TOTAL=${t:-0}"
}
scrape_json_result VCDIEDDSA "$OUTPUT_DIR/by-suite/vc-di-eddsa.json"
scrape_json_result VC20API   "$OUTPUT_DIR/by-suite/vc20-api.json"
# Track B1 (docs/designissues/2026-07-11-vc-canivc-eecc-plan.md):
# bin/eecc-runner/eecc_runner.ml writes its own flat JSON result file
# (same shape as the two above, via its own --json flag) rather than a
# TAP log — reuse the same scraper.
scrape_json_result EECCINTEROP "$OUTPUT_DIR/by-suite/eecc-interop.json"
scrape_added_summary JSONLD_FROMRDF "$JSONLD_FROMRDF_LOG" 'JSON-LD fromRdf tests:'
scrape_added_summary HDT_PARITY     "$HDT_PARITY_LOG"     'hdt-stage4 parity:'
scrape_node_test     HUB            "$HUB_LOG"
scrape_node_test     NPM            "$NPM_LOG"

# Wave (2026-07-09b, #82) — F* unit-harness-derived rows + rml-io + npm
# engine views. xpath / rml-io print an "(out of N)" tally, so the generic
# scrape_added_summary handles them. geosparql and the tests/unit file-level
# summary use bespoke line shapes ("N passed, M failed"; "N file(s) pass,
# M file(s) fail"), so each gets an explicit scrape that also derives TOTAL
# (never left 0 when pass>0, so the row can't render as a lying 0/0).
scrape_added_summary XPATH_UNIT "$TESTS_UNIT_LOG" 'xpath_tests: [0-9]+ pass'
scrape_added_summary RML_IO     "$RML_IO_LOG"     'rml-io: +[0-9]+ pass'
scrape_node_test     XFORMS_NPM  "$XFORMS_NPM_LOG"
scrape_node_test     TOAN_MATRIX "$TOAN_MATRIX_LOG"

# geosparql: one line "geosparql_v0_unit: <p> passed, <f> failed".
GEOSPARQL_PRESENT=0; GEOSPARQL_PASS=0; GEOSPARQL_FAIL=0; GEOSPARQL_SKIP=0; GEOSPARQL_TOTAL=0
if [ -f "$TESTS_UNIT_LOG" ]; then
  _gline=$(grep -aE 'geosparql_v0_unit: [0-9]+ passed' "$TESTS_UNIT_LOG" 2>/dev/null | tail -1 || true)
  if [ -n "$_gline" ]; then
    GEOSPARQL_PASS=$(echo "$_gline" | grep -oE '[0-9]+ passed' | awk '{s+=$1}END{print s+0}')
    GEOSPARQL_FAIL=$(echo "$_gline" | grep -oE '[0-9]+ failed' | awk '{s+=$1}END{print s+0}')
    GEOSPARQL_TOTAL=$((GEOSPARQL_PASS + GEOSPARQL_FAIL))
    GEOSPARQL_PRESENT=1
  fi
fi

# tests/unit file-level aggregate: "tests/unit summary: N file(s) pass,
# M file(s) fail (out of T)".
TESTS_UNIT_PRESENT=0; TESTS_UNIT_PASS=0; TESTS_UNIT_FAIL=0; TESTS_UNIT_SKIP=0; TESTS_UNIT_TOTAL=0
if [ -f "$TESTS_UNIT_LOG" ]; then
  _uline=$(grep -aE 'tests/unit summary:' "$TESTS_UNIT_LOG" 2>/dev/null | tail -1 || true)
  if [ -n "$_uline" ]; then
    TESTS_UNIT_PASS=$(echo "$_uline" | grep -oE '[0-9]+ file\(s\) pass' | grep -oE '[0-9]+' | head -1)
    TESTS_UNIT_FAIL=$(echo "$_uline" | grep -oE '[0-9]+ file\(s\) fail' | grep -oE '[0-9]+' | head -1)
    TESTS_UNIT_TOTAL=$(echo "$_uline" | sed -nE 's/.*\(out of ([0-9]+)\).*/\1/p')
    TESTS_UNIT_PASS=${TESTS_UNIT_PASS:-0}; TESTS_UNIT_FAIL=${TESTS_UNIT_FAIL:-0}
    TESTS_UNIT_TOTAL=${TESTS_UNIT_TOTAL:-$((TESTS_UNIT_PASS + TESTS_UNIT_FAIL))}
    TESTS_UNIT_PRESENT=1
  fi
fi

# XML conformance honest-breakdown block (the integrity accounting the
# runner prints between "-- HONEST BREAKDOWN" and the final tally). Captured
# verbatim for a collapsible sub-panel so the 1414/2585 headline is never
# read as a bare "conformance %" without the skip decomposition visible.
XMLCONF_BREAKDOWN=""
if [ -f "$XMLCONF_LOG" ]; then
  XMLCONF_BREAKDOWN=$(sed -n '/-- HONEST BREAKDOWN/,/^xml-conformance:/p' "$XMLCONF_LOG" 2>/dev/null \
    | sed '$d' \
    | sed -E 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g' || true)
fi

# --- Cross-suite family roll-ups --------------------------------------------
# Sums PASS/FAIL/SKIP/TOTAL across a list of "<PREFIX>" scrape results
# (only counting prefixes that are PRESENT), plus an ANY flag so a family
# with zero measured suites renders as "not measured this run" instead of
# a fabricated all-zero row.
sum_family () {
  local pfx tp=0 tf=0 ts=0 tt=0 any=0
  local pv fv sv tv prv
  for pfx in $1; do
    pv="${pfx}_PASS";  fv="${pfx}_FAIL"; sv="${pfx}_SKIP"
    tv="${pfx}_TOTAL"; prv="${pfx}_PRESENT"
    if [ "${!prv:-0}" -eq 1 ]; then
      any=1
      tp=$((tp + ${!pv:-0})); tf=$((tf + ${!fv:-0}))
      ts=$((ts + ${!sv:-0})); tt=$((tt + ${!tv:-0}))
    fi
  done
  echo "$tp $tf $ts $tt $any"
}

# emit_json_suite_obj — print a leading-comma keyed suite object into the
# JSON `suites` map, ONLY when the suite's <PREFIX>_PRESENT flag is 1.
# Reads <PREFIX>_{PASS,FAIL,SKIP,TOTAL} (skip/total default 0 when a suite,
# e.g. OWL, tracks no skip). The leading comma is always valid because the
# always-present sparql+rdf arrays precede every call.
emit_json_suite_obj () {
  local key="$1" prefix="$2"
  local prv="${prefix}_PRESENT"
  [ "${!prv:-0}" -eq 1 ] || return 0
  local pv="${prefix}_PASS" fv="${prefix}_FAIL" sv="${prefix}_SKIP" tv="${prefix}_TOTAL"
  printf ',\n    "%s": {"name":"%s","pass":%s,"fail":%s,"skip":%s,"total":%s}' \
    "$key" "$key" "${!pv:-0}" "${!fv:-0}" "${!sv:-0}" "${!tv:-0}"
}

SPARQL_TOTAL=$((SPARQL_PASS + SPARQL_FAIL + SPARQL_SKIP + SPARQL_UNSUP))
RDF_TOTAL=$((RDF_PASS + RDF_FAIL + RDF_SKIP + RDF_UNSUP))
COMBINED_PASS=$((SPARQL_PASS + RDF_PASS))
COMBINED_FAIL=$((SPARQL_FAIL + RDF_FAIL))
COMBINED_SKIP=$((SPARQL_SKIP + RDF_SKIP))
COMBINED_UNSUP=$((SPARQL_UNSUP + RDF_UNSUP))
COMBINED_TOTAL=$((SPARQL_TOTAL + RDF_TOTAL))

run_total=$((COMBINED_PASS + COMBINED_FAIL))
if [ "$run_total" -gt 0 ]; then
  COMBINED_PCT=$(awk -v p="$COMBINED_PASS" -v t="$run_total" 'BEGIN{printf "%.1f", 100*p/t}')
else
  COMBINED_PCT="0.0"
fi

TIMESTAMP_HUMAN=$(date -u +"%Y-%m-%d %H:%M UTC")
TIMESTAMP_ISO=$(date -u +"%Y-%m-%dT%H-%M-%SZ")
GIT_SHA=$(git -C "$SCRIPT_DIR" rev-parse --short HEAD 2>/dev/null || echo "unknown")
GIT_SHA_FULL=$(git -C "$SCRIPT_DIR" rev-parse HEAD 2>/dev/null || echo "unknown")
GIT_BRANCH=$(git -C "$SCRIPT_DIR" branch --show-current 2>/dev/null || echo "unknown")
GIT_SUBJECT=$(git -C "$SCRIPT_DIR" log -1 --pretty=%s 2>/dev/null || echo "")

# Tests-data timestamp: the most-recent commit that touched any of the
# *_results.log inputs. Distinguishes "page rendered now" from "test
# data is from N hours ago". Falls back to the page-render timestamp
# if no log files are tracked or git is unavailable.
TESTS_TIMESTAMP_RAW=$(git -C "$SCRIPT_DIR" log -1 --format='%ai' -- \
  "$SPARQL_LOG" "$RDF_LOG" "$RDFC10_LOG" "$OWL_LOG" 2>/dev/null | head -1)
if [ -n "$TESTS_TIMESTAMP_RAW" ]; then
  # macOS BSD `date` rejects the GNU -d flag; fall back through both.
  TESTS_TIMESTAMP_HUMAN=$(date -u -d "$TESTS_TIMESTAMP_RAW" +"%Y-%m-%d %H:%M UTC" 2>/dev/null || \
    date -u -j -f "%Y-%m-%d %H:%M:%S %z" "$TESTS_TIMESTAMP_RAW" +"%Y-%m-%d %H:%M UTC" 2>/dev/null || \
    echo "$TESTS_TIMESTAMP_RAW")
else
  TESTS_TIMESTAMP_HUMAN="$TIMESTAMP_HUMAN"
fi
TESTS_GIT_SHA=$(git -C "$SCRIPT_DIR" log -1 --format='%h' -- \
  "$SPARQL_LOG" "$RDF_LOG" "$RDFC10_LOG" "$OWL_LOG" 2>/dev/null || echo "unknown")

# --- CSV artifact ------------------------------------------------------------
CSV="$OUTPUT_DIR/latest.csv"
{
  echo "timestamp,commit,branch,category,suite,pass,fail,skip,unsupported"
  emit_csv_rows () {
    local blob="$1" category="$2"
    while IFS= read -r line; do
      [ -z "$line" ] && continue
      local name pass fail skip unsup
      name=$(echo  "$line" | awk '{print $1}')
      pass=$(echo  "$line" | sed -nE 's/.*pass:([0-9]+).*/\1/p')
      fail=$(echo  "$line" | sed -nE 's/.*fail:([0-9]+).*/\1/p')
      skip=$(echo  "$line" | sed -nE 's/.*skip:([0-9]+).*/\1/p')
      unsup=$(echo "$line" | sed -nE 's/.*unsupported:([0-9]+).*/\1/p')
      pass=${pass:-0}; fail=${fail:-0}; skip=${skip:-0}; unsup=${unsup:-0}
      echo "${TIMESTAMP_HUMAN},${GIT_SHA_FULL},${GIT_BRANCH},${category},${name},${pass},${fail},${skip},${unsup}"
    done <<<"$blob"
  }
  emit_csv_rows "$SPARQL_SUITES" sparql
  emit_csv_rows "$RDF_SUITES"    rdf
  if [ "$RDF12_PRESENT"    -eq 1 ]; then emit_csv_rows "$RDF12_SUITES"    rdf12;    fi
  if [ "$SPARQL12_PRESENT" -eq 1 ]; then emit_csv_rows "$SPARQL12_SUITES" sparql12; fi
  if [ "$RDFC10_PRESENT" -eq 1 ]; then
    echo "${TIMESTAMP_HUMAN},${GIT_SHA_FULL},${GIT_BRANCH},rdf,rdf-canon,${RDFC10_PASS},${RDFC10_FAIL},${RDFC10_SKIP},0"
  fi
  # Wave (2026-07-05): SHACL / ShEx / JSON-LD / RML / RIF Core / VC. Only
  # emitted when PRESENT — a suite this checkout never measured gets no
  # CSV row, same convention emit_csv_rows already uses for suites absent
  # from a log (never a fabricated 0-pass row).
  emit_csv_row_if_present () {
    local prefix="$1" category="$2" name="$3"
    local prv="${prefix}_PRESENT"
    [ "${!prv:-0}" -eq 1 ] || return 0
    local pv="${prefix}_PASS" fv="${prefix}_FAIL" sv="${prefix}_SKIP"
    echo "${TIMESTAMP_HUMAN},${GIT_SHA_FULL},${GIT_BRANCH},${category},${name},${!pv},${!fv},${!sv},0"
  }
  emit_csv_row_if_present OWL_SYNDL         owl   owl-syntax-dl-species
  emit_csv_row_if_present SHACL_CORE        shacl shacl-core
  emit_csv_row_if_present SHACL_SPARQL      shacl shacl-sparql
  emit_csv_row_if_present SHEX              shex  shex-validation
  emit_csv_row_if_present SHEXNEG           shex  shex-negative-syntax
  emit_csv_row_if_present JSONLD            jsonld jsonld-tordf
  emit_csv_row_if_present RML               rml   rml-core
  emit_csv_row_if_present RIFCORE_PART1     rif   rif-sparql-manifest
  emit_csv_row_if_present RIFCORE_PART2     rif   rif-core-corpus
  emit_csv_row_if_present VC                vc    vc-credential-structural
  # Wave (2026-07-09) — vendor/document + local/JS suites.
  emit_csv_row_if_present XSLT              xslt        xslt-1.0
  emit_csv_row_if_present XMLCONF           xml         xml-conformance
  emit_csv_row_if_present MATHML            mathml      mathml-content
  emit_csv_row_if_present JSONSCHEMA        jsonschema  jsonschema-draft7
  emit_csv_row_if_present SCHEMATRON        schematron  schematron
  emit_csv_row_if_present QUDT_INTEGRITY    qudt        qudt-integrity
  emit_csv_row_if_present QUDT_USER         qudt        qudt-user-shapes
  emit_csv_row_if_present CSVW2RDF          csvw        csvw-csv2rdf
  emit_csv_row_if_present DIDKEY            did         did-key
  emit_csv_row_if_present JSONLD_FROMRDF    jsonld      jsonld-fromrdf
  emit_csv_row_if_present JSONLD_EXPAND     jsonld      jsonld-expand
  emit_csv_row_if_present JSONLD_COMPACT    jsonld      jsonld-compact
  emit_csv_row_if_present JSONLD_FLATTEN    jsonld      jsonld-flatten
  emit_csv_row_if_present GRDDL             grddl       grddl-stage1-local
  emit_csv_row_if_present HDT_PARITY        hdt         hdt-stage4-parity
  emit_csv_row_if_present HUB               js          hub-browser-bundle
  emit_csv_row_if_present NPM               js          npm-package
  # Wave (2026-07-09b, #82).
  emit_csv_row_if_present GEOSPARQL         geosparql   geosparql-v0
  emit_csv_row_if_present XPATH_UNIT        xpath       xpath-1.0-unit
  emit_csv_row_if_present TESTS_UNIT        fstar-unit  tests-unit-files
  emit_csv_row_if_present RML_IO            rml         rml-io
  emit_csv_row_if_present TOAN_MATRIX       engines     toan-matrix
  emit_csv_row_if_present XFORMS_NPM        engines     xforms-npm
} > "$CSV"
# history snapshots retired 2026-07-20 (owner: worthless timeseries). latest.{csv,json} only.

# --- JSON artifact -----------------------------------------------------------
JSON="$OUTPUT_DIR/latest.json"
emit_json_suites () {
  local blob="$1" first=1
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local name pass fail skip unsup
    name=$(echo  "$line" | awk '{print $1}')
    pass=$(echo  "$line" | sed -nE 's/.*pass:([0-9]+).*/\1/p')
    fail=$(echo  "$line" | sed -nE 's/.*fail:([0-9]+).*/\1/p')
    skip=$(echo  "$line" | sed -nE 's/.*skip:([0-9]+).*/\1/p')
    unsup=$(echo "$line" | sed -nE 's/.*unsupported:([0-9]+).*/\1/p')
    pass=${pass:-0}; fail=${fail:-0}; skip=${skip:-0}; unsup=${unsup:-0}
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    printf '      {"name":"%s","pass":%s,"fail":%s,"skip":%s,"unsupported":%s}' \
      "$name" "$pass" "$fail" "$skip" "$unsup"
  done <<<"$blob"
}

{
  printf '{\n'
  printf '  "timestamp": "%s",\n' "$TIMESTAMP_HUMAN"
  printf '  "commit": "%s",\n'    "$GIT_SHA_FULL"
  printf '  "branch": "%s",\n'    "$GIT_BRANCH"
  printf '  "totals": {\n'
  printf '    "sparql":   {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s},\n' \
    "$SPARQL_PASS" "$SPARQL_FAIL" "$SPARQL_SKIP" "$SPARQL_UNSUP" "$SPARQL_TOTAL"
  printf '    "rdf":      {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s},\n' \
    "$RDF_PASS" "$RDF_FAIL" "$RDF_SKIP" "$RDF_UNSUP" "$RDF_TOTAL"
  if [ "$RDF12_PRESENT" -eq 1 ]; then
    printf '    "rdf12":    {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s},\n' \
      "$RDF12_PASS" "$RDF12_FAIL" "$RDF12_SKIP" "$RDF12_UNSUP" "$RDF12_TOTAL"
  fi
  if [ "$SPARQL12_PRESENT" -eq 1 ]; then
    printf '    "sparql12": {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s},\n' \
      "$SPARQL12_PASS" "$SPARQL12_FAIL" "$SPARQL12_SKIP" "$SPARQL12_UNSUP" "$SPARQL12_TOTAL"
  fi
  printf '    "combined": {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s,"pass_pct_of_runnable":%s},\n' \
    "$COMBINED_PASS" "$COMBINED_FAIL" "$COMBINED_SKIP" "$COMBINED_UNSUP" "$COMBINED_TOTAL" "$COMBINED_PCT"
  printf '    "owl_rl_positive_entailment": {"pass":%s,"fail":%s,"total":%s,"catalog":"third_party/testing/owl/profile-RL.rdf"},\n' \
    "$OWL_PASS" "$OWL_FAIL" "$OWL_TOTAL"
  printf '    "owl_syntax_dl_species": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"catalog":"third_party/testing/owl/syntax-dl.rdf"},\n' \
    "$OWL_SYNDL_PASS" "$OWL_SYNDL_FAIL" "$OWL_SYNDL_SKIP" "$OWL_SYNDL_TOTAL" "$([ "$OWL_SYNDL_PRESENT" -eq 1 ] && echo true || echo false)"
  # profile-QL / profile-EL catalog aggregates (2026-07-13) — see
  # sum_owl_catalog_json above. pass/fail/total fold all four scored
  # test:*Test types (PositiveEntailment/NegativeEntailment/Consistency/
  # Inconsistency); "regime" names the closure regime the catalog was
  # scored under (RL for both, per generate-report.sh's --run loop).
  printf '    "owl2_profile_ql": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"regime":"%s","catalog":"third_party/testing/owl/profile-QL.rdf"},\n' \
    "${OWL_QL_AGG_PASS:-0}" "${OWL_QL_AGG_FAIL:-0}" "${OWL_QL_AGG_SKIP:-0}" "${OWL_QL_AGG_TOTAL:-0}" \
    "$([ "${OWL_QL_AGG_PRESENT:-0}" -eq 1 ] && echo true || echo false)" "${OWL_QL_REGIME:-RL}"
  printf '    "owl2_profile_el": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"regime":"%s","catalog":"third_party/testing/owl/profile-EL.rdf"},\n' \
    "${OWL_EL_AGG_PASS:-0}" "${OWL_EL_AGG_FAIL:-0}" "${OWL_EL_AGG_SKIP:-0}" "${OWL_EL_AGG_TOTAL:-0}" \
    "$([ "${OWL_EL_AGG_PRESENT:-0}" -eq 1 ] && echo true || echo false)" "${OWL_EL_REGIME:-RL}"
  # Z33kr Phase 1 — OWL 2 DL type-inconsistency catalog with the
  # oracle_assisted count broken out as its OWN labelled field. pass/fail
  # is the PURE-VERIFIED split (z3-flipped tests stay on the fail side);
  # oracle_assisted is the additive z3 overlay, never summed into pass.
  printf '    "owl2_dl_inconsistency": {"pass":%s,"fail":%s,"skip":%s,"oracle_assisted":%s,"total":%s,"present":%s,"regime":"%s","catalog":"third_party/testing/owl/type-inconsistency.rdf"},\n' \
    "${OWL_TINC_AGG_PASS:-0}" "${OWL_TINC_AGG_FAIL:-0}" "${OWL_TINC_AGG_SKIP:-0}" \
    "${OWL_TINC_AGG_ORACLE:-0}" "${OWL_TINC_AGG_TOTAL:-0}" \
    "$([ "${OWL_TINC_AGG_PRESENT:-0}" -eq 1 ] && echo true || echo false)" "${OWL_TINC_REGIME:-DL}"
  printf '    "rdfc10": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"spec":"https://www.w3.org/TR/rdf-canon/"},\n' \
    "$RDFC10_PASS" "$RDFC10_FAIL" "$RDFC10_SKIP" "$RDFC10_TOTAL"
  printf '    "shacl_core":   {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/shacl/"},\n' \
    "$SHACL_CORE_PASS" "$SHACL_CORE_FAIL" "$SHACL_CORE_SKIP" "$SHACL_CORE_TOTAL" "$([ "$SHACL_CORE_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "shacl_sparql": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/shacl/#sparql-constraints"},\n' \
    "$SHACL_SPARQL_PASS" "$SHACL_SPARQL_FAIL" "$SHACL_SPARQL_SKIP" "$SHACL_SPARQL_TOTAL" "$([ "$SHACL_SPARQL_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "shex":         {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://shex.io/shex-semantics/"},\n' \
    "$SHEX_PASS" "$SHEX_FAIL" "$SHEX_SKIP" "$SHEX_TOTAL" "$([ "$SHEX_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "shex_negative_syntax": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://shex.io/shex-semantics/#shexc"},\n' \
    "$SHEXNEG_PASS" "$SHEXNEG_FAIL" "$SHEXNEG_SKIP" "$SHEXNEG_TOTAL" "$([ "$SHEXNEG_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "jsonld_tordf": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/json-ld11-api/#deserialize-json-ld-to-rdf-algorithm"},\n' \
    "$JSONLD_PASS" "$JSONLD_FAIL" "$JSONLD_SKIP" "$JSONLD_TOTAL" "$([ "$JSONLD_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "rml_core":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://kg-construct.github.io/rml-core/spec/"},\n' \
    "$RML_PASS" "$RML_FAIL" "$RML_SKIP" "$RML_TOTAL" "$([ "$RML_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "rif_core":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/rif-core/"},\n' \
    "$RIFCORE_COMBINED_PASS" "$RIFCORE_COMBINED_FAIL" "$RIFCORE_COMBINED_SKIP" "$RIFCORE_COMBINED_TOTAL" "$([ "$RIFCORE_COMBINED_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "vc_stage1":    {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/vc-data-model-2.0/"},\n' \
    "$VC_PASS" "$VC_FAIL" "$VC_SKIP" "$VC_TOTAL" "$([ "$VC_PRESENT" -eq 1 ] && echo true || echo false)"
  # Wave (2026-07-09) — vendor/document + local/JS suites. Every entry
  # always emits its key with a present boolean (0-count when unmeasured),
  # matching the shacl/shex/… convention above.
  bp () { [ "${1:-0}" -eq 1 ] && echo true || echo false; }
  # Wave (2026-07-09b, #82) — F* unit-harness rows + rml-io + npm engine views.
  printf '    "geosparql":      {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.ogc.org/standard/geosparql/"},\n' \
    "$GEOSPARQL_PASS" "$GEOSPARQL_FAIL" "$GEOSPARQL_SKIP" "$GEOSPARQL_TOTAL" "$(bp "$GEOSPARQL_PRESENT")"
  printf '    "xpath_unit":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/xpath-10/"},\n' \
    "$XPATH_UNIT_PASS" "$XPATH_UNIT_FAIL" "$XPATH_UNIT_SKIP" "$XPATH_UNIT_TOTAL" "$(bp "$XPATH_UNIT_PRESENT")"
  printf '    "tests_unit":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"internal (F* native unit regressions, tests/unit/run-all.sh; files-passing/files-failing)"},\n' \
    "$TESTS_UNIT_PASS" "$TESTS_UNIT_FAIL" "$TESTS_UNIT_SKIP" "$TESTS_UNIT_TOTAL" "$(bp "$TESTS_UNIT_PRESENT")"
  printf '    "rml_io":         {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://kg-construct.github.io/rml-io/spec/"},\n' \
    "$RML_IO_PASS" "$RML_IO_FAIL" "$RML_IO_SKIP" "$RML_IO_TOTAL" "$(bp "$RML_IO_PRESENT")"
  printf '    "toan_matrix":    {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"internal (TOAN CAS + Math.Matrix engines, npm node --test)"},\n' \
    "$TOAN_MATRIX_PASS" "$TOAN_MATRIX_FAIL" "$TOAN_MATRIX_SKIP" "$TOAN_MATRIX_TOTAL" "$(bp "$TOAN_MATRIX_PRESENT")"
  printf '    "xforms":         {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/xforms/"},\n' \
    "$XFORMS_NPM_PASS" "$XFORMS_NPM_FAIL" "$XFORMS_NPM_SKIP" "$XFORMS_NPM_TOTAL" "$(bp "$XFORMS_NPM_PRESENT")"
  printf '    "xslt":           {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/xslt-10/"},\n' \
    "$XSLT_PASS" "$XSLT_FAIL" "$XSLT_SKIP" "$XSLT_TOTAL" "$(bp "$XSLT_PRESENT")"
  printf '    "xml_conformance":{"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/xml/"},\n' \
    "$XMLCONF_PASS" "$XMLCONF_FAIL" "$XMLCONF_SKIP" "$XMLCONF_TOTAL" "$(bp "$XMLCONF_PRESENT")"
  printf '    "mathml":         {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/MathML3/"},\n' \
    "$MATHML_PASS" "$MATHML_FAIL" "$MATHML_SKIP" "$MATHML_TOTAL" "$(bp "$MATHML_PRESENT")"
  printf '    "jsonschema":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://json-schema.org/draft-07/schema"},\n' \
    "$JSONSCHEMA_PASS" "$JSONSCHEMA_FAIL" "$JSONSCHEMA_SKIP" "$JSONSCHEMA_TOTAL" "$(bp "$JSONSCHEMA_PRESENT")"
  printf '    "schematron":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.iso.org/standard/74515.html"},\n' \
    "$SCHEMATRON_PASS" "$SCHEMATRON_FAIL" "$SCHEMATRON_SKIP" "$SCHEMATRON_TOTAL" "$(bp "$SCHEMATRON_PRESENT")"
  printf '    "csvw_csv2rdf":   {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/csv2rdf/"},\n' \
    "$CSVW2RDF_PASS" "$CSVW2RDF_FAIL" "$CSVW2RDF_SKIP" "$CSVW2RDF_TOTAL" "$(bp "$CSVW2RDF_PRESENT")"
  printf '    "did_key":        {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/did-core/"},\n' \
    "$DIDKEY_PASS" "$DIDKEY_FAIL" "$DIDKEY_SKIP" "$DIDKEY_TOTAL" "$(bp "$DIDKEY_PRESENT")"
  printf '    "vc_di_eddsa":    {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://w3c.github.io/vc-di-eddsa-test-suite/"},\n' \
    "$VCDIEDDSA_PASS" "$VCDIEDDSA_FAIL" "$VCDIEDDSA_SKIP" "$VCDIEDDSA_TOTAL" "$(bp "$VCDIEDDSA_PRESENT")"
  printf '    "vc20_api":       {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://w3c.github.io/vc-data-model-2.0-test-suite/"},\n' \
    "$VC20API_PASS" "$VC20API_FAIL" "$VC20API_SKIP" "$VC20API_TOTAL" "$(bp "$VC20API_PRESENT")"
  printf '    "eecc_interop":   {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://github.com/european-epc-competence-center"},\n' \
    "$EECCINTEROP_PASS" "$EECCINTEROP_FAIL" "$EECCINTEROP_SKIP" "$EECCINTEROP_TOTAL" "$(bp "$EECCINTEROP_PRESENT")"
  printf '    "jsonld_fromrdf": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/json-ld11-api/#serialize-rdf-as-json-ld-algorithm"},\n' \
    "$JSONLD_FROMRDF_PASS" "$JSONLD_FROMRDF_FAIL" "$JSONLD_FROMRDF_SKIP" "$JSONLD_FROMRDF_TOTAL" "$(bp "$JSONLD_FROMRDF_PRESENT")"
  printf '    "jsonld_expand":  {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/json-ld11-api/#expansion-algorithm"},\n' \
    "$JSONLD_EXPAND_PASS" "$JSONLD_EXPAND_FAIL" "$JSONLD_EXPAND_SKIP" "$JSONLD_EXPAND_TOTAL" "$(bp "$JSONLD_EXPAND_PRESENT")"
  printf '    "jsonld_compact": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/json-ld11-api/#compaction-algorithm"},\n' \
    "$JSONLD_COMPACT_PASS" "$JSONLD_COMPACT_FAIL" "$JSONLD_COMPACT_SKIP" "$JSONLD_COMPACT_TOTAL" "$(bp "$JSONLD_COMPACT_PRESENT")"
  printf '    "jsonld_flatten": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/json-ld11-api/#flattening-algorithm"},\n' \
    "$JSONLD_FLATTEN_PASS" "$JSONLD_FLATTEN_FAIL" "$JSONLD_FLATTEN_SKIP" "$JSONLD_FLATTEN_TOTAL" "$(bp "$JSONLD_FLATTEN_PRESENT")"
  printf '    "hdt_stage4_parity":{"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"internal (HDT backend parity vs in-memory)"},\n' \
    "$HDT_PARITY_PASS" "$HDT_PARITY_FAIL" "$HDT_PARITY_SKIP" "$HDT_PARITY_TOTAL" "$(bp "$HDT_PARITY_PRESENT")"
  printf '    "hub_browser_bundle":{"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"internal (node --test tests/hub)"},\n' \
    "$HUB_PASS" "$HUB_FAIL" "$HUB_SKIP" "$HUB_TOTAL" "$(bp "$HUB_PRESENT")"
  printf '    "npm_package":    {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"internal (node --test npm/factoidal/test)"}\n' \
    "$NPM_PASS" "$NPM_FAIL" "$NPM_SKIP" "$NPM_TOTAL" "$(bp "$NPM_PRESENT")"
  printf '  },\n'
  printf '  "suites": {\n'
  printf '    "sparql": [\n'
  emit_json_suites "$SPARQL_SUITES"
  printf '\n    ],\n'
  printf '    "rdf": [\n'
  emit_json_suites "$RDF_SUITES"
  printf '\n    ]'
  # Per-suite objects (2026-07-09) — one keyed {name,pass,fail,skip,total}
  # entry per non-(sparql|rdf) suite, present-guarded. Each prints a
  # leading comma, valid because sparql+rdf always precede them. Covers the
  # earlier-wave conformance suites (owl/rdfc10/shacl/…, mirrored here from
  # their totals) plus the 2026-07-09 vendor/document + local/JS suites, so
  # the machine-readable `suites` map lists every shipped engine, not just
  # the two W3C core families.
  emit_json_suite_obj "rdf12"    RDF12
  emit_json_suite_obj "sparql12" SPARQL12
  emit_json_suite_obj "owl_rl_positive_entailment" OWL
  emit_json_suite_obj "owl_syntax_dl_species" OWL_SYNDL
  emit_json_suite_obj "owl2_profile_ql" OWL_QL_AGG
  emit_json_suite_obj "owl2_profile_el" OWL_EL_AGG
  emit_json_suite_obj "rdfc10"            RDFC10
  emit_json_suite_obj "shacl_core"        SHACL_CORE
  emit_json_suite_obj "shacl_sparql"      SHACL_SPARQL
  emit_json_suite_obj "shex"              SHEX
  emit_json_suite_obj "shex_negative_syntax" SHEXNEG
  emit_json_suite_obj "jsonld_tordf"      JSONLD
  emit_json_suite_obj "rml_core"          RML
  emit_json_suite_obj "rif_core"          RIFCORE_COMBINED
  emit_json_suite_obj "vc_stage1"         VC
  emit_json_suite_obj "xslt"              XSLT
  emit_json_suite_obj "xml_conformance"   XMLCONF
  emit_json_suite_obj "mathml"            MATHML
  emit_json_suite_obj "jsonschema"        JSONSCHEMA
  emit_json_suite_obj "schematron"        SCHEMATRON
  emit_json_suite_obj "qudt_integrity"    QUDT_INTEGRITY
  emit_json_suite_obj "qudt_user_shapes"  QUDT_USER
  emit_json_suite_obj "csvw_csv2rdf"      CSVW2RDF
  emit_json_suite_obj "did_key"           DIDKEY
  emit_json_suite_obj "vc_di_eddsa"       VCDIEDDSA
  emit_json_suite_obj "vc20_api"          VC20API
  emit_json_suite_obj "eecc_interop"      EECCINTEROP
  emit_json_suite_obj "jsonld_fromrdf"    JSONLD_FROMRDF
  emit_json_suite_obj "jsonld_expand"     JSONLD_EXPAND
  emit_json_suite_obj "jsonld_compact"    JSONLD_COMPACT
  emit_json_suite_obj "jsonld_flatten"    JSONLD_FLATTEN
  emit_json_suite_obj "grddl_stage1"      GRDDL
  emit_json_suite_obj "hdt_stage4_parity" HDT_PARITY
  emit_json_suite_obj "hub_browser_bundle" HUB
  emit_json_suite_obj "npm_package"       NPM
  # Wave (2026-07-09b, #82).
  emit_json_suite_obj "geosparql"         GEOSPARQL
  emit_json_suite_obj "xpath_unit"        XPATH_UNIT
  emit_json_suite_obj "tests_unit"        TESTS_UNIT
  emit_json_suite_obj "rml_io"            RML_IO
  emit_json_suite_obj "toan_matrix"       TOAN_MATRIX
  emit_json_suite_obj "xforms"            XFORMS_NPM
  printf '\n  }\n'
  printf '}\n'
} > "$JSON"
# history snapshot retired (see above).

# --- HTML suite rows ---------------------------------------------------------
# status_for — green/amber/grey classifier shared by every suite-node
# emitter below (moved up from the family-section block further down so
# emit_suite_rows can use it too). "any" is a 0/1 flag: 0 means "not
# measured this run" regardless of fail count, so an empty suite never
# renders as a false green.
status_for () {
  local fail="$1" any="$2"
  if [ "${any:-0}" -ne 1 ]; then echo grey
  elif [ "$fail" -eq 0 ]; then echo green
  else echo amber
  fi
}

# meter_segments — the shared 3-segment pass/fail/skip stacked-bar
# markup. One definition, reused by every row emitter on the page (this
# function, emit_owl_bar_row, emit_owl_skip_row, and the new
# family_suite_row) so a suite's proportions always render the same way
# regardless of which corpus it came from.
meter_segments () {
  local pass="$1" fail="$2" skip="$3" total="$4"
  local pp fp sp
  if [ "$total" -gt 0 ]; then
    pp=$(awk -v p="$pass" -v t="$total" 'BEGIN{printf "%.2f", 100*p/t}')
    fp=$(awk -v p="$fail" -v t="$total" 'BEGIN{printf "%.2f", 100*p/t}')
    sp=$(awk -v p="$skip" -v t="$total" 'BEGIN{printf "%.2f", 100*p/t}')
  else
    pp=0; fp=0; sp=0
  fi
  printf '<div class="meter"><div class="seg seg-pass" style="width:%s%%"></div><div class="seg seg-fail" style="width:%s%%"></div><div class="seg seg-skip" style="width:%s%%"></div></div>' \
    "$pp" "$fp" "$sp"
}

# condensed_numbers — the compact "P/F/S of T" score used in a collapsed
# suite/family summary line, where a fully-labelled sentence doesn't fit
# on one row. Never the ONLY place the numbers appear: every caller also
# renders the fully-labelled "P pass, F fail, S skip (out of T)" form
# somewhere in the expanded body, and the page-top legend explains the
# P/F/S order once — so this is a documented abbreviation, not a bare
# unlabelled score (CLAUDE.md anti-pattern #25 governs prose/reports;
# this is a UI element with its key stated once, up front).
condensed_numbers () {
  local pass="$1" fail="$2" skip="$3" total="$4"
  printf '%s/%s/%s of %s' "$pass" "$fail" "$skip" "$total"
}

# --- Per-suite YAML "remaining:" reader --------------------------------
# The .github/test-suites/<suite>.yaml manifests (schema documented in
# that dir's README) can carry an optional `remaining:` block: a list of
# short, plain-language "what's still incomplete" items, sourced from
# docs/claude-rules/w3c-completeness-ledger.md and translated out of
# internal shorthand. Reuses the exact same block-list YAML shape (and
# the same tiny grep/sed-free awk parse) as
# tools/dispatch_test_suites.sh's read_paths_block, so a human editing
# either file only has to learn one list syntax.
TEST_SUITES_DIR="$SCRIPT_DIR/../../.github/test-suites"
read_yaml_remaining () {
  local file="$1"
  [ -f "$file" ] || return 0
  awk '
    BEGIN { in_block = 0 }
    /^[A-Za-z_][A-Za-z0-9_.]*:[[:space:]]*$/ {
      key = $0; sub(/:.*$/, "", key); gsub(/^[[:space:]]+/, "", key)
      if (key == "remaining") { in_block = 1; next } else { in_block = 0 }
    }
    in_block && /^[[:space:]]+-[[:space:]]+/ {
      val = $0
      sub(/^[[:space:]]+-[[:space:]]+/, "", val)
      sub(/^"/, "", val); sub(/"[[:space:]]*$/, "", val)
      sub(/^'\''/, "", val); sub(/'\''[[:space:]]*$/, "", val)
      if (val != "") print val
    }
    !/^[[:space:]]/ && !/^$/ && in_block { in_block = 0 }
  ' "$file"
}

# family_remaining <suite-basename>... — union of read_yaml_remaining
# across one or more .github/test-suites/<name>.yaml manifests (a family
# on the page can span several suite manifests, e.g. JSON-LD 1.1's four
# runnable suites plus its family-level bookkeeping file). Basenames
# only, no .yaml suffix, no path.
family_remaining () {
  local base
  for base in "$@"; do
    read_yaml_remaining "$TEST_SUITES_DIR/${base}.yaml"
  done
}

# emit_suite_rows — one collapsible <details class="suite-node"> per
# suite (owner directive 2026-07-10: "one collapsible node per checkable
# suite", default-collapsed, summary shows name + labelled pass/fail/skip
# + a status dot). unsupported tests are folded into the displayed skip
# count (the raw fields stay separate in latest.csv/latest.json).
emit_suite_rows () {
  local blob="$1"
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local name pass fail skip unsup total cls meter name_html numbers skip_disp
    name=$(echo  "$line" | awk '{print $1}')
    pass=$(echo  "$line" | sed -nE 's/.*pass:([0-9]+).*/\1/p')
    fail=$(echo  "$line" | sed -nE 's/.*fail:([0-9]+).*/\1/p')
    skip=$(echo  "$line" | sed -nE 's/.*skip:([0-9]+).*/\1/p')
    unsup=$(echo "$line" | sed -nE 's/.*unsupported:([0-9]+).*/\1/p')
    pass=${pass:-0}; fail=${fail:-0}; skip=${skip:-0}; unsup=${unsup:-0}
    total=$((pass + fail + skip + unsup))
    if [ "$total" -eq 0 ]; then continue; fi
    skip_disp=$((skip + unsup))
    cls=$(status_for "$fail" 1)
    # Inline scope hint for the SPARQL "entailment" suite — it's a
    # narrow regime suite, NOT OWL conformance, and the name alone
    # invites confusion. The OWL panel below is the larger, separate
    # universe of entailment tests.
    name_html="${name}"
    if [ "$name" = "entailment" ]; then
      name_html='entailment <small style="font-weight:normal;color:var(--muted)">(SPARQL 1.1 regime — RDFS / D-entailment, 70 tests)</small>'
    fi
    meter=$(meter_segments "$pass" "$fail" "$skip_disp" "$total")
    local condensed; condensed=$(condensed_numbers "$pass" "$fail" "$skip_disp" "$total")
    # Fully-labelled numbers, never a bare ratio (CLAUDE.md anti-pattern
    # #25) — rendered in the body, once expanded. The summary line uses
    # the condensed P/F/S form (legend at the top of the page explains
    # it) so one suite fits one compact row on a phone.
    numbers="${pass} pass, ${fail} fail, ${skip_disp} skip (out of ${total})"
    cat <<ROW
      <details class="suite-node ${cls}">
        <summary><span class="suite-name">${name_html}</span><span class="suite-numbers">${condensed}</span><span class="dot ${cls}"></span></summary>
        <div class="suite-body">
          ${meter}
          <p class="suite-numbers-full">${numbers}</p>
        </div>
      </details>
ROW
  done <<<"$blob"
}

# Per-REC bucket → list of W3C suite names.
# Each bucket gets its own <h3> subsection inside the SPARQL 1.1 / RDF 1.1
# parents. Unmatched suites fall through to the "Other" bucket so they
# stay visible on the dashboard.
sparql_rec_for_suite () {
  case "$1" in
    aggregates|bind|bindings|cast|construct|csv-tsv-res|exists|functions|grouping|json-res|negation|project-expression|property-path|subquery|syntax-query)
      echo "query" ;;
    add|basic-update|clear|copy|delete|delete-data|delete-insert|delete-where|drop|move|syntax-update-1|syntax-update-2|update-silent)
      echo "update" ;;
    protocol|http-rdf-update)
      echo "protocol" ;;
    service|syntax-fed)
      echo "federated" ;;
    service-description)
      echo "service-description" ;;
    entailment)
      echo "entailment" ;;
    *)
      echo "other" ;;
  esac
}

rdf_rec_for_suite () {
  case "$1" in
    rdf-n-triples) echo "n-triples" ;;
    rdf-turtle)    echo "turtle" ;;
    rdf-n-quads)   echo "n-quads" ;;
    rdf-trig)      echo "trig" ;;
    rdf-xml)       echo "rdf-xml" ;;
    rdf-mt)        echo "semantics" ;;
    *)             echo "other" ;;
  esac
}

# Filter $1 (raw suite log lines) to only those whose suite name maps
# to bucket $2, using the bucket-fn $3.
filter_suites_by_bucket () {
  local blob="$1"; local target_bucket="$2"; local bucket_fn="$3"
  local out=""
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local name; name=$(echo "$line" | awk '{print $1}')
    local bucket; bucket=$("$bucket_fn" "$name")
    if [ "$bucket" = "$target_bucket" ]; then
      out+="$line"$'\n'
    fi
  done <<<"$blob"
  printf '%s' "$out"
}

# emit_rec_subsection — h3 + suite rows inside a per-REC bucket, but
# only if the bucket has at least one suite. Layout: pure markup; the
# h3 sits inside the parent .suites container in the existing CSS, so
# subsection headings stay aligned with the surrounding bars.
emit_rec_subsection () {
  local title="$1"; local href="$2"; local lines="$3"
  if [ -z "$(echo "$lines" | tr -d '[:space:]')" ]; then
    return
  fi
  local rows; rows=$(emit_suite_rows "$lines")
  cat <<HTML
  <h3 class="rec-subhead"><a href="${href}" target="_blank" rel="noopener">${title}</a></h3>
${rows}
HTML
}

SPARQL_ROWS_HTML=$(
  emit_rec_subsection "SPARQL 1.1 Query Language"      "https://www.w3.org/TR/sparql11-query/"               "$(filter_suites_by_bucket "$SPARQL_SUITES" query              sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Update"              "https://www.w3.org/TR/sparql11-update/"              "$(filter_suites_by_bucket "$SPARQL_SUITES" update             sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Protocol"            "https://www.w3.org/TR/sparql11-protocol/"            "$(filter_suites_by_bucket "$SPARQL_SUITES" protocol           sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Federated Query"     "https://www.w3.org/TR/sparql11-federated-query/"     "$(filter_suites_by_bucket "$SPARQL_SUITES" federated          sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Service Description" "https://www.w3.org/TR/sparql11-service-description/" "$(filter_suites_by_bucket "$SPARQL_SUITES" service-description sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Entailment Regimes"  "https://www.w3.org/TR/sparql11-entailment/"          "$(filter_suites_by_bucket "$SPARQL_SUITES" entailment         sparql_rec_for_suite)"
  emit_rec_subsection "Other (uncategorised)"          ""                                                    "$(filter_suites_by_bucket "$SPARQL_SUITES" other              sparql_rec_for_suite)"
)

RDF_ROWS_HTML=$(
  emit_rec_subsection "RDF 1.1 N-Triples"  "https://www.w3.org/TR/n-triples/"           "$(filter_suites_by_bucket "$RDF_SUITES" n-triples rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 Turtle"     "https://www.w3.org/TR/turtle/"              "$(filter_suites_by_bucket "$RDF_SUITES" turtle    rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 N-Quads"    "https://www.w3.org/TR/n-quads/"             "$(filter_suites_by_bucket "$RDF_SUITES" n-quads   rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 TriG"       "https://www.w3.org/TR/trig/"                "$(filter_suites_by_bucket "$RDF_SUITES" trig      rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 RDF/XML"    "https://www.w3.org/TR/rdf-syntax-grammar/"  "$(filter_suites_by_bucket "$RDF_SUITES" rdf-xml   rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 Semantics"  "https://www.w3.org/TR/rdf11-mt/"            "$(filter_suites_by_bucket "$RDF_SUITES" semantics rdf_rec_for_suite)"
  emit_rec_subsection "Other (uncategorised)" ""                                        "$(filter_suites_by_bucket "$RDF_SUITES" other     rdf_rec_for_suite)"
)

# ---------------------------------------------------------------------
# emit_failure_detail — given a per-category log file and a section id,
# extract every "FAIL: …" / "skip: …" / "SKIP: …" line and render an
# inline <details> block. The h2 totals link to the section ids
# (#sparql-failures, #sparql-skips, #rdf-failures) so a reader who
# clicks "1 fail" lands on the actual failure description, not a
# dead-end count.
# ---------------------------------------------------------------------
# emit_failure_detail — owner directive 2026-07-10: never render a
# clickable failures/skips disclosure that turns out to be empty only
# after the reader clicks it. Each of the two <details> blocks below is
# emitted ONLY when its list is non-empty; when a log has zero FAILs (or
# zero skips) that block is omitted entirely — the suite's own summary
# line already shows "0 fail" / "0 skip", so there is nothing to expand
# into. Applies uniformly to every caller of this function.
emit_failure_detail () {
  local log="$1"
  local id_prefix="$2"
  local label="$3"

  # Bail with empty output if the log doesn't exist (e.g. RDF-only run).
  if [ ! -f "$log" ]; then
    echo ""
    return
  fi

  # FAIL lines.
  local fail_block=""
  fail_block=$(grep -E '^[[:space:]]*FAIL:' "$log" 2>/dev/null \
               | sed -E 's/^[[:space:]]+//' \
               | sed -E 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g' \
               | awk '{ printf "<li>%s</li>\n", $0 }' || true)

  # skip lines (lower- and upper-case).
  local skip_block=""
  skip_block=$(grep -E '^[[:space:]]*([sS][kK][iI][pP]):' "$log" 2>/dev/null \
               | sed -E 's/^[[:space:]]+//' \
               | sed -E 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g' \
               | awk '{ printf "<li>%s</li>\n", $0 }' || true)

  if [ -n "$fail_block" ]; then
    cat <<HTML
<details id="${id_prefix}-failures" class="failure-detail">
  <summary>${label} failures (click to expand)</summary>
  <ul>
${fail_block}
  </ul>
</details>
HTML
  fi

  if [ -n "$skip_block" ]; then
    cat <<HTML
<details id="${id_prefix}-skips" class="failure-detail">
  <summary>${label} skips (click to expand)</summary>
  <ul>
${skip_block}
  </ul>
</details>
HTML
  fi
}

SPARQL_FAILURE_DETAIL_HTML=$(emit_failure_detail "$SPARQL_LOG" "sparql" "SPARQL 1.1")
RDF_FAILURE_DETAIL_HTML=$(emit_failure_detail "$RDF_LOG" "rdf" "RDF 1.1")

# Note: RDFC-1.0 (RDF Dataset Canonicalization) is a SEPARATE W3C
# corpus (vendored at third_party/testing/rdf-canon/). Earlier
# versions of this report stitched a synthetic "rdf-canon" row into
# the RDF 1.1 panel above, which made readers think the 26 RDFC-1.0
# fails were RDF 1.1 core fails. They are not — the RDF 1.1 totals
# (~1031 tests) come exclusively from third_party/testing/w3c/rdf/
# rdf11/{rdf-mt, rdf-n-quads, rdf-n-triples, rdf-trig, rdf-turtle,
# rdf-xml}. RDFC-1.0 has its own dedicated panel below.

# --- OWL 2 panel ---------------------------------------------------------
# Distinct corpus, distinct denominator; deliberately NOT folded into the
# SPARQL/RDF totals tiles. profile-RL gets actual pass/fail from
# owl_runner; other OWL 2 catalogs are listed as "skipped for now" with
# rationale, so the user can see the full W3C OWL 2 Test Cases footprint
# we've vendored and what we're NOT yet exercising.
if [ "$OWL_PRESENT" -ne 1 ]; then
  OWL_PASS=0; OWL_FAIL=0; OWL_TOTAL=0
fi

# ConsistencyTest + InconsistencyTest bars (Phase 2.2, 2026-05-08).
emit_owl_bar_row () {
  local label="$1" pass="$2" fail="$3" total="$4"
  local skip=$((total - pass - fail))
  [ "$skip" -lt 0 ] && skip=0
  local any=1
  [ "$total" -eq 0 ] && any=0
  local cls meter numbers condensed
  cls=$(status_for "$fail" "$any")
  meter=$(meter_segments "$pass" "$fail" "$skip" "$total")
  numbers="${pass} pass, ${fail} fail, ${skip} skip (out of ${total})"
  condensed=$(condensed_numbers "$pass" "$fail" "$skip" "$total")
  printf '<details class="suite-node %s">
    <summary><span class="suite-name">%s</span><span class="suite-numbers">%s</span><span class="dot %s"></span></summary>
    <div class="suite-body">
      %s
      <p class="suite-numbers-full">%s</p>
    </div>
  </details>' "$cls" "$label" "$condensed" "$cls" "$meter" "$numbers"
}
OWL_NEG_ROW=""
if [ "$OWL_NEG_PRESENT" -eq 1 ]; then
  OWL_NEG_ROW=$(emit_owl_bar_row "profile-RL NegEnt" "$OWL_NEG_PASS" "$OWL_NEG_FAIL" "$OWL_NEG_TOTAL")
fi
OWL_CONS_ROW=""
if [ "$OWL_CONS_PRESENT" -eq 1 ]; then
  OWL_CONS_ROW=$(emit_owl_bar_row "profile-RL Consistency"   "$OWL_CONS_PASS" "$OWL_CONS_FAIL" "$OWL_CONS_TOTAL")
fi
OWL_INC_ROW=""
if [ "$OWL_INC_PRESENT" -eq 1 ]; then
  OWL_INC_ROW=$(emit_owl_bar_row  "profile-RL Inconsistency" "$OWL_INC_PASS"  "$OWL_INC_FAIL"  "$OWL_INC_TOTAL")
fi

# --- Tableau OWL-DL entailment row (first-class, named) ------------------
# Trust-repair (2026-07-09): the F* tableau reasoner
# (Tableau.fst :: tableau_materialise) has driven the W3C SPARQL 1.1
# entailment-regimes suite for weeks, but its result was only visible as a
# SPARQL sub-row nobody browsing for "the OWL tableau reasoner" would find.
# Surface it under its own name at the top of the OWL 2 panel, sourced from
# the SAME entailment scrape (SPARQL_SUITES, line ~290) — interpolated,
# never hardcoded, so the row can never drift from the measured value.
TAB_ENTAIL_LINE=$(printf '%s\n' "$SPARQL_SUITES" | grep -E '^[[:space:]]*entailment[[:space:]]' | head -1 || true)
TAB_ENTAIL_PASS=$(echo "$TAB_ENTAIL_LINE" | sed -nE 's/.*pass:([0-9]+).*/\1/p'); TAB_ENTAIL_PASS=${TAB_ENTAIL_PASS:-0}
TAB_ENTAIL_FAIL=$(echo "$TAB_ENTAIL_LINE" | sed -nE 's/.*fail:([0-9]+).*/\1/p'); TAB_ENTAIL_FAIL=${TAB_ENTAIL_FAIL:-0}
TAB_ENTAIL_SKIP=$(echo "$TAB_ENTAIL_LINE" | sed -nE 's/.*skip:([0-9]+).*/\1/p'); TAB_ENTAIL_SKIP=${TAB_ENTAIL_SKIP:-0}
TAB_ENTAIL_TOTAL=$((TAB_ENTAIL_PASS + TAB_ENTAIL_FAIL + TAB_ENTAIL_SKIP))
TAB_ENTAIL_PRESENT=0
[ "$TAB_ENTAIL_TOTAL" -gt 0 ] && TAB_ENTAIL_PRESENT=1
TABLEAU_ROW=""
if [ "$TAB_ENTAIL_TOTAL" -gt 0 ]; then
  TABLEAU_ROW=$(emit_owl_bar_row \
    'OWL DL entailment — Tableau <small style="font-weight:normal;color:var(--muted)">(<code>Tableau.fst</code> · <code>tableau_materialise</code>, live in <code>w3c_runner</code> — SPARQL 1.1 entailment-regimes suite)</small>' \
    "$TAB_ENTAIL_PASS" "$TAB_ENTAIL_FAIL" "$TAB_ENTAIL_TOTAL")
fi
# Phase 2.3 — DL catalog rows (generic, loop-driven).
emit_catalog_rows () {
  # $1 = prefix (e.g. OWL_TPE), $2 = catalog short label (e.g. type-PosEnt)
  local prefix="$1" label="$2"
  # Regime tag (RL|DL) captured by extract_owl_scores from the log header,
  # rendered on every row so the dashboard never silently mixes regimes.
  local reg_var="${prefix}_REGIME"
  local reg="${!reg_var:-RL}"
  local types_with_short="PositiveEntailmentTests:PE NegativeEntailmentTests:NE ConsistencyTests:Cons InconsistencyTests:Inc"
  for entry in $types_with_short; do
    local t="${entry%%:*}" short="${entry##*:}"
    local p_var="${prefix}_${t}_PRESENT"
    local present="${!p_var}"
    [ "${present:-0}" -eq 1 ] || continue
    local pass_var="${prefix}_${t}_PASS"
    local fail_var="${prefix}_${t}_FAIL"
    local total_var="${prefix}_${t}_TOTAL"
    emit_owl_bar_row "$label $short [$reg]" "${!pass_var}" "${!fail_var}" "${!total_var}"
  done
}
OWL_DL_ROWS=$( {
  emit_catalog_rows OWL_TPE   "type-PosEnt"
  emit_catalog_rows OWL_TNE   "type-NegEnt"
  emit_catalog_rows OWL_TCON  "type-Cons"
  emit_catalog_rows OWL_TINC  "type-Inc"
  emit_catalog_rows OWL_EL    "profile-EL"
  emit_catalog_rows OWL_QL    "profile-QL"
  emit_catalog_rows OWL_SEMDL "sem-Direct"
  # syntax-dl species identification (2026-07-10): its score line has its
  # own shape (SpeciesTests, not the four entailment/consistency types),
  # so it is scraped separately above rather than via extract_owl_scores.
  if [ "$OWL_SYNDL_PRESENT" -eq 1 ]; then
    emit_owl_bar_row "syntax-dl species DL-vs-FULL [syntactic]" \
      "$OWL_SYNDL_PASS" "$OWL_SYNDL_FAIL" "$OWL_SYNDL_TOTAL"
  fi
} )

# RIF Core dedicated row (Phase 2.3c).
RIF_ROW=""
if [ "$RIF_PRESENT" -eq 1 ]; then
  RIF_ROW=$(emit_owl_bar_row "RIF Core" "$RIF_PASS" "$RIF_FAIL" "$RIF_TOTAL")
fi

# Deferred-category counts are the `<test:TestCase>` occurrences in each
# vendored OWL 2 Test Cases catalog file (Agent D scoping on 2026-04-24).
# Compute fresh so the numbers never go stale.
OWL_DIR="$SCRIPT_DIR/../../third_party/testing/owl"
count_testcases () {
  local f="$1"
  if [ -f "$f" ]; then
    grep -c "test:TestCase" "$f" 2>/dev/null || echo 0
  else
    echo 0
  fi
}
OWL_EL_N=$(count_testcases "$OWL_DIR/profile-EL.rdf")
OWL_QL_N=$(count_testcases "$OWL_DIR/profile-QL.rdf")
OWL_RL_CATALOG_N=$(count_testcases "$OWL_DIR/profile-RL.rdf")
OWL_SEMDL_N=$(count_testcases "$OWL_DIR/semantics-direct.rdf")
OWL_SYNDL_N=$(count_testcases "$OWL_DIR/syntax-dl.rdf")
OWL_TPE_N=$(count_testcases "$OWL_DIR/type-positive-entailment.rdf")
OWL_TNE_N=$(count_testcases "$OWL_DIR/type-negative-entailment.rdf")
OWL_TCON_N=$(count_testcases "$OWL_DIR/type-consistency.rdf")
OWL_TINC_N=$(count_testcases "$OWL_DIR/type-inconsistency.rdf")

emit_owl_skip_row () {
  local name="$1" count="$2" reason="$3"
  local css_class="${4:-grey}"
  cat <<ROW
  <details class="suite-node ${css_class}">
    <summary><span class="suite-name">${name}</span><span class="suite-numbers">not run &mdash; ${count} tests</span><span class="dot ${css_class}"></span></summary>
    <div class="suite-body">
      <div class="meter"><div class="seg seg-skip" style="width:100%"></div></div>
      <p class="suite-prov">${reason}</p>
    </div>
  </details>
ROW
}

# Note (2026-05-08, updated 2026-07-10): the W3C SPARQL 1.1
# entailment-regime suite (live score in the SPARQL section above —
# never hardcode it here, it has gone stale in this very comment
# twice) is the **live testbed for Tableau materialisation**.
# parent4/5/6/7 + simple7/8 + sparqldl-01..12 + many-others are
# OWL-DL queries on the Tableau codepath. The 2026-07-09 strict
# runner-integrity comparison exposed engine-side bugs lenient
# comparison had hidden (#236 variable leak, ASK-boolean gaps);
# task #100 fixed all but the RIF import-profile materialisation
# gap (rif04, see the ledger's SPARQL row for what remains).
# The "semantics-direct" catalog below IS wired through owl_runner
# (--regime dl, Phase 2.3d).
OWL_SKIP_ROWS=""
# Most catalog skip-rows above (profile-EL, profile-QL,
# semantics-direct, type-*) were retired 2026-05-08 when their
# runner wiring landed (Phase 2.1-2.3). The catalogs now have live
# scored bars in the OWL panel.
#
# The last catalog skip-row (syntax-dl) was retired 2026-07-10 when the
# OWL2_SyntaxDL species checker landed — syntax-dl now has a live scored
# bar in the OWL panel (see OWL_DL_ROWS above). emit_owl_skip_row stays
# for the next unwired suite.
# RL-RDF-rules-tests.rdf (the per-rule attribution catalog) and
# all.rdf (an aggregator) are intentionally skipped — they're not
# independent test sets.
#
# GeoSPARQL and DID used to have placeholder "roadmap" rows here. Both
# now have live scored suite nodes elsewhere on the page (GeoSPARQL
# under "SPARQL extras" and the F* engines family; DID under its own
# W3C Recommendations node) — this OWL panel is OWL 2 only, per the
# owner's 2026-07-10 directive that it stop listing non-OWL suites.
# CSVW, ShEx, JSON-LD 1.1, VC 2.0, and RML are likewise scored in their
# own families, not here.

# --- RDFC-1.0 subsection (folded into the RDF 1.1 core family) ----------
# RDFC-1.0 (W3C RDF Dataset Canonicalization 1.0) is a separate W3C
# suite with its own denominator, surfaced as a subsection inside the
# "RDF 1.1 core" family rather than its own top-level section — same
# spec family (RDF graph-level semantics), just a different corpus.
# Baseline 2026-07-05 (wave 8): HFDQ + full HNDQ permutation
# enumeration lands, Map tests compared structurally, NegEval checked
# against an HNDQ work budget — the suite reads 86 pass, 0 fail (of
# 86), not the earlier "Map is STUB" state this prose used to say.
if [ "$RDFC10_PRESENT" -ne 1 ]; then
  RDFC10_PASS=0; RDFC10_FAIL=0; RDFC10_SKIP=0; RDFC10_TOTAL=0
fi
RDFC10_ROW=$(emit_owl_bar_row "RDFC-1.0 (eval + Map + NegEval)" "$RDFC10_PASS" "$RDFC10_FAIL" "$RDFC10_TOTAL")
RDFC10_HTML=$(cat <<RDFCEOF
  <h3 class="rec-subhead"><a href="https://www.w3.org/TR/rdf-canon/" target="_blank" rel="noopener">RDF Dataset Canonicalization (RDFC-1.0)</a></h3>
${RDFC10_ROW}
  <p class="suite-prov">
    Runner: <code>bin/rdfc10-runner</code> (<code>bin/linux-x86_64/rdfc10_runner</code>) &middot;
    Suite: <code>third_party/testing/rdf-canon/</code> &middot;
    Algorithm: F&#42; <code>formal/fstar/RDF.Canonical.fst</code> (Hash First Degree Quads +
    full Hash N-Degree Quads permutation enumeration), verified with no
    <code>--lax</code> and no <code>--admit_smt_queries</code>. Eval tests compare the
    canonical N-Quads form bytewise; Map tests compare the bnode&rarr;canonical-id
    mapping structurally; NegEval tests are bounded by an HNDQ work budget.
  </p>
RDFCEOF
)

OWL_TOTAL_UNIVERSE=$(( OWL_TOTAL + ${OWL_EL_N:-174} + ${OWL_QL_N:-130} + ${OWL_SEMDL_N:-976} + ${OWL_SYNDL_N:-646} + ${OWL_TPE_N:-412} + ${OWL_TNE_N:-46} + ${OWL_TCON_N:-708} + ${OWL_TINC_N:-256} ))
if [ "$OWL_TOTAL_UNIVERSE" -gt 0 ]; then
  OWL_UNIVERSE_PCT=$(awk -v p="$OWL_PASS" -v t="$OWL_TOTAL_UNIVERSE" 'BEGIN{printf "%.1f", (p/t)*100}')
else
  OWL_UNIVERSE_PCT="0"
fi

OWL_HTML=$(cat <<OWLEOF
<p class="fam-subhead">OWL 2 <span class="inline-numbers">${OWL_PASS}+ pass via owl_runner across 8 catalogs (profile-RL/EL/QL + 4 DL + syntax-dl species) &middot; live scoring</span></p>
<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">
  <strong>Scope.</strong> The OWL 2 W3C Test Cases catalog (~${OWL_TOTAL_UNIVERSE}
  <code>test:TestCase</code> entries across 9 categories) is vendored
  under <code>third_party/testing/owl/</code>. As of Phase 2.3
  (2026-05-08), <strong>seven catalogs</strong> run live through
  <code>owl_runner</code> with PositiveEntailment / NegativeEntailment /
  Consistency / Inconsistency scoring: <code>profile-RL.rdf</code>,
  <code>profile-EL.rdf</code>, <code>profile-QL.rdf</code>,
  <code>type-positive-entailment.rdf</code>,
  <code>type-negative-entailment.rdf</code>,
  <code>type-consistency.rdf</code>, <code>type-inconsistency.rdf</code>,
  and <code>semantics-direct.rdf</code>. The ninth catalog
  (<code>syntax-dl.rdf</code>) scores through the F\*
  <code>OWL2.SyntaxDL</code> species checker (its row appears above).
</p>
<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">
  <strong>Tableau on the live codepath.</strong> The F\*
  <code>Tableau.tableau_materialise</code> module (0
  <code>assume val</code>, 0 <code>--lax</code>) drives the SPARQL
  entailment regime codepath via <code>w3c_runner.ml</code>:
  parent4/5/6/7, simple7/8, sparqldl-01…12, etc. — the
  <strong>SPARQL 1.1 Entailment Regimes row above</strong>
  passes (see its live score) because Tableau drives the membership
  check. Phase 2.3d (2026-07-09) wires the same Tableau
  materialisation into <code>owl_runner</code> via
  <code>--regime dl</code>: each DL catalog row below is tagged
  <code>[DL]</code> (Tableau) or <code>[RL]</code> (Datalog closure)
  so the two regimes are never silently mixed. DL runs RL-closure
  &rarr; <code>tableau_materialise</code> &rarr; RL-closure, falling
  back to the RL closure on a per-test cap-trip, so every DL row
  scores &ge; its RL baseline. Tableau is positive-sound, so the
  RL&rarr;DL flips it produces are gains (type-inconsistency and
  positive-entailment rows moved up), never wrong answers.
</p>
<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">
  <strong>Pass-rate context.</strong> Across the scored catalogs,
  the bulk of remaining failures fall into two categories:
  (1) tests that use OWL Functional-Style Syntax (not RDF/XML)
  trigger <code>FAIL/no-premise</code> — these need fuller FSS parser
  coverage before scoring is meaningful; (2) Inconsistency /
  entailment failures beyond the tableau's decided fragment. The
  refutation side landed 2026-07-10 (<code>Tableau.Refute.fst</code>:
  NNF, lazy TBox unfolding, disjunction branching, ∃-witnesses,
  complement / min-max / counting / bottom-property clashes — each
  <code>Some false</code> carries a per-rule Direct Semantics
  soundness argument, and the DL rows below score it), so what
  remains on the inconsistency side is the undecided residue:
  nominals (<code>owl:oneOf</code>), datatype facets, inverse-role
  interaction, and searches that exhaust the refuter's linear work
  budget (deep propositional encodings) — indeterminate results fall
  back to the RL verdict, never below it.
</p>
<div class="suites">
  ${TABLEAU_ROW}
  $(emit_owl_bar_row "profile-RL PosEnt" "$OWL_PASS" "$OWL_FAIL" "$OWL_TOTAL")
  ${OWL_NEG_ROW}
  ${OWL_CONS_ROW}
  ${OWL_INC_ROW}
  ${OWL_DL_ROWS}
${OWL_SKIP_ROWS}</div>
<p style="margin: 0.3em 0 1em; color: var(--muted); font-size: 0.85em;">
  <strong>OWL 2 (W3C conformance):</strong>
  We vendor the full W3C OWL 2 Test Cases at
  <code>third_party/testing/owl/</code> (10 catalog files, ~2500
  <code>test:TestCase</code> entries after overlap). After Phase 2.3
  (2026-05-08), all 8 main catalogs run live through
  <code>owl_runner</code>: 7 with PE/NE/Cons/Inc scoring, plus (as of
  2026-07-10) <code>syntax-dl.rdf</code> with species identification.
  The runner applies <code>owl_rl_closure_with_reflexivity</code>
  (fuel 100) and for entailment tests checks the conclusion&rsquo;s
  triples against the closure (relaxed bnode match); for consistency
  tests it consults <code>RDF_Graph_Executable.is_inconsistent</code>
  against the same closure; for species identification it consults the
  syntax-directed F&#42; checker <code>OWL2.SyntaxDL.species_is_dl</code>
  (no reasoning) over premise + conclusion documents.
  Other suites once listed here as roadmap items — GeoSPARQL, JSON-LD 1.1,
  CSVW, ShEx, DID, VC, RML — now have live scored suite nodes of their
  own elsewhere on this page.
</p>
OWLEOF
)

# --- Parse + serialize throughput (optional; fail-soft) ---------------------
# Produced by tools/bench-parse-serialize.sh, which runs against the
# committed binary and has no toolchain dependency. This script only
# *includes* the fragment verbatim if present -- it does no JSON
# parsing of its own, so a missing or stale file degrades to simply
# omitting the section rather than breaking report generation.
PERF_FRAGMENT="$OUTPUT_DIR/perf-parse-serialize.fragment.html"
if [ -f "$PERF_FRAGMENT" ]; then
  PERF_SECTION_HTML=$(cat "$PERF_FRAGMENT")
else
  PERF_SECTION_HTML=""
fi

[ -n "$GIT_SUBJECT" ] && GIT_SUBJECT_LINE=" — &ldquo;${GIT_SUBJECT}&rdquo;" || GIT_SUBJECT_LINE=""

# =============================================================================
# Family sections (2026-07-05 dashboard redesign) ----------------------------
# Every standards suite this project measures is grouped into one of eight
# families (RDF 1.1 core, SPARQL 1.1, Reasoning: RDFS/OWL 2, Shapes, Rules,
# Mapping, JSON-LD 1.1, Verifiable Credentials 2.0), each rendered as a
# <section class="family <status>"> card with a headline roll-up, a
# collapsible (native <details>, no JS required) list of per-suite rows, and
# a one-line provenance (runner binary + vendored suite dir) under each row.
# Status colour is consistent everywhere: green = full pass; amber = partial
# with every residual fail diagnosed in writing (a link is attached to the
# row); grey = not measured this run, or genuinely out of scope. See the
# legend rendered directly above the first family section.
# =============================================================================
GITHUB_BLOB_BASE="https://github.com/danbri/factoidal/blob/${GIT_BRANCH}"

# family_suite_row — shared row renderer for the newer suites (SHACL, ShEx,
# JSON-LD, RML, RIF Core, VC, ...). Renders as one collapsible
# <details class="suite-node"> (owner directive 2026-07-10: one
# collapsible node per checkable suite, default-collapsed, summary shows
# name + labelled pass/fail/skip + a status dot). Handles present=0 as an
# explicit "not measured this run" grey row (never a fabricated 0-pass
# number), and carries a one-line <p class="suite-prov"> in the body with
# the runner + vendored suite dir, plus an optional diagnosis line shown
# only when the suite has a fail.
family_suite_row () {
  local name="$1" pass="$2" fail="$3" skip="$4" total="$5" present="$6" prov="$7" diag="${8:-}" notmeasured="${9:-not measured this run}"
  local cls numbers meter diag_html="" condensed
  if [ "$present" -ne 1 ] || [ "$total" -eq 0 ]; then
    cls="grey"
    numbers="$notmeasured"
    condensed="$notmeasured"
    meter='<div class="meter"><div class="seg seg-skip" style="width:100%"></div></div>'
  else
    numbers="${pass} pass, ${fail} fail, ${skip} skip (out of ${total})"
    condensed=$(condensed_numbers "$pass" "$fail" "$skip" "$total")
    meter=$(meter_segments "$pass" "$fail" "$skip" "$total")
    cls=$(status_for "$fail" 1)
    if [ "$fail" -gt 0 ] && [ -n "$diag" ]; then diag_html="<p class=\"suite-diag\">${diag}</p>"; fi
  fi
  cat <<ROW
      <details class="suite-node ${cls}">
        <summary><span class="suite-name">${name}</span><span class="suite-numbers">${condensed}</span><span class="dot ${cls}"></span></summary>
        <div class="suite-body">
          ${meter}
          <p class="suite-numbers-full">${numbers}</p>
          <p class="suite-prov">${prov}</p>
          ${diag_html}
        </div>
      </details>
ROW
}

# family_section — the outer card for one spec/suite family, now itself a
# collapsible <details class="family-node"> (2026-07-10 second pass: the
# first pass left families as always-open cards, which is what read as
# "stacked padded cards" rather than a tree on a phone). Collapsed by
# default; the summary line carries the family name, a condensed
# pass/fail/skip score, an optional "N of M suites" fraction (the
# denominator M counts suites the spec family DEFINES, run or not — see
# $11), an optional gap-count badge, and a status dot. Expanding it
# reveals the full prose headline, the per-suite rows (already their own
# collapsible <details class="suite-node">, from family_suite_row /
# emit_suite_rows / emit_owl_bar_row above), any extra footnote prose,
# and a "Remaining work" list sourced from the suite manifests'
# `remaining:` YAML field ($12) — or, when that list is empty AND the
# aggregate has zero fails, a "complete against the vendored suites"
# line. A family with fails but no populated `remaining:` yet renders
# neither claim, rather than fabricate either one.
#
# Args: id title status headline body [footnote] [agg_pass agg_fail
#       agg_skip agg_total] [suite_fraction] [remaining_lines]
family_section () {
  local id="$1" title="$2" fstatus="$3" headline="$4" body="$5" footnote="${6:-}"
  local agg_pass="${7:-0}" agg_fail="${8:-0}" agg_skip="${9:-0}" agg_total="${10:-0}"
  local suite_fraction="${11:-}" remaining_lines="${12:-}"

  local score_html
  if [ "$agg_total" -gt 0 ] 2>/dev/null; then
    score_html=$(condensed_numbers "$agg_pass" "$agg_fail" "$agg_skip" "$agg_total")
  else
    score_html="not measured this run"
  fi
  [ -n "$suite_fraction" ] && score_html="${score_html} &middot; ${suite_fraction} suites"

  local gap_count=0 remaining_html=""
  local trimmed; trimmed=$(printf '%s' "$remaining_lines" | tr -d '[:space:]')
  if [ -n "$trimmed" ]; then
    local items="" rline esc
    while IFS= read -r rline; do
      [ -z "$rline" ] && continue
      gap_count=$((gap_count + 1))
      esc=$(printf '%s' "$rline" | sed -E 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g')
      items+="        <li>${esc}</li>"$'\n'
    done <<<"$remaining_lines"
    remaining_html=$(cat <<REM
    <div class="remaining">
      <p class="remaining-title">Remaining work</p>
      <ul>
${items}      </ul>
    </div>
REM
)
  elif [ "$agg_total" -gt 0 ] 2>/dev/null && [ "$agg_fail" -eq 0 ] 2>/dev/null; then
    remaining_html='    <p class="remaining-complete">Complete against the vendored suites.</p>'
  fi

  local badge_html=""
  if [ "$gap_count" -gt 0 ]; then
    local gap_word="gaps"
    [ "$gap_count" -eq 1 ] && gap_word="gap"
    badge_html="<span class=\"gap-badge\">${gap_count} ${gap_word}</span>"
  fi

  cat <<SEC
<details class="family-node ${fstatus}" id="${id}">
  <summary>
    <span class="fam-name">${title}</span>
    <span class="fam-score">${score_html}</span>
    ${badge_html}
    <span class="dot ${fstatus}"></span>
  </summary>
  <div class="family-body">
    <p class="fam-headline ${fstatus}">${headline}</p>
    <div class="suites">
${body}
    </div>
    ${footnote}
${remaining_html}
  </div>
</details>
SEC
}

# group_section — top-level standards-status grouping (owner directive
# 2026-07-10): one collapsible node per group, open by default, wrapping
# a fixed-order list of family_section cards.
group_section () {
  local id="$1" title="$2" body="$3"
  cat <<GRP
<details class="group-section" id="${id}" open>
  <summary class="group-summary">${title}</summary>
  <div class="group-body">
${body}
  </div>
</details>
GRP
}

# --- RDF 1.1 core: syntaxes + semantics --------------------------------------
# rdf-mt carries the RDFS entailment tests (RDF Schema 1.1 shares the RDF
# 1.1 Semantics suite). RDFC-1.0 is a separate 2024 Recommendation and
# renders as its own family below (owner directive 2026-07-10).
RDFCORE_PASS=$RDF_PASS
RDFCORE_FAIL=$RDF_FAIL
RDFCORE_SKIP=$RDF_SKIP
RDFCORE_TOTAL=$RDF_TOTAL
RDFCORE_STATUS=$(status_for "$RDFCORE_FAIL" 1)
RDFCORE_HEADLINE="${RDFCORE_PASS} pass, ${RDFCORE_FAIL} fail, ${RDFCORE_SKIP} skip (of ${RDFCORE_TOTAL}) across N-Triples, Turtle, N-Quads, TriG, RDF/XML, and RDF 1.1 Semantics (rdf-mt, which carries the RDFS entailment tests)."
RDFCORE_BODY=$(printf '%s\n' "$RDF_ROWS_HTML")
RDFCORE_REMAINING=$(family_remaining rdf-xml)
RDFCORE_HTML=$(family_section "rdf-core" "RDF 1.1 core" "$RDFCORE_STATUS" "$RDFCORE_HEADLINE" "$RDFCORE_BODY" "$RDF_FAILURE_DETAIL_HTML" \
  "$RDFCORE_PASS" "$RDFCORE_FAIL" "$RDFCORE_SKIP" "$RDFCORE_TOTAL" "" "$RDFCORE_REMAINING")

# --- RDFC-1.0 (RDF Dataset Canonicalization, W3C Recommendation 2024) -------
RDFC10FAM_STATUS=$(status_for "$RDFC10_FAIL" 1)
RDFC10FAM_HEADLINE="${RDFC10_PASS} pass, ${RDFC10_FAIL} fail, ${RDFC10_SKIP} skip (of ${RDFC10_TOTAL}) on the W3C rdf-canon suite."
RDFC10FAM_HTML=$(family_section "rdfc10" "RDF Dataset Canonicalization (RDFC-1.0)" "$RDFC10FAM_STATUS" "$RDFC10FAM_HEADLINE" "$RDFC10_HTML" "" \
  "$RDFC10_PASS" "$RDFC10_FAIL" "$RDFC10_SKIP" "$RDFC10_TOTAL")

# --- SPARQL 1.1 ---------------------------------------------------------
SPARQL_STATUS=$(status_for "$SPARQL_FAIL" 1)
SPARQL_HEADLINE="${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip (of ${SPARQL_TOTAL}) across Query, Update, Protocol, Federated Query, Service Description, and Entailment Regimes."
SPARQL_REMAINING=$(family_remaining sparql11-protocol)
SPARQL_FAMILY_HTML=$(family_section "sparql11" "SPARQL 1.1" "$SPARQL_STATUS" "$SPARQL_HEADLINE" "$SPARQL_ROWS_HTML" "$SPARQL_FAILURE_DETAIL_HTML" \
  "$SPARQL_PASS" "$SPARQL_FAIL" "$SPARQL_SKIP" "$SPARQL_TOTAL" "" "$SPARQL_REMAINING")

# --- RDF 1.2 / SPARQL 1.2 (W3C Working Drafts, epic #305) ----------------
# Emerging next-revision suites: kept in their own Working-Drafts group
# (below), NOT under Recommendations, since 1.2 is not yet a Rec.
V12_FAMILY_HTML=""
if [ "$RDF12_PRESENT" -eq 1 ] || [ "$SPARQL12_PRESENT" -eq 1 ]; then
  V12_ROWS_HTML=$(
    emit_rec_subsection "RDF 1.2 (N-Triples / N-Quads / Turtle / TriG)" "https://www.w3.org/TR/rdf12-n-triples/" "$RDF12_SUITES"
    emit_rec_subsection "SPARQL 1.2 Query"                              "https://www.w3.org/TR/sparql12-query/"   "$SPARQL12_SUITES"
  )
  V12_PASS=$((RDF12_PASS + SPARQL12_PASS))
  V12_FAIL=$((RDF12_FAIL + SPARQL12_FAIL))
  V12_SKIP=$((RDF12_SKIP + SPARQL12_SKIP))
  V12_TOTAL=$((RDF12_TOTAL + SPARQL12_TOTAL))
  V12_STATUS=$(status_for "$V12_FAIL" 1)
  V12_HEADLINE="RDF 1.2 ${RDF12_PASS} pass, ${RDF12_FAIL} fail (of ${RDF12_TOTAL}); SPARQL 1.2 ${SPARQL12_PASS} pass, ${SPARQL12_FAIL} fail (of ${SPARQL12_TOTAL}). Triple terms &lt;&lt;( s p o )&gt;&gt;, reifiers, annotations, VERSION, directional literals — parsed and queried live in the browser demo. Still open: RDF/XML 1.2, RDF 1.2 canonicalization (86) and entailment (74), and a handful of SPARQL 1.2 eval cases."
  V12_FAMILY_HTML=$(family_section "rdf-sparql-12" "RDF 1.2 / SPARQL 1.2" "$V12_STATUS" "$V12_HEADLINE" "$V12_ROWS_HTML" "" \
    "$V12_PASS" "$V12_FAIL" "$V12_SKIP" "$V12_TOTAL")
fi

# --- Reasoning: RDFS / OWL 2 ---------------------------------------------
# OWL_HTML already carries its own rich prose (scope + pass-rate context)
# from the earlier catalog-by-catalog wiring; wrap it as this family's
# footnote rather than re-deriving a numeric aggregate across catalogs
# whose test-type buckets (Positive/Negative/Consistency/Inconsistency)
# aren't directly summable into one pass/fail/skip/total the way the
# newer suites are.
OWL_FAMILY_STATUS=$(status_for "$OWL_FAIL" "$OWL_PRESENT")
OWL_FAMILY_HEADLINE="profile-RL PositiveEntailmentTests: ${OWL_PASS} pass, ${OWL_FAIL} fail (of ${OWL_TOTAL}); six further OWL 2 catalogs (NegEnt/Cons/Inc + 4 DL catalogs) scored below, RIF Core scored in its own family."
OWL_SKIP_FOR_SCORE=$((OWL_TOTAL - OWL_PASS - OWL_FAIL))
[ "$OWL_SKIP_FOR_SCORE" -lt 0 ] && OWL_SKIP_FOR_SCORE=0
OWL_REMAINING=$(family_remaining owl-profile-rl)
OWL_FAMILY_HTML=$(family_section "owl2" "OWL 2" "$OWL_FAMILY_STATUS" "$OWL_FAMILY_HEADLINE" "$OWL_HTML" "" \
  "$OWL_PASS" "$OWL_FAIL" "$OWL_SKIP_FOR_SCORE" "$OWL_TOTAL" "" "$OWL_REMAINING")

# --- Shapes: SHACL (W3C Recommendation) and ShEx (W3C CG spec) ------------
# Soft rivals, kept as separate-but-adjacent nodes (owner directive
# 2026-07-10) rather than one combined family: SHACL is a Recommendation
# (W3C Recommendations group), ShEx is a Community Group specification
# (CG/Notes/Submissions group), so a strict standards-status tree puts
# them in different top-level groups. Each node's body carries a
# cross-reference line pointing at the other, so a reader browsing one
# still finds its rival.
read -r SHACL_FAM_PASS SHACL_FAM_FAIL SHACL_FAM_SKIP SHACL_FAM_TOTAL SHACL_FAM_ANY <<< "$(sum_family "SHACL_CORE SHACL_SPARQL")"
SHACL_STATUS=$(status_for "$SHACL_FAM_FAIL" "$SHACL_FAM_ANY")
if [ "$SHACL_FAM_ANY" -eq 1 ]; then
  SHACL_HEADLINE="${SHACL_FAM_PASS} pass, ${SHACL_FAM_FAIL} fail, ${SHACL_FAM_SKIP} skip (out of ${SHACL_FAM_TOTAL}) across SHACL Core and SHACL SPARQL-based Constraints."
else
  SHACL_HEADLINE="Not measured this run."
fi
SHACL_BODY=$(
  family_suite_row "SHACL Core" "$SHACL_CORE_PASS" "$SHACL_CORE_FAIL" "$SHACL_CORE_SKIP" "$SHACL_CORE_TOTAL" "$SHACL_CORE_PRESENT" \
    "Runner: <code>bin/shacl-runner</code> (<code>bin/linux-x86_64/shacl_runner</code>) &middot; Suite: <code>third_party/testing/shacl/data-shapes-test-suite/tests/core/</code>"
  family_suite_row "SHACL SPARQL-based Constraints" "$SHACL_SPARQL_PASS" "$SHACL_SPARQL_FAIL" "$SHACL_SPARQL_SKIP" "$SHACL_SPARQL_TOTAL" "$SHACL_SPARQL_PRESENT" \
    "Runner: <code>bin/shacl-runner</code> (<code>bin/linux-x86_64/shacl_runner tests/sparql/manifest.ttl</code>) &middot; Suite: <code>third_party/testing/shacl/data-shapes-test-suite/tests/sparql/</code>"
)
SHACL_CROSSREF='<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">See also <a href="#shex">ShEx</a>, the other shapes-constraint language for RDF — a W3C Community Group specification, not a Recommendation.</p>'
SHACL_HTML=$(family_section "shacl" "SHACL (Shapes Constraint Language)" "$SHACL_STATUS" "$SHACL_HEADLINE" "$SHACL_BODY" "$SHACL_CROSSREF" \
  "$SHACL_FAM_PASS" "$SHACL_FAM_FAIL" "$SHACL_FAM_SKIP" "$SHACL_FAM_TOTAL" "" "$(family_remaining shacl-core shacl-sparql)")

# ShEx family = validation manifest + negativeSyntax (ShExC grammar-
# reject) suites; family counts are their sum.
SHEX_FAM_PASS=$(( SHEX_PASS + SHEXNEG_PASS ))
SHEX_FAM_FAIL=$(( SHEX_FAIL + SHEXNEG_FAIL ))
SHEX_FAM_SKIP=$(( SHEX_SKIP + SHEXNEG_SKIP ))
SHEX_FAM_TOTAL=$(( SHEX_TOTAL + SHEXNEG_TOTAL ))
SHEX_FAM_PRESENT=$(( SHEX_PRESENT | SHEXNEG_PRESENT ))
SHEX_STATUS=$(status_for "$SHEX_FAM_FAIL" "$SHEX_FAM_PRESENT")
if [ "$SHEX_PRESENT" -eq 1 ] && [ "$SHEXNEG_PRESENT" -eq 1 ]; then
  SHEX_HEADLINE="Validation: ${SHEX_PASS} pass, ${SHEX_FAIL} fail, ${SHEX_SKIP} skip (out of ${SHEX_TOTAL}); negativeSyntax (ShExC grammar-reject): ${SHEXNEG_PASS} pass, ${SHEXNEG_FAIL} fail (out of ${SHEXNEG_TOTAL})."
elif [ "$SHEX_PRESENT" -eq 1 ]; then
  SHEX_HEADLINE="${SHEX_PASS} pass, ${SHEX_FAIL} fail, ${SHEX_SKIP} skip (out of ${SHEX_TOTAL}) on the shexSpec/shexTest validation manifest."
else
  SHEX_HEADLINE="Not measured this run."
fi
SHEX_BODY=$(
  family_suite_row "ShEx Validation" "$SHEX_PASS" "$SHEX_FAIL" "$SHEX_SKIP" "$SHEX_TOTAL" "$SHEX_PRESENT" \
    "Runner: <code>bin/shex-runner</code> (<code>bin/linux-x86_64/shex_runner</code>) &middot; Suite: <code>third_party/testing/shex/</code> (shexSpec/shexTest, ShExJ-first)" \
    "<a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/shex.yaml\" target=\"_blank\" rel=\"noopener\">diagnosis: the 1 mismatch is an upstream fixture defect (start2RefS2.json has predicate p1 where the canonical ShExC schema has p2), not an engine bug</a>"
  family_suite_row "ShEx negativeSyntax (ShExC grammar-reject)" "$SHEXNEG_PASS" "$SHEXNEG_FAIL" "$SHEXNEG_SKIP" "$SHEXNEG_TOTAL" "$SHEXNEG_PRESENT" \
    "Runner: <code>bin/shex-runner --negative-syntax</code> &middot; Suite: <code>third_party/testing/shex/negativeSyntax/</code> — every fixture MUST fail to parse; pass = <code>Parser.ShExC</code> (F*) rejects it"
)
SHEX_CROSSREF='<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">See also <a href="#shacl">SHACL</a>, the other shapes-constraint language for RDF — a W3C Recommendation.</p>'
SHEX_HTML=$(family_section "shex" "ShEx (Shape Expressions)" "$SHEX_STATUS" "$SHEX_HEADLINE" "$SHEX_BODY" "$SHEX_CROSSREF" \
  "$SHEX_FAM_PASS" "$SHEX_FAM_FAIL" "$SHEX_FAM_SKIP" "$SHEX_FAM_TOTAL" "" "$(family_remaining shex shex-negative-syntax)")

# --- Rules: RIF Core -------------------------------------------------------
RULES_STATUS=$(status_for "$RIFCORE_COMBINED_FAIL" "$RIFCORE_COMBINED_PRESENT")
if [ "$RIFCORE_COMBINED_PRESENT" -eq 1 ]; then
  RULES_HEADLINE="${RIFCORE_COMBINED_PASS} pass, ${RIFCORE_COMBINED_FAIL} fail, ${RIFCORE_COMBINED_SKIP} skip (of ${RIFCORE_COMBINED_TOTAL}) — Part 1 (4 vendored SPARQL-manifest cases) + Part 2 (46-test W3C RIF Core dialect corpus)."
else
  RULES_HEADLINE="Not measured this run."
fi
RULES_BODY=$(
  family_suite_row "RIF Core — combined (Part 1 + Part 2)" "$RIFCORE_COMBINED_PASS" "$RIFCORE_COMBINED_FAIL" "$RIFCORE_COMBINED_SKIP" "$RIFCORE_COMBINED_TOTAL" "$RIFCORE_COMBINED_PRESENT" \
    "Runner: <code>bin/rif-runner</code> (<code>bin/linux-x86_64/rif_runner</code>) &middot; Suites: <code>third_party/testing/rif/tc/</code> + <code>third_party/testing/rif-core-suite/</code>" \
    "<a href=\"${GITHUB_BLOB_BASE}/bin/rif-runner/README.md\" target=\"_blank\" rel=\"noopener\">diagnosis: 1 corpus data defect (malformed xsd:string IRI in the official W3C zip) + 3 labelled engine KNOWN-GAPs, see bin/rif-runner/README.md</a>"
  family_suite_row "RIF Core — Part 1 (4 vendored SPARQL-manifest cases)" "$RIFCORE_PART1_PASS" "$RIFCORE_PART1_FAIL" "$RIFCORE_PART1_SKIP" "$RIFCORE_PART1_TOTAL" "$RIFCORE_PART1_PRESENT" \
    "Runner: <code>bin/rif-runner</code> &middot; Suite: <code>third_party/testing/rif/tc/</code> (the same 4 cases are also scored independently as the &ldquo;RIF Core&rdquo; row under SPARQL 1.1 Entailment Regimes above, via <code>w3c_runner</code>'s entailment dispatch — both pipelines agree)"
  family_suite_row "RIF Core — Part 2 (W3C Core_v1.22 corpus)" "$RIFCORE_PART2_PASS" "$RIFCORE_PART2_FAIL" "$RIFCORE_PART2_SKIP" "$RIFCORE_PART2_TOTAL" "$RIFCORE_PART2_PRESENT" \
    "Runner: <code>bin/rif-runner</code> &middot; Suite: <code>third_party/testing/rif-core-suite/Core_v1.22/Approved/</code>" \
    "<a href=\"${GITHUB_BLOB_BASE}/docs/claude-rules/scope.md\" target=\"_blank\" rel=\"noopener\">diagnosis: docs/claude-rules/scope.md RIF section — every skip names the exact missing builtin/feature</a>"
)
RULES_HTML=$(family_section "rules" "Rules: RIF Core" "$RULES_STATUS" "$RULES_HEADLINE" "$RULES_BODY" "" \
  "$RIFCORE_COMBINED_PASS" "$RIFCORE_COMBINED_FAIL" "$RIFCORE_COMBINED_SKIP" "$RIFCORE_COMBINED_TOTAL" "" "$(family_remaining rif)")

# --- GRDDL (W3C Recommendation) --------------------------------------------
# Scraped and reported in latest.json/latest.csv since the 2026-07-05 wave
# but never rendered as a page section — added here (owner directive
# 2026-07-10) so a measured suite is never invisible on the page.
GRDDL_STATUS=$(status_for "$GRDDL_FAIL" "$GRDDL_PRESENT")
if [ "$GRDDL_PRESENT" -eq 1 ]; then
  GRDDL_HEADLINE="${GRDDL_PASS} pass, ${GRDDL_FAIL} fail, ${GRDDL_SKIP} skip (out of ${GRDDL_TOTAL}) on the local GRDDL Stage 1 subset."
else
  GRDDL_HEADLINE="Not measured this run."
fi
GRDDL_BODY=$(
  family_suite_row "GRDDL Stage 1 (local subset)" "$GRDDL_PASS" "$GRDDL_FAIL" "$GRDDL_SKIP" "$GRDDL_TOTAL" "$GRDDL_PRESENT" \
    "Runner: <code>bin/grddl-runner</code> (<code>bin/linux-x86_64/grddl_runner</code>) &middot; Suite: local subset of the GRDDL Test Cases" \
    "the fails are graph-mismatch cases in the local subset; the skips are fixtures that need a live network fetch of a transformation profile, out of scope for an offline conformance run"
)
GRDDL_HTML=$(family_section "grddl" "GRDDL" "$GRDDL_STATUS" "$GRDDL_HEADLINE" "$GRDDL_BODY" "" \
  "$GRDDL_PASS" "$GRDDL_FAIL" "$GRDDL_SKIP" "$GRDDL_TOTAL" "" "$(family_remaining grddl)")

# --- Mapping: RML (W3C Community Group) and CSVW (W3C Recommendation) -----
# Split into two families (owner directive 2026-07-10): CSVW csv2rdf is a
# W3C Recommendation, RML is a Knowledge Graph Construction Community
# Group specification — different standards-status groups on the tree.
read -r RML_FAM_PASS RML_FAM_FAIL RML_FAM_SKIP RML_FAM_TOTAL RML_FAM_ANY <<< "$(sum_family "RML RML_IO")"
RML_STATUS=$(status_for "$RML_FAM_FAIL" "$RML_FAM_ANY")
if [ "$RML_FAM_ANY" -eq 1 ]; then
  RML_HEADLINE="${RML_FAM_PASS} pass, ${RML_FAM_FAIL} fail, ${RML_FAM_SKIP} skip (out of ${RML_FAM_TOTAL}) across RML rml-core and RML rml-io source-tests."
else
  RML_HEADLINE="Not measured this run."
fi
RML_BODY=$(
  family_suite_row "RML rml-core" "$RML_PASS" "$RML_FAIL" "$RML_SKIP" "$RML_TOTAL" "$RML_PRESENT" \
    "Runner: <code>bin/rml-runner</code> (<code>bin/linux-x86_64/rml_runner</code>) &middot; Suite: <code>third_party/testing/rml-modules/rml-core/</code>"
  family_suite_row "RML rml-io (source-tests)" "$RML_IO_PASS" "$RML_IO_FAIL" "$RML_IO_SKIP" "$RML_IO_TOTAL" "$RML_IO_PRESENT" \
    "Runner: <code>bin/linux-x86_64/rml_runner --io</code> &middot; Suite: <code>third_party/testing/rml-modules/rml-io/</code> (RMLSTC0* source tests) &middot; rml-cc (content-container) has no row: the committed runner exposes no <code>--cc</code> mode yet (tracked with the rml program plan)" \
    "<a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-05-rml-program-plan.md\" target=\"_blank\" rel=\"noopener\">diagnosis: the fails/skips are rml-io logical-target (RMLTTC0*) and unsupported-source fixtures out of scope for the source-tests section — see the rml program plan</a>"
)
RML_HTML=$(family_section "mapping-rml" "RML (rml-core / rml-io)" "$RML_STATUS" "$RML_HEADLINE" "$RML_BODY" "" \
  "$RML_FAM_PASS" "$RML_FAM_FAIL" "$RML_FAM_SKIP" "$RML_FAM_TOTAL" "" "$(family_remaining rml)")

CSVW_STATUS=$(status_for "$CSVW2RDF_FAIL" "$CSVW2RDF_PRESENT")
if [ "$CSVW2RDF_PRESENT" -eq 1 ]; then
  CSVW_HEADLINE="${CSVW2RDF_PASS} pass, ${CSVW2RDF_FAIL} fail, ${CSVW2RDF_SKIP} skip (out of ${CSVW2RDF_TOTAL}) on the vendored csv2rdf corpus."
else
  CSVW_HEADLINE="Not measured this run."
fi
CSVW_BODY=$(
  family_suite_row "CSVW csv2rdf" "$CSVW2RDF_PASS" "$CSVW2RDF_FAIL" "$CSVW2RDF_SKIP" "$CSVW2RDF_TOTAL" "$CSVW2RDF_PRESENT" \
    "Runner: <code>bin/csvw-runner</code> (<code>bin/linux-x86_64/csvw_runner</code>) &middot; Suite: vendored W3C csv2rdf corpus (ToRdf / ToRdfWithWarnings / NegativeRdf)" \
    "<a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-05-csvw-program-plan.md\" target=\"_blank\" rel=\"noopener\">diagnosis: burn-down in progress — the CSVW program plan tracks the ToRdf / warnings / negative buckets; residual fails need full @context / metadata-merge processing</a>"
)
CSVW_HTML=$(family_section "csvw" "CSVW (CSV on the Web)" "$CSVW_STATUS" "$CSVW_HEADLINE" "$CSVW_BODY" "" \
  "$CSVW2RDF_PASS" "$CSVW2RDF_FAIL" "$CSVW2RDF_SKIP" "$CSVW2RDF_TOTAL" "" "$(family_remaining csvw)")

# --- JSON-LD 1.1 ------------------------------------------------------------
# Five directions now scored: toRdf (jsonld_runner) + fromRdf
# (jsonld_fromrdf_runner, 2026-07-09) + expand (jsonld_expand_runner,
# 2026-07-10) + compact (jsonld_compact_runner, 2026-07-10) + flatten
# (jsonld_flatten_runner, 2026-07-10).
read -r JSONLD_FAM_PASS JSONLD_FAM_FAIL JSONLD_FAM_SKIP JSONLD_FAM_TOTAL JSONLD_FAM_ANY <<< "$(sum_family "JSONLD JSONLD_FROMRDF JSONLD_EXPAND JSONLD_COMPACT JSONLD_FLATTEN")"
JSONLD_STATUS=$(status_for "$JSONLD_FAM_FAIL" "$JSONLD_FAM_ANY")
if [ "$JSONLD_FAM_ANY" -eq 1 ]; then
  JSONLD_FAMILY_HEADLINE="${JSONLD_FAM_PASS} pass, ${JSONLD_FAM_FAIL} fail, ${JSONLD_FAM_SKIP} skip (of ${JSONLD_FAM_TOTAL}) across the W3C JSON-LD 1.1 toRdf, fromRdf, expand, compact and flatten manifests."
else
  JSONLD_FAMILY_HEADLINE="Not measured this run."
fi
JSONLD_BODY=$(
  family_suite_row "JSON-LD 1.1 toRdf" "$JSONLD_PASS" "$JSONLD_FAIL" "$JSONLD_SKIP" "$JSONLD_TOTAL" "$JSONLD_PRESENT" \
    "Runner: <code>bin/jsonld-runner</code> (<code>bin/linux-x86_64/jsonld_runner</code>) &middot; Suite: <code>third_party/testing/json-ld/</code> (toRdf manifest)" \
    "<a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-05-docs-hub-plan.md\" target=\"_blank\" rel=\"noopener\">diagnosis: the 1 fail is the documented Ryu-class float-formatting case; the 6 skips are JSON-LD 1.0-only fixtures, out of scope for this 1.1 program</a>"
  family_suite_row "JSON-LD 1.1 fromRdf" "$JSONLD_FROMRDF_PASS" "$JSONLD_FROMRDF_FAIL" "$JSONLD_FROMRDF_SKIP" "$JSONLD_FROMRDF_TOTAL" "$JSONLD_FROMRDF_PRESENT" \
    "Runner: <code>bin/jsonld-fromrdf-runner</code> (<code>bin/linux-x86_64/jsonld_fromrdf_runner</code>) &middot; Suite: W3C JSON-LD 1.1 fromRdf manifest (Serialize RDF as JSON-LD)" \
    "<a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/jsonld-fromrdf.yaml\" target=\"_blank\" rel=\"noopener\">diagnosis: residual fails are the documented @native/list-container serialisation gaps — see the suite manifest</a>"
  family_suite_row "JSON-LD 1.1 expand" "$JSONLD_EXPAND_PASS" "$JSONLD_EXPAND_FAIL" "$JSONLD_EXPAND_SKIP" "$JSONLD_EXPAND_TOTAL" "$JSONLD_EXPAND_PRESENT" \
    "Runner: <code>bin/jsonld-expand-runner</code> (<code>bin/linux-x86_64/jsonld_expand_runner</code>) &middot; Suite: W3C JSON-LD 1.1 expand manifest (Expansion Algorithm)" \
    "<a href=\"${GITHUB_BLOB_BASE}/third_party/testing/json-ld/tests/expand-manifest.jsonld\" target=\"_blank\" rel=\"noopener\">diagnosis: residual fails are enumerated algorithm/option gaps (scoped @context, @container edge cases, error-code negatives) plus the JSON-LD 1.0-only skips — see the commit for the per-bucket breakdown</a>"
  family_suite_row "JSON-LD 1.1 compact" "$JSONLD_COMPACT_PASS" "$JSONLD_COMPACT_FAIL" "$JSONLD_COMPACT_SKIP" "$JSONLD_COMPACT_TOTAL" "$JSONLD_COMPACT_PRESENT" \
    "Runner: <code>bin/jsonld-compact-runner</code> (<code>bin/linux-x86_64/jsonld_compact_runner</code>) &middot; Suite: W3C JSON-LD 1.1 compact manifest (Compaction Algorithm)" \
    "<a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/jsonld-compact.yaml\" target=\"_blank\" rel=\"noopener\">diagnosis: residual fails are enumerated Compaction-Algorithm gaps — see the suite manifest and the landing commit for the per-bucket breakdown</a>"
  family_suite_row "JSON-LD 1.1 flatten" "$JSONLD_FLATTEN_PASS" "$JSONLD_FLATTEN_FAIL" "$JSONLD_FLATTEN_SKIP" "$JSONLD_FLATTEN_TOTAL" "$JSONLD_FLATTEN_PRESENT" \
    "Runner: <code>bin/jsonld-flatten-runner</code> (<code>bin/linux-x86_64/jsonld_flatten_runner</code>) &middot; Suite: W3C JSON-LD 1.1 flatten manifest (Node Map Generation + Flattening Algorithm)" \
    "<a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/jsonld-flatten.yaml\" target=\"_blank\" rel=\"noopener\">diagnosis: residual fails are enumerated Flattening-Algorithm gaps — see the suite manifest and the landing commit for the per-bucket breakdown</a>"
)
JSONLD_SUITES_RUN=$(( JSONLD_PRESENT + JSONLD_FROMRDF_PRESENT + JSONLD_EXPAND_PRESENT + JSONLD_COMPACT_PRESENT + JSONLD_FLATTEN_PRESENT ))
JSONLD_FAMILY_HTML=$(family_section "jsonld11" "JSON-LD 1.1" "$JSONLD_STATUS" "$JSONLD_FAMILY_HEADLINE" "$JSONLD_BODY" "" \
  "$JSONLD_FAM_PASS" "$JSONLD_FAM_FAIL" "$JSONLD_FAM_SKIP" "$JSONLD_FAM_TOTAL" "${JSONLD_SUITES_RUN} of 7" \
  "$(family_remaining _jsonld-family)")

# --- Verifiable Credentials 2.0 --------------------------------------------
# Prose rewritten in plain language (owner directive 2026-07-10): explain
# what the remaining fail and skips actually are, in ordinary words, with
# no internal shorthand or bare issue numbers.
VC_STATUS=$(status_for "$VC_FAIL" "$VC_PRESENT")
if [ "$VC_PRESENT" -eq 1 ]; then
  VC_FAMILY_HEADLINE="${VC_PASS} pass, ${VC_FAIL} fail, ${VC_SKIP} skip (out of ${VC_TOTAL}) on the structural Stage 1 suite. Signing and verifying credentials (the Data Integrity eddsa-rdfc-2022 proof: RDFC-1.0 canonicalization + SHA-256 + Ed25519 via HACL*) runs in the native binary, Node, and the browser bundle; full conformance testing of that signing layer against the official W3C proof-options test suite is still pending."
else
  VC_FAMILY_HEADLINE="Not measured this run."
fi
VC_DIAG="All 117 scorable fixtures pass. The two validity-period fixtures are scored for real: the official test suite fills in concrete dates at run time, and this runner now does the same substitution before checking, so the engine's own validFrom/validUntil ordering check decides the verdict. The three &ldquo;reject-or-patch&rdquo; fixtures are scored as must-reject: the official suite lets an issuer either repair a missing @context or reject the document, and since this engine validates rather than issues, rejecting is the compliant behavior. Three vendored fixtures are marked <strong>withdrawn upstream</strong> and excluded from the scorable set: unsigned template files for holder-binding tests the official test suite removed as unsound in February 2025 &mdash; they contain no signature to verify, the official suite does not run them, and they are nobody's work to do (a skip would wrongly suggest otherwise). Signature cryptography is implemented and in use, not pending: eddsa-rdfc-2022 Data Integrity proofs (RDFC-1.0 canonicalization, SHA-256, Ed25519 via the formally verified HACL&#42; library) sign and verify in this same binary &mdash; <code>vc_runner --crypto</code> runs an 8-check create/verify/tamper roundtrip, 8 pass, 0 fail."
# Task #88 (canivc.com community-compatibility integration, 2026-07-10):
# two more measurements against the same VC family, each with its OWN
# denominator — deliberately NOT folded into VC_PASS/VC_FAIL/VC_TOTAL
# above (anti-pattern #25: different suites, different scope, never
# add the numerators together). vc-di-eddsa is the official W3C Data
# Integrity eddsa-rdfc-2022 signing/verifying suite run against a new
# HTTP shim (bin/vc-api-shim); vc20-api is the ALREADY-vendored VC Data
# Model 2.0 suite's own issuer/verifier HTTP tests, run against the
# same shim — complementary to, not a replacement for, the Stage 1
# structural-fixture row above.
VCDIEDDSA_DIAG="Remaining 5 failures: 3 are missing DATA_LOSS_DETECTION_ERROR detection (a JSON-LD term silently dropped by expansion is not caught and rejected), 2 are multi-proof / <code>proof.previousProof</code> chaining (not supported — the shim checks exactly one proof). Community comparison on the identical 31-test scope (canivc.com's &ldquo;eddsa-rdfc-2022 issuers&rdquo; + &ldquo;verifiers&rdquo; matrices): scores range 0% to 100% among registered implementations, median 41.9%; 83.9% here places Factoidal above the median, close behind Trential (93.5%) and SpruceID (96.8%), behind Grotto Networking (100%)."
VC20API_DIAG="Single dominant cause for nearly all 37 failures: the shim has no VC Data Model 2.0 structural validator of its own (it only implements Data Integrity signing/verifying) — almost every failure is a missing-rejection-of-malformed-input test (bad <code>credentialStatus</code>/<code>refreshService</code>/<code>credentialSchema</code>/<code>termsOfUse</code>/<code>evidence</code> shape, <code>validUntil</code> before <code>validFrom</code>, missing <code>type</code>/<code>@context</code>, malformed Verifiable Presentation). Full breakdown: <code>docs/test-results/by-suite/vc20-api.json</code>."
# Track B1 (2026-07-13, docs/designissues/2026-07-11-vc-canivc-eecc-plan.md):
# vendored EECC (European EPC Competence Center) Apache-2.0 fixtures —
# see third_party/testing/eecc/PROVENANCE.md for the full clone/licence/
# pruning record. A DIFFERENT denominator again (anti-pattern #25):
# real-world GS1 credentials, not an official W3C test corpus.
EECCINTEROP_DIAG="4 real, DataIntegrityProof-signed W3C VCDM 2.0 credentials from EECC's own GS1 sandbox get a structural check (<code>VC_Credential.vc_check_from_string</code>, the same Stage 1 checker above) plus a crypto-verify check that is scored SKIP, not attempted or failed: every fixture's <code>verificationMethod</code> is a <code>did:web</code> URL needing live HTTPS DID resolution this offline runner does not perform, and no public key material is bundled in the fixture JSON. Every other vendored file (JSON Schemas, SD-JWT/mdoc claim sets from webuild-attestations, one JWT-VC example — a different credential serialization Factoidal has no parser for) is a format-mismatch SKIP, not fed through the JSON-LD checker at all. Full breakdown: <code>docs/test-results/by-suite/eecc-interop.json</code>."
VC_BODY=$(
  family_suite_row "VC Data Model 2.0 — structural (Stage 1)" "$VC_PASS" "$VC_FAIL" "$VC_SKIP" "$VC_TOTAL" "$VC_PRESENT" \
    "Runner: <code>bin/vc-runner</code> (<code>bin/linux-x86_64/vc_runner</code>) &middot; Suite: <code>third_party/testing/vc/tests/input/</code> (structural fixtures, filename-encoded verdicts)" \
    "${VC_DIAG} <a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-05-vc-program-plan.md\" target=\"_blank\" rel=\"noopener\">VC program plan</a>"
  family_suite_row "Data Integrity eddsa-rdfc-2022 (W3C vc-di-eddsa-test-suite, via shim)" "$VCDIEDDSA_PASS" "$VCDIEDDSA_FAIL" "$VCDIEDDSA_SKIP" "$VCDIEDDSA_TOTAL" "$VCDIEDDSA_PRESENT" \
    "Runner: <code>tests/vc-di-eddsa/run.sh</code> &middot; Suite: <code>third_party/testing/vc-di-eddsa/tests/{05-di-rdfc-create,15-di-rdfc-verify}.js</code> against <code>bin/vc-api-shim/server.mjs</code>" \
    "${VCDIEDDSA_DIAG} <a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/vc-di-eddsa.yaml\" target=\"_blank\" rel=\"noopener\">suite manifest</a> &middot; <a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-10-canivc-community-compat.md\" target=\"_blank\" rel=\"noopener\">canivc.com scoping doc</a>"
  family_suite_row "VC Data Model 2.0 — issuer/verifier HTTP suite (via shim)" "$VC20API_PASS" "$VC20API_FAIL" "$VC20API_SKIP" "$VC20API_TOTAL" "$VC20API_PRESENT" \
    "Runner: <code>tests/vc20-api/run.sh</code> &middot; Suite: <code>third_party/testing/vc/tests/{1.03-conformance,4.03-contexts,...,7-algorithms}.js</code> (14 files) against <code>bin/vc-api-shim/server.mjs</code>" \
    "${VC20API_DIAG} <a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/vc20-api.yaml\" target=\"_blank\" rel=\"noopener\">suite manifest</a>"
  family_suite_row "EECC VC/DID interop fixtures (vendored vc-verifier-rules + webuild-attestations)" "$EECCINTEROP_PASS" "$EECCINTEROP_FAIL" "$EECCINTEROP_SKIP" "$EECCINTEROP_TOTAL" "$EECCINTEROP_PRESENT" \
    "Runner: <code>bin/eecc-runner</code> (<code>bin/linux-x86_64/eecc_runner</code>) &middot; Fixtures: <code>third_party/testing/eecc/</code> (vendored real-world GS1 credentials, Apache-2.0)" \
    "${EECCINTEROP_DIAG} <a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/eecc-interop.yaml\" target=\"_blank\" rel=\"noopener\">suite manifest</a> &middot; <a href=\"${GITHUB_BLOB_BASE}/third_party/testing/eecc/PROVENANCE.md\" target=\"_blank\" rel=\"noopener\">vendoring provenance</a> &middot; <a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-11-vc-canivc-eecc-plan.md\" target=\"_blank\" rel=\"noopener\">VC/canivc/EECC plan</a>"
  cat <<CANIVC
      <details class="suite-node grey">
        <summary><span class="suite-name">VC community compatibility (canivc.com)</span><span class="suite-numbers">snapshot 2026-07-10</span><span class="dot grey"></span></summary>
        <div class="suite-body">
          <p class="suite-numbers-full">Digital Bazaar's <a href="https://canivc.com" target="_blank" rel="noopener">canivc.com</a> aggregates the same official W3C/CCG test-suite reports across ~20 implementations. Per-suite comparison (community min/median/max % across registered implementations, from a snapshot vendored at <code>third_party/testing/canivc-snapshot/</code>; full scoping + gap rationale in <a href="${GITHUB_BLOB_BASE}/docs/designissues/2026-07-10-canivc-community-compat.md" target="_blank" rel="noopener">the canivc.com integration doc</a>):</p>
          <table class="canivc-compat">
            <thead><tr><th>suite</th><th>Factoidal</th><th>community min / median / max</th><th>status</th></tr></thead>
            <tbody>
              <tr><td>eddsa-rdfc-2022 (create+verify, 31 tests)</td><td>83.9% (26/31)</td><td>0% / 41.9% / 100%</td><td>measured — above median</td></tr>
              <tr><td>VC Data Model 2.0 (issuer/verifier HTTP)</td><td>37.3% (22/59)</td><td>22.0% / 54.7% / 96.6%</td><td>measured — below median (structural validation gap, see row above)</td></tr>
              <tr><td>did:key</td><td>not measured via HTTP resolver</td><td>25.0% / 25.0% / 87.5%</td><td>assessed, not implemented — see scoping doc</td></tr>
              <tr><td>Data Integrity ECDSA</td><td>not implemented</td><td>0% / 90.0% / 100%</td><td>out of scope — no ECDSA cryptosuite wired (HACL&#42; has P-256 source, not adopted)</td></tr>
              <tr><td>Ed25519Signature2020</td><td>not implemented</td><td>0% / 78.6% / 100%</td><td>out of scope — legacy cryptosuite, assessed distance from eddsa-rdfc-2022, not attempted</td></tr>
              <tr><td>Data Integrity BBS</td><td>not implemented</td><td>2.3% / 78.5% / 100%</td><td>out of scope — no BBS signature scheme anywhere in the codebase</td></tr>
              <tr><td>VC JOSE/COSE</td><td>not implemented</td><td>68.6% / 100% / 100%</td><td>out of scope — different (JWT/CWT) securing stack</td></tr>
              <tr><td>VC Bitstring Status List</td><td>not implemented</td><td>3.8% / 32.7% / 96.2%</td><td>out of scope — credentialStatus processing not implemented</td></tr>
              <tr><td>VC-API Issuer (full)</td><td>not implemented</td><td>0% / 42.9% / 96.4%</td><td>out of scope — full VC-API surface far beyond issue/verify</td></tr>
              <tr><td>VC-API Verifier (full)</td><td>not implemented</td><td>0% / 55.6% / 97.2%</td><td>out of scope — same reason</td></tr>
            </tbody>
          </table>
        </div>
      </details>
CANIVC
)
VC_FAMILY_HTML=$(family_section "vc2" "Verifiable Credentials 2.0" "$VC_STATUS" "$VC_FAMILY_HEADLINE" "$VC_BODY" "" \
  "$VC_PASS" "$VC_FAIL" "$VC_SKIP" "$VC_TOTAL" "" "$(family_remaining vc)")

# --- XML-family W3C Recommendations: XSLT 1.0 / XML 1.0 / MathML 3 --------
# XSLT 1.0, XML 1.0, and MathML 3 are each their own W3C Recommendation
# and each renders as its own family node (owner directive 2026-07-10 —
# independent items are not treated as a single component).
XSLTFAM_STATUS=$(status_for "$XSLT_FAIL" "$XSLT_PRESENT")
if [ "$XSLT_PRESENT" -eq 1 ]; then
  XSLTFAM_HEADLINE="${XSLT_PASS} pass, ${XSLT_FAIL} fail, ${XSLT_SKIP} skip (out of ${XSLT_TOTAL}) on XSLT 1.0 transform conformance."
else
  XSLTFAM_HEADLINE="Not measured this run."
fi
XSLTFAM_BODY=$(
  family_suite_row "XSLT 1.0" "$XSLT_PASS" "$XSLT_FAIL" "$XSLT_SKIP" "$XSLT_TOTAL" "$XSLT_PRESENT" \
    "Runner: <code>bin/xslt-runner</code> (<code>bin/linux-x86_64/xslt_runner</code>) &middot; Suite: <code>third_party/testing/xslt/manifest.json</code>" \
    "<a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/xslt.yaml\" target=\"_blank\" rel=\"noopener\">diagnosis: residual fails are the documented XSLT 1.0 constructs not yet in the transform engine — see the suite manifest</a>"
)
XSLTFAM_HTML=$(family_section "xslt10" "XSLT 1.0" "$XSLTFAM_STATUS" "$XSLTFAM_HEADLINE" "$XSLTFAM_BODY" "" \
  "$XSLT_PASS" "$XSLT_FAIL" "$XSLT_SKIP" "$XSLT_TOTAL")

# XML conformance carries a collapsible honest-breakdown sub-panel so the
# headline is never read as a bare conformance % — the skip decomposition
# (real not-wf rejects vs DTD-boundary skips vs out-of-profile) sits one
# tap away.
if [ -n "$XMLCONF_BREAKDOWN" ]; then
  XMLCONF_BREAKDOWN_HTML=$(cat <<XBD
      <details class="failure-detail">
        <summary>XML conformance — integrity breakdown (real rejects vs skips)</summary>
        <pre>${XMLCONF_BREAKDOWN}</pre>
      </details>
XBD
)
else
  XMLCONF_BREAKDOWN_HTML=""
fi
XMLCONFFAM_STATUS=$(status_for "$XMLCONF_FAIL" "$XMLCONF_PRESENT")
if [ "$XMLCONF_PRESENT" -eq 1 ]; then
  XMLCONFFAM_HEADLINE="${XMLCONF_PASS} pass, ${XMLCONF_FAIL} fail, ${XMLCONF_SKIP} skip (out of ${XMLCONF_TOTAL}) on XML 1.0 well-formedness conformance."
else
  XMLCONFFAM_HEADLINE="Not measured this run."
fi
XMLCONFFAM_BODY=$(
  family_suite_row "XML 1.0 conformance" "$XMLCONF_PASS" "$XMLCONF_FAIL" "$XMLCONF_SKIP" "$XMLCONF_TOTAL" "$XMLCONF_PRESENT" \
    "Runner: <code>bin/xml-runner</code> (<code>bin/linux-x86_64/xml_runner</code>) &middot; Suite: <code>third_party/testing/xml/xmlconf</code> (OASIS/W3C XML conformance) &middot; skips are DTD-boundary / out-of-XML-1.0-profile fixtures, decomposed in the breakdown below"
  printf '%s' "$XMLCONF_BREAKDOWN_HTML"
)
XMLCONFFAM_HTML=$(family_section "xml10" "XML 1.0" "$XMLCONFFAM_STATUS" "$XMLCONFFAM_HEADLINE" "$XMLCONFFAM_BODY" "" \
  "$XMLCONF_PASS" "$XMLCONF_FAIL" "$XMLCONF_SKIP" "$XMLCONF_TOTAL")

MATHMLFAM_STATUS=$(status_for "$MATHML_FAIL" "$MATHML_PRESENT")
if [ "$MATHML_PRESENT" -eq 1 ]; then
  MATHMLFAM_HEADLINE="${MATHML_PASS} pass, ${MATHML_FAIL} fail, ${MATHML_SKIP} skip (out of ${MATHML_TOTAL}) on Content MathML evaluation."
else
  MATHMLFAM_HEADLINE="Not measured this run."
fi
MATHMLFAM_BODY=$(
  family_suite_row "MathML 3 content" "$MATHML_PASS" "$MATHML_FAIL" "$MATHML_SKIP" "$MATHML_TOTAL" "$MATHML_PRESENT" \
    "Runner: <code>bin/mathml-runner</code> (<code>bin/linux-x86_64/mathml_runner</code>) &middot; Suite: <code>third_party/testing/mathml/manifest.json</code> (Content MathML evaluation)"
)
MATHMLFAM_HTML=$(family_section "mathml3" "MathML 3" "$MATHMLFAM_STATUS" "$MATHMLFAM_HEADLINE" "$MATHMLFAM_BODY" "" \
  "$MATHML_PASS" "$MATHML_FAIL" "$MATHML_SKIP" "$MATHML_TOTAL")

# --- DID (W3C Recommendation) ----------------------------------------------
# Split out from the old combined "JSON Schema / DID" family (owner
# directive 2026-07-10): DID Core reached W3C Recommendation status, so it
# gets its own node in the W3C Recommendations group. JSON Schema is not a
# W3C specification at all and moves to the open-source-comparison/
# internal group below, alongside ISO Schematron.
DID_STATUS=$(status_for "$DIDKEY_FAIL" "$DIDKEY_PRESENT")
if [ "$DIDKEY_PRESENT" -eq 1 ]; then
  DID_HEADLINE="${DIDKEY_PASS} pass, ${DIDKEY_FAIL} fail, ${DIDKEY_SKIP} skip (out of ${DIDKEY_TOTAL}) on did:key resolution."
else
  DID_HEADLINE="Not measured this run."
fi
DID_BODY=$(
  family_suite_row "DID did:key" "$DIDKEY_PASS" "$DIDKEY_FAIL" "$DIDKEY_SKIP" "$DIDKEY_TOTAL" "$DIDKEY_PRESENT" \
    "Runner: <code>bin/did-runner</code> (<code>bin/linux-x86_64/did_runner</code>) &middot; Suite: did:key resolution + multibase/multicodec accept/reject cases"
)
DID_HTML=$(family_section "did" "DID (Decentralized Identifiers)" "$DID_STATUS" "$DID_HEADLINE" "$DID_BODY" "" \
  "$DIDKEY_PASS" "$DIDKEY_FAIL" "$DIDKEY_SKIP" "$DIDKEY_TOTAL" "" "$(family_remaining did)")

# --- Other conformance suites (not W3C): JSON Schema / ISO Schematron -----
JSONSCHEMA_STATUS=$(status_for "$JSONSCHEMA_FAIL" "$JSONSCHEMA_PRESENT")
if [ "$JSONSCHEMA_PRESENT" -eq 1 ]; then
  JSONSCHEMA_HEADLINE="${JSONSCHEMA_PASS} pass, ${JSONSCHEMA_FAIL} fail, ${JSONSCHEMA_SKIP} skip (out of ${JSONSCHEMA_TOTAL}) on the JSON-Schema-Test-Suite draft-07 battery. An independent specification (json-schema.org), not W3C."
else
  JSONSCHEMA_HEADLINE="Not measured this run."
fi
JSONSCHEMA_BODY=$(
  family_suite_row "JSON Schema draft-07" "$JSONSCHEMA_PASS" "$JSONSCHEMA_FAIL" "$JSONSCHEMA_SKIP" "$JSONSCHEMA_TOTAL" "$JSONSCHEMA_PRESENT" \
    "Runner: <code>bin/jsonschema-runner</code> (<code>bin/linux-x86_64/jsonschema_runner</code>) &middot; Suite: <code>third_party/testing/jsonschema/</code> (JSON-Schema-Test-Suite draft7) &middot; skips are optional/format vocabularies out of scope for the core validator"
)
JSONSCHEMA_HTML=$(family_section "json-schema" "JSON Schema" "$JSONSCHEMA_STATUS" "$JSONSCHEMA_HEADLINE" "$JSONSCHEMA_BODY" "" \
  "$JSONSCHEMA_PASS" "$JSONSCHEMA_FAIL" "$JSONSCHEMA_SKIP" "$JSONSCHEMA_TOTAL")

SCHEMATRON_STATUS=$(status_for "$SCHEMATRON_FAIL" "$SCHEMATRON_PRESENT")
if [ "$SCHEMATRON_PRESENT" -eq 1 ]; then
  SCHEMATRON_HEADLINE="${SCHEMATRON_PASS} pass, ${SCHEMATRON_FAIL} fail, ${SCHEMATRON_SKIP} skip (out of ${SCHEMATRON_TOTAL}) on rule-based assertion cases. An ISO standard (ISO/IEC 19757-3), not a W3C specification."
else
  SCHEMATRON_HEADLINE="Not measured this run."
fi
SCHEMATRON_BODY=$(
  family_suite_row "ISO Schematron" "$SCHEMATRON_PASS" "$SCHEMATRON_FAIL" "$SCHEMATRON_SKIP" "$SCHEMATRON_TOTAL" "$SCHEMATRON_PRESENT" \
    "Runner: <code>bin/schematron-runner</code> (<code>bin/linux-x86_64/schematron_runner</code>) &middot; Suite: <code>third_party/testing/schematron/</code> (rule-based assertion cases)"
)
SCHEMATRON_HTML=$(family_section "schematron" "ISO Schematron" "$SCHEMATRON_STATUS" "$SCHEMATRON_HEADLINE" "$SCHEMATRON_BODY" "" \
  "$SCHEMATRON_PASS" "$SCHEMATRON_FAIL" "$SCHEMATRON_SKIP" "$SCHEMATRON_TOTAL")

# --- QUDT (independent ontology suite, qudt.org — not a W3C spec) ----------
# QUDT (Quantities, Units, Dimensions and data Types) is the de-facto RDF
# vocabulary for units of measure, published by QUDT.org. It has NO official
# conformance suite; the two rows below are the Layer-A targets defined in
# docs/designissues/2026-07-10-qudt-scoping.md: our verified SHACL validator
# running QUDT's own shipped rulesets — the contributor integrity ruleset
# against the vendored v3.4.0 all-in-one distribution (one scored entry per
# ruleset shape), and the user-facing deprecation/consistency ruleset
# against authored fixtures. Layers B (exact-rational unit conversion +
# dimension-vector algebra in F*) and C (qudtf: SPARQL extension functions)
# are the remaining follow-ups.
read -r QUDT_FAM_PASS QUDT_FAM_FAIL QUDT_FAM_SKIP QUDT_FAM_TOTAL QUDT_FAM_ANY <<< "$(sum_family "QUDT_INTEGRITY QUDT_USER")"
QUDT_STATUS=$(status_for "$QUDT_FAM_FAIL" "$QUDT_FAM_ANY")
if [ "$QUDT_FAM_ANY" -eq 1 ]; then
  QUDT_HEADLINE="${QUDT_FAM_PASS} pass, ${QUDT_FAM_FAIL} fail, ${QUDT_FAM_SKIP} skip (out of ${QUDT_FAM_TOTAL}) across QUDT's own shipped SHACL rulesets (v3.4.0). An independent ontology suite (qudt.org), not W3C — no official conformance suite exists, so these are the scoping doc's Layer-A targets."
else
  QUDT_HEADLINE="Not measured this run."
fi
QUDT_BODY=$(
  family_suite_row "QUDT integrity (contributor ruleset vs distribution)" "$QUDT_INTEGRITY_PASS" "$QUDT_INTEGRITY_FAIL" "$QUDT_INTEGRITY_SKIP" "$QUDT_INTEGRITY_TOTAL" "$QUDT_INTEGRITY_PRESENT" \
    "Runner: <code>bin/qudt-runner</code> (<code>bin/linux-x86_64/qudt_runner --integrity</code>) &middot; Data: <code>third_party/qudt/QUDT-all-in-one-SHACL.ttl</code> (131k triples) vs <code>COLLECTION_QUDT_QA_TESTS_ALL.ttl</code>; one entry per ruleset shape; upstream data findings annotated in <code>tests/qudt/dispositions.tsv</code>, never patched"
  family_suite_row "QUDT user shapes (deprecation + consistency fixtures)" "$QUDT_USER_PASS" "$QUDT_USER_FAIL" "$QUDT_USER_SKIP" "$QUDT_USER_TOTAL" "$QUDT_USER_PRESENT" \
    "Runner: <code>bin/qudt-runner</code> (<code>bin/linux-x86_64/qudt_runner --fixtures</code>) &middot; Fixtures: <code>tests/qudt/fixtures/</code> (-ok/-viol verdicts) vs <code>COLLECTION_QUDT_USER_TESTS.ttl</code> &middot; remaining: Layer B exact-rational conversion + dimension algebra in F*, Layer C qudtf: SPARQL functions"
)
QUDT_HTML=$(family_section "qudt" "QUDT (units of measure)" "$QUDT_STATUS" "$QUDT_HEADLINE" "$QUDT_BODY" "" \
  "$QUDT_FAM_PASS" "$QUDT_FAM_FAIL" "$QUDT_FAM_SKIP" "$QUDT_FAM_TOTAL")

# --- Storage backend & JS/browser runtime: HDT parity / hub / npm ---------
# Not W3C conformance — these exercise the shipped engine end to end: the
# HDT on-disk backend answering byte-identically to the in-memory backend,
# and the browser/npm bundle (reactive cells, all 7 engine FP APIs,
# HDT-in-bundle, VC crypto via HACL* wasm).
read -r RUNTIME_PASS RUNTIME_FAIL RUNTIME_SKIP RUNTIME_TOTAL RUNTIME_ANY <<< "$(sum_family "HDT_PARITY HUB NPM")"
RUNTIME_STATUS=$(status_for "$RUNTIME_FAIL" "$RUNTIME_ANY")
if [ "$RUNTIME_ANY" -eq 1 ]; then
  RUNTIME_HEADLINE="${RUNTIME_PASS} pass, ${RUNTIME_FAIL} fail, ${RUNTIME_SKIP} skip (of ${RUNTIME_TOTAL}) across HDT backend parity and the browser/npm bundle suites (node --test)."
else
  RUNTIME_HEADLINE="Not measured this run."
fi
RUNTIME_BODY=$(
  family_suite_row "HDT stage-4 backend parity" "$HDT_PARITY_PASS" "$HDT_PARITY_FAIL" "$HDT_PARITY_SKIP" "$HDT_PARITY_TOTAL" "$HDT_PARITY_PRESENT" \
    "Runner: <code>tests/local/hdt_stage4_parity.sh</code> &middot; Fixture: <code>third_party/testing/hdt/rml-core-ontology.hdt</code> vs ground-truth <code>.nt</code> (unbound/bound-S/P/O/ASK/COUNT, byte-identical)"
  family_suite_row "hub browser-bundle cells" "$HUB_PASS" "$HUB_FAIL" "$HUB_SKIP" "$HUB_TOTAL" "$HUB_PRESENT" \
    "Runner: <code>node --test tests/hub/*.mjs</code> &middot; live cells for every docs-hub post, run against the JS/wasm bundle" \
    "<a href=\"${GITHUB_BLOB_BASE}/tests/hub/\" target=\"_blank\" rel=\"noopener\">diagnosis: any residual fails are fixtures/build-artifacts absent in this checkout (uninitialised submodule or unbuilt C demo), not engine regressions</a>"
  family_suite_row "npm package suite" "$NPM_PASS" "$NPM_FAIL" "$NPM_SKIP" "$NPM_TOTAL" "$NPM_PRESENT" \
    "Runner: <code>node --test npm/factoidal/test/*.test.js</code> &middot; the 7 engine FP APIs, HDT-in-bundle, delta-log, VC crypto (HACL* wasm)" \
    "<a href=\"${GITHUB_BLOB_BASE}/npm/factoidal/test/\" target=\"_blank\" rel=\"noopener\">diagnosis: any residual fails are vendored-fixture submodules absent in this checkout, not engine regressions</a>"
)
RUNTIME_HTML=$(family_section "runtime-parity" "Storage backend &amp; JS runtime: HDT parity / hub / npm" "$RUNTIME_STATUS" "$RUNTIME_HEADLINE" "$RUNTIME_BODY" "" \
  "$RUNTIME_PASS" "$RUNTIME_FAIL" "$RUNTIME_SKIP" "$RUNTIME_TOTAL")

# --- F* unit regressions & adjacent engines (#82) --------------------------
# The tests/unit native harness (run-all.sh) is now relinked per-test against
# the committed .cmx — each test carries only its own dependency closure, so
# a stale/unrelated module can't break an unrelated test's link (#82). That
# unhid several shipped F* engines: geosparql (WKT geometry + geof: topology)
# and xpath-1.0 come straight out of the harness; the TOAN/Matrix CAS engines
# and the XForms bind/recalc model are scored through the JS bundle
# (node --test). The aggregate row shows files-passing / files-failing across
# all 41 native unit files. This replaces the earlier grey "XForms not yet
# wired (#82)" note with real rows + an honest native-XForms status.
read -r ENGINES_PASS ENGINES_FAIL ENGINES_SKIP ENGINES_TOTAL ENGINES_ANY <<< "$(sum_family "GEOSPARQL XPATH_UNIT TOAN_MATRIX XFORMS_NPM")"
ENGINES_CARD_FAIL=$((ENGINES_FAIL + ${TESTS_UNIT_FAIL:-0}))
ENGINES_STATUS=$(status_for "$ENGINES_CARD_FAIL" "$ENGINES_ANY")
if [ "$ENGINES_ANY" -eq 1 ]; then
  ENGINES_HEADLINE="${ENGINES_PASS} pass, ${ENGINES_FAIL} fail, ${ENGINES_SKIP} skip (of ${ENGINES_TOTAL}) across GeoSPARQL v0, XPath 1.0, the TOAN/Matrix CAS engines, and the XForms model — shipped F* engines now surfaced from the native unit harness or the JS bundle; the aggregate row below reports how many of the 41 native unit files link and pass in this checkout."
else
  ENGINES_HEADLINE="Not measured this run."
fi
ENGINES_BODY=$(
  family_suite_row "GeoSPARQL (geof: topology + WKT)" "$GEOSPARQL_PASS" "$GEOSPARQL_FAIL" "$GEOSPARQL_SKIP" "$GEOSPARQL_TOTAL" "$GEOSPARQL_PRESENT" \
    "Runner: <code>tests/unit/run-all.sh geosparql_v0_unit</code> &middot; F* <code>RDF.Geo.*</code> — exact-rational WKT geometry + Simple-Features topology + geof: distance/envelope. Hub post21 pins 12 more assertions live against the browser bundle (counted in the npm/hub runtime family)."
  family_suite_row "XPath 1.0 (unit)" "$XPATH_UNIT_PASS" "$XPATH_UNIT_FAIL" "$XPATH_UNIT_SKIP" "$XPATH_UNIT_TOTAL" "$XPATH_UNIT_PRESENT" \
    "Runner: <code>tests/unit/run-all.sh xpath_tests</code> &middot; the F* XPath 1.0 evaluator over location-step / predicate / node-set / function-library cases."
  family_suite_row "TOAN CAS + Math.Matrix engines" "$TOAN_MATRIX_PASS" "$TOAN_MATRIX_FAIL" "$TOAN_MATRIX_SKIP" "$TOAN_MATRIX_TOTAL" "$TOAN_MATRIX_PRESENT" \
    "Runner: <code>node --test npm/factoidal/test/{toan,matrix}.test.js</code> &middot; the F* CAS (summation / product / simplify / diff / subst) + exact-rational matrix engines via the JS bundle. The npm package suite (runtime family above) additionally exercises xslt, mathml, xforms, jsonschema, schematron, hdt, and vc-crypto — each a shipped engine with its own test file."
  family_suite_row "XForms model (bind/recalc)" "$XFORMS_NPM_PASS" "$XFORMS_NPM_FAIL" "$XFORMS_NPM_SKIP" "$XFORMS_NPM_TOTAL" "$XFORMS_NPM_PRESENT" \
    "Runner: <code>node --test npm/factoidal/test/xforms.test.js</code> &middot; the F* XForms bind/recalc model via the JS bundle. The larger native suite (<code>tests/unit/xforms_tests.ml</code>, ~29 bind/recalc cases) can't link in this checkout — its <code>XForms_Bind.cmx</code> is not in the committed artifact set — so the harness fix (<a href=\"https://github.com/danbri/factoidal/issues/82\" target=\"_blank\" rel=\"noopener\">#82</a>) is landed but that suite awaits a committed build; no fabricated 29/29 is shown."
  family_suite_row "F* unit regressions (tests/unit)" "$TESTS_UNIT_PASS" "$TESTS_UNIT_FAIL" "$TESTS_UNIT_SKIP" "$TESTS_UNIT_TOTAL" "$TESTS_UNIT_PRESENT" \
    "Runner: <code>tests/unit/run-all.sh</code> &middot; files-passing / files-failing across all 41 native unit files, each relinked against its own committed-.cmx dependency closure. The ${TESTS_UNIT_FAIL:-0} failing files either need a module with no committed .cmx (Math_* / MathML_* / XForms_Bind engines) or hit a committed-.cmx epoch mismatch (RML_Eval vs SPARQL11_Algebra committed in different builds) — an artifact-staleness gap, not a harness bug."
)
# The condensed family-level score must sum to its own total (unlike
# ENGINES_CARD_FAIL, which folds in tests_unit's fail count for STATUS
# colour purposes only) — so build a separate, self-consistent
# pass+fail+skip=total aggregate across all five rows in this family,
# tests_unit included, for the collapsed summary line.
ENGINES_AGG_PASS=$((ENGINES_PASS + TESTS_UNIT_PASS))
ENGINES_AGG_FAIL=$((ENGINES_FAIL + TESTS_UNIT_FAIL))
ENGINES_AGG_SKIP=$((ENGINES_SKIP + TESTS_UNIT_SKIP))
ENGINES_AGG_TOTAL=$((ENGINES_TOTAL + TESTS_UNIT_TOTAL))
ENGINES_HTML=$(family_section "fstar-engines" "F&#42; unit regressions &amp; adjacent engines: GeoSPARQL / XPath / TOAN / XForms" "$ENGINES_STATUS" "$ENGINES_HEADLINE" "$ENGINES_BODY" "" \
  "$ENGINES_AGG_PASS" "$ENGINES_AGG_FAIL" "$ENGINES_AGG_SKIP" "$ENGINES_AGG_TOTAL")

# --- SPARQL extras: entailment regimes / GeoSPARQL / Jena rdf:text --------
# Owner directive (2026-07-10): the OWL 2 panel used to list GeoSPARQL and
# DID as roadmap items, which don't belong there — OWL 2 is a W3C
# Recommendation family and neither of those is OWL. This node collects
# SPARQL-adjacent extensions that are NOT themselves W3C Recommendations:
# the SPARQL 1.1 Entailment Regimes score is surfaced again here for
# convenience (its JSON/CSV data stays where it already lives, under the
# sparql family — this is presentation only), alongside GeoSPARQL (an OGC
# standard, not W3C) and Jena's rdf:text full-text search extension (not a
# standard at all — a vendor magic-property convention this project also
# implements). None of the three change the SPARQL 1.1 Recommendation
# family's own numbers.
# GeoSPARQL and Jena rdf:text are each their own family node (owner
# directive 2026-07-10 — promoted out of the old "SPARQL extras"
# umbrella). The extras node keeps only the entailment-regimes duplicate
# presentation.
SPARQLEXTRAS_STATUS=$(status_for "$TAB_ENTAIL_FAIL" "$TAB_ENTAIL_PRESENT")
if [ "$TAB_ENTAIL_PRESENT" -eq 1 ]; then
  SPARQLEXTRAS_HEADLINE="A duplicate presentation of the SPARQL 1.1 Entailment Regimes score, surfaced here for readers looking for reasoning-adjacent SPARQL capability."
else
  SPARQLEXTRAS_HEADLINE="Not measured this run."
fi
SPARQLEXTRAS_BODY=$(
  family_suite_row "SPARQL 1.1 Entailment Regimes" "$TAB_ENTAIL_PASS" "$TAB_ENTAIL_FAIL" "$TAB_ENTAIL_SKIP" "$TAB_ENTAIL_TOTAL" "$TAB_ENTAIL_PRESENT" \
    "Same measurement as the SPARQL 1.1 family's Entailment Regimes row &middot; driven by <code>Tableau.fst</code>'s <code>tableau_materialise</code> via <code>w3c_runner</code>"
)
SPARQLEXTRAS_HTML=$(family_section "sparql-extras" "SPARQL extras: entailment regimes" "$SPARQLEXTRAS_STATUS" "$SPARQLEXTRAS_HEADLINE" "$SPARQLEXTRAS_BODY" "" \
  "$TAB_ENTAIL_PASS" "$TAB_ENTAIL_FAIL" "$TAB_ENTAIL_SKIP" "$TAB_ENTAIL_TOTAL")

# --- GeoSPARQL (OGC standard) -----------------------------------------------
GEOFAM_STATUS=$(status_for "$GEOSPARQL_FAIL" "$GEOSPARQL_PRESENT")
if [ "$GEOSPARQL_PRESENT" -eq 1 ]; then
  GEOFAM_HEADLINE="${GEOSPARQL_PASS} pass, ${GEOSPARQL_FAIL} fail, ${GEOSPARQL_SKIP} skip (out of ${GEOSPARQL_TOTAL}) on geof: topology + WKT unit fixtures."
else
  GEOFAM_HEADLINE="Not measured this run."
fi
GEOFAM_BODY=$(
  family_suite_row "GeoSPARQL (geof: topology + WKT)" "$GEOSPARQL_PASS" "$GEOSPARQL_FAIL" "$GEOSPARQL_SKIP" "$GEOSPARQL_TOTAL" "$GEOSPARQL_PRESENT" \
    "OGC standard (not a W3C Recommendation) &middot; Runner: <code>tests/unit/run-all.sh geosparql_v0_unit</code> &middot; local fixtures, not the OGC compliance suite"
)
GEOSPARQLFAM_HTML=$(family_section "geosparql" "GeoSPARQL (OGC)" "$GEOFAM_STATUS" "$GEOFAM_HEADLINE" "$GEOFAM_BODY" "" \
  "$GEOSPARQL_PASS" "$GEOSPARQL_FAIL" "$GEOSPARQL_SKIP" "$GEOSPARQL_TOTAL")

# --- Jena rdf:text full-text search (vendor convention) ---------------------
JENA_TEXT_BODY="This project implements the jena-text <code>text:query</code> magic property (Slice 1: exact/token AND-match, no BM25 ranking) in <code>formal/fstar/SPARQL.FullText.fst</code>, exercised by hand-written local fixtures (<code>tests/local/fulltext_slice1.sh</code>, hub post 20) rather than an official conformance suite &mdash; Apache Jena does not publish a vendorable rdf:text/full-text-search test corpus, and none is checked into this repository. No pass/fail score is reported here because there is nothing to check it against."
JENATEXT_ROW=$(family_suite_row "Jena rdf:text (full-text search)" 0 0 0 0 0 "$JENA_TEXT_BODY" "" "no test data vendored")
JENATEXTFAM_HTML=$(family_section "jena-text" "SPARQL full-text search (jena-text convention)" "grey" "Implemented (text:query magic property); no vendorable conformance corpus exists, so no score is claimed." "$JENATEXT_ROW")

# --- HDT (W3C Member Submission) -------------------------------------------
# There is no external HDT conformance test suite vendored in this repo —
# HDT correctness is exercised indirectly by the stage-4 backend parity
# check (in the storage-backend/JS-runtime family below), which compares
# the HDT-backed engine against the in-memory engine byte-for-byte rather
# than against an HDT-specific corpus. This node exists so HDT (named
# explicitly in the owner's 2026-07-10 grouping directive) has a place in
# the W3C Community Group / Notes / Submissions group, honest about what
# is and isn't measured against the submission itself.
HDT_BODY="No HDT-specific conformance suite is vendored in this repository (the HDT Member Submission publishes a binary format spec, not a test suite). Correctness of this project's HDT backend is instead checked by the <a href=\"#runtime-parity\">HDT stage-4 backend parity</a> check below, which compares HDT-backed query results against the in-memory backend byte-for-byte on unbound/bound-S/P/O/ASK/COUNT queries."
HDT_ROW=$(family_suite_row "HDT (binary RDF format)" 0 0 0 0 0 "$HDT_BODY" "" "no format-conformance suite vendored")
HDT_HTML=$(family_section "hdt" "HDT" "grey" "No format-conformance suite to measure; see the backend parity check below." "$HDT_ROW")
# (no aggregate numbers — nothing to measure — falls back to grey "not measured this run")

# =============================================================================
# Top-level standards-status tree (owner directive 2026-07-10) ---------------
# Every family above is placed into exactly one of three groups, each its
# own collapsible node, open by default, in a fixed order within the group:
#   1. W3C Recommendations
#   2. W3C Community Group / Notes / Submissions
#   3. Apache / open-source comparison + internal
# REC status was checked per spec (not assumed from "it's on this page"):
# RDF 1.1 (incl. RDF/XML, RDFC-1.0), SPARQL 1.1, OWL 2, SHACL, CSVW,
# JSON-LD 1.1, VC 2.0 + Data Integrity, DID, RIF Core, GRDDL, XSLT 1.0,
# XML 1.0, and MathML 3 are all W3C Recommendations. ShEx is a W3C
# Community Group specification (not on the Recommendation track); HDT is
# a W3C Member Submission; RML is a Knowledge Graph Construction Community
# Group specification. JSON Schema and ISO Schematron are not W3C
# specifications at all. GeoSPARQL is an OGC standard, not W3C. QUDT is
# an independent ontology suite (qudt.org, a W3C member org, but QUDT is
# not on any W3C track). Jena rdf:text is a vendor convention, not a
# standard.
# =============================================================================
GROUP1_BODY=$(printf '%s\n' \
  "$RDFCORE_HTML" "$RDFC10FAM_HTML" "$SPARQL_FAMILY_HTML" "$OWL_FAMILY_HTML" "$SHACL_HTML" \
  "$CSVW_HTML" "$JSONLD_FAMILY_HTML" "$VC_FAMILY_HTML" "$DID_HTML" \
  "$RULES_HTML" "$GRDDL_HTML" "$XSLTFAM_HTML" "$XMLCONFFAM_HTML" "$MATHMLFAM_HTML")
GROUP1_HTML=$(group_section "group-w3c-rec" "W3C Recommendations" "$GROUP1_BODY")

# W3C Working Drafts (emerging next-revision specs) — RDF 1.2 / SPARQL 1.2.
# Its own group so it is never mistaken for a Recommendation. Empty (and
# therefore omitted) if the 1.2 runners produced no rows this run.
GROUP_WD_HTML=""
if [ -n "$V12_FAMILY_HTML" ]; then
  GROUP_WD_HTML=$(group_section "group-w3c-wd" "W3C Working Drafts (emerging)" "$V12_FAMILY_HTML")
fi

GROUP2_BODY=$(printf '%s\n' "$SHEX_HTML" "$HDT_HTML" "$RML_HTML")
GROUP2_HTML=$(group_section "group-w3c-cg" "W3C Community Group / Notes / Submissions" "$GROUP2_BODY")

GROUP3_BODY=$(printf '%s\n' \
  "$GEOSPARQLFAM_HTML" "$SPARQLEXTRAS_HTML" "$JENATEXTFAM_HTML" "$QUDT_HTML" "$JSONSCHEMA_HTML" "$SCHEMATRON_HTML")
GROUP3_HTML=$(group_section "group-other-standards" "Other standards (OGC / ISO / independent)" "$GROUP3_BODY")

GROUP4_BODY=$(printf '%s\n' "$RUNTIME_HTML" "$ENGINES_HTML")
GROUP4_HTML=$(group_section "group-internal" "Factoidal internal suites (engine end-to-end, parity, regressions)" "$GROUP4_BODY")

# --- Legend -----------------------------------------------------------------
LEGEND_HTML=$(cat <<'LEGENDEOF'
<div class="legend">
  <p class="legend-title">How to read this page</p>
  <ul class="legend-list">
    <li><span class="dot green"></span><strong>Green</strong> — full pass: every runnable test in the suite passes.</li>
    <li><span class="dot amber"></span><strong>Amber</strong> — partial: at least one fail, but every residual fail is diagnosed in writing (a link sits next to the row).</li>
    <li><span class="dot grey"></span><strong>Grey</strong> — not measured this run, or out of scope for this suite (e.g. skipped fixtures, a roadmap item with no runner yet).</li>
  </ul>
  <p class="legend-note">Collapsed rows show a condensed score in <strong>pass/fail/skip of total</strong> order (e.g. &ldquo;461/0/6 of 467&rdquo; means 461 pass, 0 fail, 6 skip out of 467) — tap a row to expand it for the fully-labelled sentence and a stacked pass/fail/skip meter, measured against that suite's own total so proportions are comparable across suites of very different sizes. A family row with an amber <strong>N gaps</strong> badge has a &ldquo;Remaining work&rdquo; list inside it; an expanded family with no badge and no fails is marked complete against the vendored suites.</p>
</div>
LEGENDEOF
)

cat > "$OUTPUT_DIR/index.html" <<HTMLEOF
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Factoidal — W3C test results</title>
<style>
  /*
   * Mobile-first (owner directive 2026-07-05): base rules below target a
   * ~390px phone viewport and widen via min-width media queries. Nothing
   * in this file should require horizontal scrolling of the page itself —
   * wide content (raw logs, long paths) lives inside its own
   * overflow-x:auto container (see the "pre" rule below).
   */
  :root {
    --fg: #1a1a1a; --muted: #666; --bg: #fff; --surface: #f7f7f7;
    --border: #e0e0e0; --brand: #2d6a4f; --brand-dark: #1b4332;
    --ok: #2d6a4f; --ok-tint: #e8f3ee;
    --warn: #b45309; --warn-tint: #fdf1e2;
    --err: #c0392b; --err-tint: #fbe9e7;
    --skip: #6b7280; --skip-tint: #eef0f2;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --fg: #e8e8e8; --muted: #a3a3a3; --bg: #14181a; --surface: #1d2224;
      --border: #333c3f; --brand: #7fc9a3; --brand-dark: #9fd9bd;
      --ok: #6fbf8f; --ok-tint: #16261e;
      --warn: #e8a13d; --warn-tint: #2b2113;
      --err: #e2685c; --err-tint: #2c1917;
      --skip: #9aa4ab; --skip-tint: #22282b;
    }
  }
  * { box-sizing: border-box; }
  html, body { margin: 0; padding: 0; }
  html { font-size: 100%; } /* 1rem/1em = 16px equivalent, never shrunk below this in body copy */
  body {
    font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
    color: var(--fg); background: var(--bg); line-height: 1.55;
    overflow-x: hidden; /* belt-and-braces: no component should ever push the page wider than the viewport */
  }
  a { color: var(--brand-dark); }

  header {
    background: var(--surface);
    border-bottom: 1px solid var(--border); padding: 1em 1em;
  }
  header .inner { max-width: 900px; margin: 0 auto; }
  header h1 { margin: 0 0 0.3em; font-size: 1.3rem; color: var(--brand-dark); }
  header p  { margin: 0; color: var(--muted); font-size: 0.95rem; }
  header nav { margin-top: 0.8em; font-size: 0.95rem; }
  header nav a { margin-right: 1.1em; display: inline-block; padding: 0.3em 0; }

  /* Freshness panel — both timestamps in one place. "Rendered" = when
     this HTML was last regenerated. "Tests" = when the underlying
     *_results.log last changed. Mobile-first: a plain block under the
     title. Widens to an absolutely-positioned top-right pill once
     there's room (min-width breakpoint below). */
  .rendered-pill {
    background: var(--bg); border: 1px solid var(--border);
    border-radius: 6px;
    padding: 0.5em 0.7em;
    margin: 0.8em 0 0;
    font-size: 0.82rem; color: var(--muted);
    line-height: 1.4;
  }
  .rendered-pill .row { display: block; }
  .rendered-pill strong { color: var(--brand-dark); font-weight: 600; }
  .rendered-pill .label {
    display: inline-block; min-width: 4.4em;
    color: var(--muted); font-weight: 400;
  }
  .rendered-pill.stale strong.tests { color: var(--warn); }

  main { max-width: 900px; margin: 0 auto; padding: 1em 0.8em; }

  .summary {
    display: grid; grid-template-columns: repeat(auto-fit, minmax(130px, 1fr));
    gap: 0.6em; margin: 0 0 1.2em;
  }
  .tile {
    background: var(--surface); border: 1px solid var(--border);
    border-radius: 6px; padding: 0.7em 0.8em;
  }
  .tile .label { color: var(--muted); font-size: 0.82rem; margin-bottom: 0.15em; }
  .tile .value { font-size: 1.3rem; font-weight: 600; line-height: 1.2; }
  .tile .value small { font-size: 0.62em; font-weight: 400; color: var(--muted); }
  .tile.ok   .value { color: var(--ok); }
  .tile.err  .value { color: var(--err); }
  .tile.warn .value { color: var(--warn); }

  .caveat {
    border-left: 4px solid var(--skip);
    background: var(--surface);
    padding: 0.8em 1em; margin: 0 0 1.2em; border-radius: 0 6px 6px 0;
    font-size: 0.92rem;
  }
  .caveat strong { color: var(--brand-dark); }

  /* Colour legend — explains green/amber/grey once, up top, referenced
     by every family section below. Wraps naturally on narrow screens. */
  .legend {
    background: var(--surface); border: 1px solid var(--border);
    border-radius: 8px; padding: 0.9em 1em; margin: 0 0 1.4em;
  }
  .legend-title { margin: 0 0 0.5em; font-weight: 600; color: var(--brand-dark); }
  .legend-list { list-style: none; margin: 0 0 0.6em; padding: 0; }
  .legend-list li {
    display: flex; align-items: flex-start; gap: 0.5em;
    margin: 0.35em 0; font-size: 0.92rem;
  }
  .legend-note { margin: 0; font-size: 0.85rem; color: var(--muted); }
  .dot {
    flex: none; width: 0.85em; height: 0.85em; border-radius: 50%;
    margin-top: 0.25em;
  }
  .dot.green { background: var(--ok); }
  .dot.amber { background: var(--warn); }
  .dot.grey  { background: var(--skip); }

  /* --- Top-level standards-status groups (2026-07-10 tree redesign) ---- */
  /* One collapsible node per group (W3C Recommendations / W3C Community
     Group-Notes-Submissions / Apache &amp; open-source comparison +
     internal), open by default, each wrapping a fixed-order list of
     family cards. */
  details.group-section {
    border: 1px solid var(--border); border-radius: 10px;
    padding: 0.3em 0.9em 0.9em; margin: 0 0 1.4em;
    background: var(--bg);
  }
  details.group-section > summary.group-summary {
    cursor: pointer; list-style: none;
    font-size: 1.15rem; font-weight: 700; color: var(--brand-dark);
    padding: 0.6em 0.2em; min-height: 44px; display: flex; align-items: center;
  }
  details.group-section > summary.group-summary::-webkit-details-marker { display: none; }
  details.group-section > summary.group-summary::marker { content: ""; }
  details.group-section > summary.group-summary::before {
    content: "\25BE"; display: inline-block; margin-right: 0.4em;
    transition: transform 0.15s ease;
  }
  details.group-section:not([open]) > summary.group-summary::before {
    transform: rotate(-90deg);
  }
  details.group-section .group-body { margin-top: 0.3em; }

  /* --- Family nodes: one collapsible <details> per spec family --------- */
  /* Second pass (2026-07-10): families used to be always-open cards — a
     name line, then a full prose score paragraph below, at ~1rem+ font —
     which is what read as "stacked padded cards" rather than a tree on a
     phone. Now a collapsible node, same chevron/dot/condensed-score
     pattern as a suite row, nested one level deeper (see
     .family-body .suites below for the indentation guide-line). */
  details.family-node {
    border: 1px solid var(--border); border-left-width: 4px;
    border-radius: 8px; margin: 0 0 0.6em; background: var(--bg);
  }
  details.family-node.green { border-left-color: var(--ok); }
  details.family-node.amber { border-left-color: var(--warn); }
  details.family-node.grey  { border-left-color: var(--skip); }
  details.family-node > summary {
    cursor: pointer; list-style: none;
    display: flex; flex-wrap: wrap; align-items: center; gap: 0.2em 0.6em;
    padding: 0.55em 0.7em; min-height: 2.5rem;
  }
  details.family-node > summary::-webkit-details-marker { display: none; }
  details.family-node > summary::marker { content: ""; }
  details.family-node > summary::before {
    content: "\25B8"; flex: none; color: var(--muted);
    transition: transform 0.15s ease;
  }
  details.family-node[open] > summary::before { transform: rotate(90deg); }
  details.family-node .fam-name {
    font-weight: 600; color: var(--brand-dark); font-size: 0.98rem;
    flex: 1 1 auto; min-width: 0; overflow-wrap: anywhere;
  }
  details.family-node .fam-score {
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.8rem; color: var(--muted);
    flex: 1 1 100%; /* own line on a narrow phone; see 640px override */
  }
  details.family-node .gap-badge {
    flex: none; font-size: 0.72rem; font-weight: 600;
    background: var(--warn-tint); color: var(--warn);
    border-radius: 10px; padding: 0.1em 0.6em;
  }
  details.family-node > summary .dot { flex: none; }
  details.family-node .family-body { padding: 0 0.8em 0.8em; }
  /* Indentation guide-line: a family's own suite list sits visibly
     nested under its summary, and (one level up) under the group it
     belongs to — the "real visual hierarchy by indentation" the tree
     needs. */
  details.family-node .family-body .suites {
    padding-left: 0.7em; margin-left: 0.15em;
    border-left: 2px solid var(--border);
  }
  .fam-headline {
    margin: 0 0 0.7em; font-size: 0.92rem; color: var(--muted);
    padding-left: 0.9em; border-left: 3px solid var(--border);
  }
  .fam-headline.green { border-left-color: var(--ok); }
  .fam-headline.amber { border-left-color: var(--warn); }
  .fam-headline.grey  { border-left-color: var(--skip); }

  /* "Remaining work" -- what's incomplete, sourced from each suite
     manifest's "remaining:" YAML field (see read_yaml_remaining /
     family_remaining in generate-report.sh). Only one of these two
     renders per family: the list, or the completeness line -- never
     both, and never a fabricated completeness claim when a family has
     fails but no populated "remaining:" yet (family_section renders
     neither in that case). */
  .remaining {
    margin: 0.6em 0 0; padding: 0.6em 0.8em;
    border-left: 4px solid var(--warn); background: var(--warn-tint);
    border-radius: 0 4px 4px 0; font-size: 0.85rem;
  }
  .remaining-title { margin: 0 0 0.3em; font-weight: 600; color: var(--warn); }
  .remaining ul { margin: 0; padding-left: 1.2em; }
  .remaining li { margin: 0.25em 0; overflow-wrap: anywhere; }
  .remaining-complete {
    margin: 0.6em 0 0; font-size: 0.85rem; color: var(--ok);
  }

  /* .fam-subhead — a sub-heading inside an expanded family body (e.g.
     the OWL 2 panel's catalog-scope line). Not a real <h2>: it lives
     inside a collapsed-by-default <details>, so a search-engine/
     accessibility-tree heading here would outrank the page's real
     section structure while being invisible by default. */
  .fam-subhead {
    margin: 0 0 0.35em; font-size: 1.02rem; font-weight: 700;
    color: var(--brand-dark);
  }
  h2 .inline-numbers, .fam-subhead .inline-numbers {
    display: block; font-weight: 400; color: var(--muted); font-size: 0.85rem;
    margin: 0.2em 0 0;
  }
  h2 .inline-numbers a, .fam-subhead .inline-numbers a {
    color: inherit; text-decoration: underline; text-decoration-style: dotted;
  }
  h2 .inline-numbers a:hover, .fam-subhead .inline-numbers a:hover { color: var(--brand-dark); }

  /* Per-REC subsection headings inside SPARQL 1.1 / RDF 1.1 families */
  h3.rec-subhead {
    margin: 1.0em 0 0.35em; font-size: 0.95rem; font-weight: 600;
    color: var(--brand-dark); border-bottom: 1px solid var(--border);
    padding-bottom: 0.2em;
  }
  h3.rec-subhead a {
    color: inherit; text-decoration: none; border-bottom: 1px dotted var(--muted);
  }
  h3.rec-subhead a:hover { color: var(--brand); border-bottom-color: var(--brand); }

  .failure-detail {
    margin: 0.5em 0 1em;
    padding: 0.6em 0.8em;
    border-left: 4px solid var(--muted);
    background: var(--surface);
    border-radius: 3px;
    font-size: 0.88rem;
  }
  .failure-detail summary {
    cursor: pointer; color: var(--muted); padding: 0.4em 0;
    min-height: 44px; display: flex; align-items: center;
  }
  .failure-detail summary:hover { color: var(--brand-dark); }
  .failure-detail ul {
    margin: 0.5em 0 0; padding-left: 1.3em;
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.85rem;
  }
  .failure-detail li { margin: 0.3em 0; line-height: 1.4; overflow-wrap: anywhere; }

  /* --- Suite nodes: one collapsible <details> per checkable suite ------- */
  /* Second pass (2026-07-10): one COMPACT line when collapsed —
     "chevron  name  P/F/S of T  dot" — targeting <=2.5rem row height on
     a phone, not a padded card. flex-wrap:nowrap + ellipsis on the name
     keeps it to one row at any width down to ~320px; the fully-labelled
     "P pass, F fail, S skip (out of T)" sentence and the meter bar only
     render once the row is tapped open (suite-body). */
  .suites { display: flex; flex-direction: column; gap: 0.3em; margin: 0 0 0.4em; }
  details.suite-node {
    margin: 0; border: none; border-radius: 6px;
    background: var(--surface); padding: 0;
  }
  details.suite-node > summary {
    display: flex; flex-wrap: nowrap; align-items: center; gap: 0.5em;
    cursor: pointer; list-style: none;
    padding: 0.35em 0.6em; min-height: 2.5rem; font-size: 0.9rem;
    color: var(--fg); font-weight: 400;
  }
  details.suite-node > summary::-webkit-details-marker { display: none; }
  details.suite-node > summary::marker { content: ""; }
  details.suite-node > summary::before {
    content: "\25B8"; flex: none; color: var(--muted);
    transition: transform 0.15s ease;
  }
  details.suite-node[open] > summary::before { transform: rotate(90deg); }
  details.suite-node .suite-name {
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.85rem; font-weight: 600;
    flex: 1 1 auto; min-width: 0;
    overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
  }
  details.suite-node .suite-numbers {
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.78rem; color: var(--muted); flex: none; white-space: nowrap;
  }
  details.suite-node .suite-body { padding: 0 0.7em 0.7em; display: flex; flex-direction: column; gap: 0.35em; }
  details.suite-node.green { background: var(--ok-tint); }
  details.suite-node.amber { background: var(--warn-tint); }
  details.suite-node.grey  { background: var(--skip-tint); }
  .suite-diag { margin: 0; font-size: 0.8rem; color: var(--muted); }
  /* Fully-labelled "P pass, F fail, S skip (out of T)" — the expanded
     counterpart to the condensed summary line, so the labelled form
     (CLAUDE.md anti-pattern #25) is always one tap away. */
  .suite-numbers-full { margin: -0.2em 0 0; font-size: 0.82rem; color: var(--muted); }

  /* Stacked pass/fail/skip meter — one definition, used by every suite
     row on the page. Always full-width of its row. */
  .meter {
    display: flex; width: 100%; height: 0.85em;
    background: var(--border); border-radius: 3px; overflow: hidden;
  }
  .meter .seg { height: 100%; }
  .meter .seg-pass { background: var(--ok); }
  .meter .seg-fail { background: var(--err); }
  .meter .seg-skip { background: var(--skip); }

  .suite-prov {
    margin: -0.25em 0 0.15em; font-size: 0.78rem; color: var(--muted);
    overflow-wrap: anywhere;
  }
  .suite-prov a { color: var(--brand-dark); }
  .suite-prov code {
    background: var(--surface); padding: 0.05em 0.3em; border-radius: 3px;
    font-size: 0.95em;
  }

  details {
    margin: 1em 0; background: var(--surface); border-radius: 6px;
    padding: 0.4em 0.8em; border: 1px solid var(--border);
  }
  details summary {
    cursor: pointer; font-weight: 500; color: var(--muted);
    font-size: 0.95rem; padding: 0.7em 0.2em;
    min-height: 44px; display: flex; align-items: center;
  }
  details pre {
    background: var(--bg); padding: 0.6em 0.7em;
    border: 1px solid var(--border); border-radius: 4px;
    font-size: 0.8rem; overflow-x: auto; margin: 0.4em 0 0.6em;
    white-space: pre;
  }
  details ul { margin: 0.4em 0 0.6em; padding-left: 1.2em; font-size: 0.92rem; }
  details li { overflow-wrap: anywhere; }
  details code {
    background: var(--bg); padding: 0.1em 0.3em;
    border: 1px solid var(--border); border-radius: 2px;
    font-size: 0.88em; overflow-wrap: anywhere;
  }

  footer {
    max-width: 900px; margin: 2em auto 3em; padding: 1em 0.8em;
    color: var(--muted); font-size: 0.85rem; border-top: 1px solid var(--border);
  }
  footer code { background: var(--surface); padding: 0.1em 0.4em; border-radius: 3px; }

  /* --- Widen past phone width ------------------------------------------ */
  /* The suite/family summary rows are flex-nowrap + ellipsis from the
     base (mobile) rule already, so they stay one compact line at every
     width — no grid re-layout needed past 640px, just more breathing
     room and letting the family score sit inline instead of wrapping to
     its own row. */
  @media (min-width: 640px) {
    main { padding: 1.5em 1em; }
    header { padding: 1.2em 1em; }
    details.suite-node > summary { padding: 0.4em 0.8em; }
    details.family-node > summary { padding: 0.6em 0.9em; }
    details.family-node .fam-score { flex: 0 1 auto; }
    .suite-prov { margin: 0; }
  }
  @media (min-width: 800px) {
    details.group-section .group-body { padding-left: 0.2em; }
  }
  @media (min-width: 760px) {
    header { position: relative; }
    header .inner { position: relative; padding-right: 13em; }
    .rendered-pill {
      position: absolute; top: 0; right: 0; margin: 0;
      white-space: nowrap;
      box-shadow: 0 1px 2px rgba(0,0,0,0.08);
    }
    h2 .inline-numbers, .fam-subhead .inline-numbers { display: inline; margin-left: 0.5em; }
  }
</style>
</head>
<body>

<header>
  <div class="inner">
    <div class="rendered-pill" title="Rendered = when this page was last regenerated. Tests = when the *_results.log files inside the repository were last updated. Both UTC.">
      <span class="row"><span class="label">Rendered</span><strong>${TIMESTAMP_HUMAN}</strong></span>
      <span class="row"><span class="label">Tests</span><strong class="tests">${TESTS_TIMESTAMP_HUMAN}</strong></span>
    </div>
    <h1>W3C test results</h1>
    <p>Pass/fail/skip counts against every standards suite this project measures: RDF 1.1, SPARQL 1.1, RDF 1.2 / SPARQL 1.2 (W3C Working Drafts), RDFS/OWL 2, SHACL, ShEx, RIF Core, RML, CSVW, JSON-LD 1.1, Verifiable Credentials 2.0, XSLT 1.0, XML 1.0, MathML 3, ISO Schematron, JSON Schema, QUDT, DID — plus HDT backend parity and the browser/npm bundle suites.</p>
    <nav>
      <a href="/factoidal/">Home</a>
      <a href="/factoidal/fstar-extracted/">Demos</a>
      <a href="https://github.com/danbri/factoidal">GitHub</a>
    </nav>
  </div>
</header>

<main>

<div class="summary">
  <div class="tile ok">
    <div class="label">Pass</div>
    <div class="value">${COMBINED_PASS}</div>
  </div>
  <div class="tile err">
    <div class="label">Fail</div>
    <div class="value">${COMBINED_FAIL}</div>
  </div>
  <div class="tile warn">
    <div class="label">Skipped</div>
    <div class="value">${COMBINED_SKIP}</div>
  </div>
  <div class="tile">
    <div class="label">Pass / runnable</div>
    <div class="value">${COMBINED_PCT}%<small> of ${run_total}</small></div>
  </div>
  <div class="tile">
    <div class="label">Total in suites</div>
    <div class="value">${COMBINED_TOTAL}</div>
  </div>
</div>

<div class="caveat">
  <strong>Scope.</strong> These counts measure conformance only — whether the
  engine produces the expected result on each vendored fixture. They say
  nothing about performance, memory use, scale, or real-world query shape
  (see the parse/serialize throughput section below for that, measured
  separately). Skipped tests are features not yet implemented or explicitly
  out of scope for the current stage. Raw per-suite logs and machine-readable
  artifacts are linked at the bottom of the page.
</div>

${LEGEND_HTML}

${GROUP1_HTML}
${GROUP_WD_HTML}

${GROUP2_HTML}

${GROUP3_HTML}

${GROUP4_HTML}

${PERF_SECTION_HTML}

<details>
  <summary>Machine-readable artifacts</summary>
  <ul>
    <li><a href="latest.csv"><code>latest.csv</code></a> — one row per suite (timestamp, commit, branch, category, suite, pass/fail/skip/unsupported)</li>
    <li><a href="latest.json"><code>latest.json</code></a> — same data plus totals, structured</li>
    <li><code>history/&lt;timestamp&gt;.csv</code> / <code>.json</code> — timestamped copies, one pair per runner invocation</li>
    <li><a href="perf-parse-serialize.json"><code>perf-parse-serialize.json</code></a> — parse/serialize/canonicalize throughput (if present; produced by <code>tools/bench-parse-serialize.sh</code>, not this script)</li>
  </ul>
  <p style="margin: 0.6em 0 0; color: var(--muted); font-size: 0.9em;">
    The raw runner logs (including per-test FAIL lines with diffs) are committed under
    <code>formal/fstar/ocaml-output/*_results.log</code> — one file per suite, named to
    match each suite's <code>.github/test-suites/&lt;suite&gt;.yaml</code> manifest.
  </p>
</details>

<details>
  <summary>Raw per-suite numbers</summary>
  <h3 style="font-size: 0.95em; margin: 0.8em 0 0.3em;">SPARQL 1.1</h3>
  <pre>${SPARQL_TOTAL} total: ${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip, ${SPARQL_UNSUP} unsupported
${SPARQL_SUITES}</pre>
  <h3 style="font-size: 0.95em; margin: 0.8em 0 0.3em;">RDF 1.1</h3>
  <pre>${RDF_TOTAL} total: ${RDF_PASS} pass, ${RDF_FAIL} fail, ${RDF_SKIP} skip, ${RDF_UNSUP} unsupported
${RDF_SUITES}</pre>
  <h3 style="font-size: 0.95em; margin: 0.8em 0 0.3em;">Shapes / Rules / Mapping / JSON-LD / VC</h3>
  <pre>shacl-core:   ${SHACL_CORE_PASS} pass, ${SHACL_CORE_FAIL} fail, ${SHACL_CORE_SKIP} skip (of ${SHACL_CORE_TOTAL}) — present=${SHACL_CORE_PRESENT}
shacl-sparql: ${SHACL_SPARQL_PASS} pass, ${SHACL_SPARQL_FAIL} fail, ${SHACL_SPARQL_SKIP} skip (of ${SHACL_SPARQL_TOTAL}) — present=${SHACL_SPARQL_PRESENT}
shex:         ${SHEX_PASS} pass, ${SHEX_FAIL} fail, ${SHEX_SKIP} skip (of ${SHEX_TOTAL}) — present=${SHEX_PRESENT}
shex-negative-syntax: ${SHEXNEG_PASS} pass, ${SHEXNEG_FAIL} fail (of ${SHEXNEG_TOTAL}) — present=${SHEXNEG_PRESENT}
jsonld-tordf: ${JSONLD_PASS} pass, ${JSONLD_FAIL} fail, ${JSONLD_SKIP} skip (of ${JSONLD_TOTAL}) — present=${JSONLD_PRESENT}
rml-core:     ${RML_PASS} pass, ${RML_FAIL} fail, ${RML_SKIP} skip (of ${RML_TOTAL}) — present=${RML_PRESENT}
rif-core:     ${RIFCORE_COMBINED_PASS} pass, ${RIFCORE_COMBINED_FAIL} fail, ${RIFCORE_COMBINED_SKIP} skip (of ${RIFCORE_COMBINED_TOTAL}) — present=${RIFCORE_COMBINED_PRESENT}
vc-stage1:    ${VC_PASS} pass, ${VC_FAIL} fail, ${VC_SKIP} skip (of ${VC_TOTAL}) — present=${VC_PRESENT}</pre>
</details>

<details>
  <summary>How this page is generated</summary>
  <p style="margin: 0.5em 0; color: var(--muted); font-size: 0.9em;">
    Source: <code>formal/fstar/generate-report.sh</code>. It shells out to the
    <code>w3c_runner</code> binary (extracted from F* specs, compiled via OCaml),
    scrapes per-suite counts, and writes <code>index.html</code>, <code>latest.csv</code>,
    and <code>latest.json</code>. Run <code>./generate-report.sh --run</code> in
    <code>formal/fstar/</code> to regenerate. CI re-runs on every push and nightly
    at 06:00 UTC.
  </p>
</details>

</main>

<footer>
  Generated <strong>${TIMESTAMP_HUMAN}</strong> from commit
  <code><a href="https://github.com/danbri/factoidal/commit/${GIT_SHA_FULL}">${GIT_SHA}</a></code>
  on branch <code>${GIT_BRANCH}</code>${GIT_SUBJECT_LINE}.
  Re-run locally: <code>cd formal/fstar &amp;&amp; ./generate-report.sh --run</code>.
</footer>

</body>
</html>
HTMLEOF

echo ""
echo "Report generated: $OUTPUT_DIR/index.html"
echo "  CSV:  $CSV  (+ history/${TIMESTAMP_ISO}.csv)"
echo "  JSON: $JSON (+ history/${TIMESTAMP_ISO}.json)"
echo "  SPARQL: ${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip, ${SPARQL_UNSUP} unsupported"
echo "  RDF:    ${RDF_PASS} pass, ${RDF_FAIL} fail, ${RDF_SKIP} skip, ${RDF_UNSUP} unsupported"
echo "  Overall: ${COMBINED_PASS}/${run_total} runnable = ${COMBINED_PCT}%"
if [ "$OWL_PRESENT" -eq 1 ]; then
  echo "  OWL 2 RL (profile-RL PositiveEntailmentTests): ${OWL_PASS} pass, ${OWL_FAIL} fail (out of ${OWL_TOTAL})"
else
  echo "  OWL 2 RL: no cached log ($OWL_LOG); re-run with --run to populate"
fi
report_suite_line () {
  local label="$1" prefix="$2"
  local prv="${prefix}_PRESENT" pv="${prefix}_PASS" fv="${prefix}_FAIL" sv="${prefix}_SKIP" tv="${prefix}_TOTAL"
  if [ "${!prv:-0}" -eq 1 ]; then
    echo "  ${label}: ${!pv} pass, ${!fv} fail, ${!sv} skip (out of ${!tv})"
  else
    echo "  ${label}: not measured this run"
  fi
}
report_suite_line "SHACL Core"        SHACL_CORE
report_suite_line "SHACL SPARQL"      SHACL_SPARQL
report_suite_line "ShEx"              SHEX
report_suite_line "JSON-LD 1.1 toRdf" JSONLD
report_suite_line "RML rml-core"      RML
report_suite_line "RIF Core"          RIFCORE_COMBINED
report_suite_line "VC 2.0 (Stage 1)"  VC
report_suite_line "XSLT 1.0"          XSLT
report_suite_line "XML conformance"   XMLCONF
report_suite_line "MathML 3"          MATHML
report_suite_line "JSON Schema"       JSONSCHEMA
report_suite_line "Schematron"        SCHEMATRON
report_suite_line "CSVW csv2rdf"      CSVW2RDF
report_suite_line "DID did:key"       DIDKEY
report_suite_line "JSON-LD fromRdf"   JSONLD_FROMRDF
report_suite_line "JSON-LD expand"    JSONLD_EXPAND
report_suite_line "JSON-LD compact"   JSONLD_COMPACT
report_suite_line "HDT stage-4 parity" HDT_PARITY
report_suite_line "hub bundle"        HUB
report_suite_line "npm package"       NPM
echo "  Commit: ${GIT_SHA} (${GIT_BRANCH})"
