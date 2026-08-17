#!/usr/bin/env bash
# tests/local/rdfs_entailment_regime_regressions.sh
#
# Regression pin for finding RS-4 of
# docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md (issue
# #335): RDF.Entailment.Regime.fst defined a one-argument `rdfs_closure`
# that SHADOWED RDFS.Closure's two-argument RDFS rule driver, so the
# rdf12 manifests' "RDFS" entailment regime applied exactly one rule --
# the RDF 1.2 rdf:reifies range step -- and none of rdfs1-rdfs13.
#
# Why this script exists at all: the W3C rdf-semantics manifest CANNOT
# detect that regression. It carries two "RDFS" tests (reifies-range,
# triple-terms-propositions) and two "RDFS-Plus" tests (opaque-iri,
# opaque-iri-control), and none of the four mentions rdfs:subClassOf,
# rdfs:domain, rdfs:range or rdfs:subPropertyOf. Both scores are
# identical before and after the fix. Without this pin the fix is
# unfalsifiable and could silently regress.
#
# It compiles tests/local/rdfs_entailment_regime_probe.ml -- a throwaway
# OCaml test driver, the same ad-hoc-harness-compiled-by-its-own-script
# convention as tests/local/rml_virtual_pushdown_probe.ml and
# tests/local/delta_log_crash_harness.sh's probe.ml, NOT registered in
# build-ocaml.sh -- against the extracted .cmx files, and calls
# RDF_Entailment_Regime.entails_rdf / entails_rdfs / entails_rdfs_plus
# directly. Every function it calls is Tot; the verdicts are values.
#
# Per rule #17 every external process is bounded with `timeout`.
# Per rule #25 counts are labelled, never a bare ratio.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OCAML_OUT="${ROOT}/formal/fstar/ocaml-output"
BUILD_SH="${ROOT}/formal/fstar/build-ocaml.sh"
PROBE_ML="${ROOT}/tests/local/rdfs_entailment_regime_probe.ml"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/factoidal-rdfs-regime-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

note() { echo "== $* =="; }

if [[ ! -f "${OCAML_OUT}/RDF_Entailment_Regime.cmx" ]]; then
  echo "rdfs_entailment_regime_regressions: extracted objects missing: ${OCAML_OUT}/RDF_Entailment_Regime.cmx" >&2
  echo "(run 'cd formal/fstar && ./build-ocaml.sh extract' first)" >&2
  exit 2
fi

# Link order is READ OUT OF build-ocaml.sh's own COMMON_MODULES list
# rather than copied into this file, so a module inserted upstream
# cannot silently desynchronise this harness (anti-pattern #27). Take
# the ordered prefix up to and including RDF_Entailment_Regime.ml --
# everything the probe needs (Parser_Turtle, XSD_Datatypes,
# XSD_IEEE754, Parser_JSON, RDF_Entailment_Simple) sits earlier in it.
note "deriving link order from build-ocaml.sh COMMON_MODULES"
# The `COMMON_MODULES="` opener sits flush against the first module
# name, so strip it (and the closing quote) before tokenising -- else
# the first token reads `COMMON_MODULES=".ml`.
MODULE_LINE="$(sed -n '/^  COMMON_MODULES="/,/[^\\]$/p' "${BUILD_SH}" \
  | tr -d '\\' | tr '\n' ' ' | sed -e 's/^ *COMMON_MODULES="//' -e 's/"//g')"
CMX_LIST=()
FOUND_REGIME=0
for tok in ${MODULE_LINE}; do
  case "${tok}" in
    *.ml)
      m="${tok%.ml}"
      CMX_LIST+=("${OCAML_OUT}/${m}.cmx")
      if [[ "${m}" == "RDF_Entailment_Regime" ]]; then FOUND_REGIME=1; break; fi
      ;;
  esac
done

if [[ ${FOUND_REGIME} -ne 1 ]]; then
  echo "rdfs_entailment_regime_regressions: RDF_Entailment_Regime.ml not found in build-ocaml.sh COMMON_MODULES" >&2
  exit 2
fi
echo "link order: ${#CMX_LIST[@]} modules, ending at RDF_Entailment_Regime"

if ! command -v ocamlfind >/dev/null 2>&1; then
  eval "$(opam env --switch=fstar 2>/dev/null)" || true
fi
if ! command -v ocamlfind >/dev/null 2>&1; then
  echo "rdfs_entailment_regime_regressions: ocamlfind not on PATH (rule #12: eval \$(opam env --switch=fstar))" >&2
  exit 2
fi

# The prefix includes the Parquet/COTTAS writers, which pull the zstd
# stub object; same probe-link boilerplate as virtual_rml_stage5.sh.
ZSTD_LIB_FLAGS=()
for dir in /opt/homebrew/lib /opt/homebrew/opt/zstd/lib \
           /usr/local/lib /usr/lib /usr/lib/x86_64-linux-gnu \
           /usr/lib/aarch64-linux-gnu; do
  if [[ -f "${dir}/libzstd.a" || -f "${dir}/libzstd.so" || -f "${dir}/libzstd.dylib" ]]; then
    ZSTD_LIB_FLAGS=(-cclib "-L${dir}" -cclib -lzstd)
    break
  fi
done

STUB_OBJ=()
if [[ -f "${OCAML_OUT}/parquet_zstd_stubs.o" ]]; then
  STUB_OBJ=("${OCAML_OUT}/parquet_zstd_stubs.o")
fi

PROBE_BIN="${WORKDIR}/rdfs_entailment_regime_probe"
# ocamlopt writes the probe's .cmi / .cmx / .o beside its SOURCE, so
# compile from a copy inside WORKDIR and leave tests/local clean.
cp "${PROBE_ML}" "${WORKDIR}/rdfs_entailment_regime_probe.ml"
note "building rdfs_entailment_regime_probe"
BUILD_RC=0
BUILD_OUT=$(cd "${WORKDIR}" && timeout 600 ocamlfind ocamlopt \
  -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp \
  -linkpkg -w -8-14-26 \
  -I "${OCAML_OUT}" \
  "${CMX_LIST[@]}" \
  "${STUB_OBJ[@]}" \
  "${ZSTD_LIB_FLAGS[@]}" \
  "${WORKDIR}/rdfs_entailment_regime_probe.ml" \
  -o "${PROBE_BIN}" 2>&1) || BUILD_RC=$?

if [[ ${BUILD_RC} -ne 0 ]]; then
  echo "FAIL: probe failed to build (rc=${BUILD_RC})"
  echo "${BUILD_OUT}" | sed 's/^/  /'
  exit 1
fi

note "running rdfs_entailment_regime_probe"
PROBE_RC=0
PROBE_OUT="$(timeout 120 "${PROBE_BIN}")" || PROBE_RC=$?
echo "${PROBE_OUT}"

NCHECKS=$(printf '%s\n' "${PROBE_OUT}" | grep -cE '^(ok  |FAIL) ')
NFAIL=$(printf '%s\n' "${PROBE_OUT}" | grep -cE '^FAIL ')
NPASS=$(( NCHECKS - NFAIL ))

echo
echo "rdfs_entailment_regime_regressions: ${NPASS} pass, ${NFAIL} fail (out of ${NCHECKS} checks)"

if [[ ${PROBE_RC} -ne 0 || ${NFAIL} -ne 0 || ${NCHECKS} -eq 0 ]]; then
  exit 1
fi
exit 0
