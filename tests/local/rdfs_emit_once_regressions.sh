#!/usr/bin/env bash
# tests/local/rdfs_emit_once_regressions.sh
#
# Regression pin for issue #340 item (4) and section 10.5.1 of
# docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md.
#
# WHAT THIS PINS. #340 item (4) proposed HOISTING the five RS-2 rule
# rows (rdfs1, rdfs4a, rdfs4b, rdfs8, rdfs13) out of
# `RDFS.Closure.rdfs_closure_step` and running them once after the fixed
# point, on the reading that they are non-recursive. They are not: every
# one of them emits a triple that is a premise of rdfs9 or rdfs11, both
# of which stay in the loop. A hoist therefore loses derivations, and it
# loses them SILENTLY -- no W3C suite in this tree goes red.
#
# The fix that landed instead (`RDFS.Closure.snapshot_carries` /
# `emit_once`) keeps all twelve rows in the loop and only suppresses a
# re-emission the step's index snapshot already carries, so it must NOT
# lose any of these. This script is what makes both claims falsifiable.
#
# Each case below is a two-or-fewer-triple graph whose RDFS closure
# contains a triple that exists ONLY because a RS-2 row fed rdfs9 or
# rdfs11 inside the loop. If a future change hoists a row, or breaks the
# emit-once guard's set-neutrality, the matching line disappears and this
# script exits non-zero.
#
# Per rule #17 every external process is bounded with `timeout`.
# Per rule #25 counts are labelled, never a bare ratio.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
FACTOIDAL="${FACTOIDAL_BIN:-${ROOT}/bin/linux-x86_64/factoidal}"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/factoidal-rdfs-emit-once-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

RDF="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDFS="http://www.w3.org/2000/01/rdf-schema#"
XSD="http://www.w3.org/2001/XMLSchema#"
EX="http://ex.org/"

if [[ ! -x "${FACTOIDAL}" ]]; then
  echo "rdfs_emit_once_regressions: factoidal binary not found or not executable: ${FACTOIDAL}" >&2
  echo "(set FACTOIDAL_BIN, or run 'cd formal/fstar && ./build-ocaml.sh' first)" >&2
  exit 2
fi

PASS=0
FAIL=0
TOTAL=0

# run_case <name> <graph-file> <expected-triple-line> <why>
run_case() {
  local name="$1" graph="$2" expected="$3" why="$4"
  TOTAL=$((TOTAL + 1))
  local out="${WORKDIR}/${name}.nq"
  local rc=0
  timeout 120 "${FACTOIDAL}" entail --data "${graph}" --regime RDFS > "${out}" 2>"${WORKDIR}/${name}.err" || rc=$?
  if [[ "${rc}" -ne 0 ]]; then
    echo "FAIL ${name}: factoidal entail exited ${rc}"
    sed -e 's/^/       /' "${WORKDIR}/${name}.err"
    FAIL=$((FAIL + 1))
    return
  fi
  if grep -qxF "${expected}" "${out}"; then
    echo "ok   ${name}  (${why})"
    PASS=$((PASS + 1))
  else
    echo "FAIL ${name}: closure is missing the derivation this case pins"
    echo "       why      : ${why}"
    echo "       expected : ${expected}"
    echo "       closure had $(wc -l < "${out}") triples; premise graph:"
    sed -e 's/^/         /' "${graph}"
    FAIL=$((FAIL + 1))
  fi
}

echo "== rdfs emit-once / no-hoist regression pin =="
echo "   binary: ${FACTOIDAL}"

# ---- case A: rdfs13 feeds rdfs9 -------------------------------------
# rdfs13 gives  :d rdfs:subClassOf rdfs:Literal
# rdfs9  then gives  :a rdf:type rdfs:Literal
# Nothing else in the rule table produces that conclusion, so a hoisted
# rdfs13 loses it. Note how ordinary the premise graph is: declare a
# datatype, use it.
cat > "${WORKDIR}/a.nt" <<EOF
<${EX}d> <${RDF}type> <${RDFS}Datatype> .
<${EX}a> <${RDF}type> <${EX}d> .
EOF
run_case "rdfs13-feeds-rdfs9" "${WORKDIR}/a.nt" \
  "<${EX}a> <${RDF}type> <${RDFS}Literal> ." \
  "rdfs13 then rdfs9"

# ---- case B: rdfs1 feeds rdfs13 feeds rdfs9 -------------------------
# rdfs1 has no data premise at all; it emits xsd:string rdf:type
# rdfs:Datatype, which is exactly rdfs13's premise.
cat > "${WORKDIR}/b.nt" <<EOF
<${EX}a> <${RDF}type> <${XSD}string> .
EOF
run_case "rdfs1-feeds-rdfs13" "${WORKDIR}/b.nt" \
  "<${XSD}string> <${RDFS}subClassOf> <${RDFS}Literal> ." \
  "rdfs1 then rdfs13"
run_case "rdfs1-feeds-rdfs13-feeds-rdfs9" "${WORKDIR}/b.nt" \
  "<${EX}a> <${RDF}type> <${RDFS}Literal> ." \
  "rdfs1 then rdfs13 then rdfs9"

# ---- case C: rdfs8 feeds rdfs11 -------------------------------------
# rdfs8 gives  :C rdfs:subClassOf rdfs:Resource ; with an asserted
# rdfs:Resource rdfs:subClassOf :Top, rdfs11 gives :C rdfs:subClassOf
# :Top. Saying something about rdfs:Resource is unusual but perfectly
# legal RDFS, and it is exactly what an RDFS test suite probes.
cat > "${WORKDIR}/c.nt" <<EOF
<${EX}C> <${RDF}type> <${RDFS}Class> .
<${RDFS}Resource> <${RDFS}subClassOf> <${EX}Top> .
EOF
run_case "rdfs8-feeds-rdfs11" "${WORKDIR}/c.nt" \
  "<${EX}C> <${RDFS}subClassOf> <${EX}Top> ." \
  "rdfs8 then rdfs11"

# ---- case D: rdfs4a / rdfs4b feed rdfs9 -----------------------------
# rdfs4a gives  :a rdf:type rdfs:Resource ; rdfs4b gives the same for
# the object :b. With rdfs:Resource rdfs:subClassOf :Top asserted,
# rdfs9 types every term.
cat > "${WORKDIR}/d.nt" <<EOF
<${EX}a> <${EX}p> <${EX}b> .
<${RDFS}Resource> <${RDFS}subClassOf> <${EX}Top> .
EOF
run_case "rdfs4a-feeds-rdfs9" "${WORKDIR}/d.nt" \
  "<${EX}a> <${RDF}type> <${EX}Top> ." \
  "rdfs4a then rdfs9"
run_case "rdfs4b-feeds-rdfs9" "${WORKDIR}/d.nt" \
  "<${EX}b> <${RDF}type> <${EX}Top> ." \
  "rdfs4b then rdfs9"

# ---- case E: the guard did not suppress a first emission ------------
# The emit-once guard skips a row's emission when the step's index
# SNAPSHOT already carries the triple. If it ever suppressed a FIRST
# emission the rows would vanish entirely, so pin one plain rdfs4a
# conclusion on a graph that asserts nothing about the RDFS vocabulary.
cat > "${WORKDIR}/e.nt" <<EOF
<${EX}s> <${EX}q> <${EX}o> .
EOF
run_case "rdfs4a-fires-at-all" "${WORKDIR}/e.nt" \
  "<${EX}s> <${RDF}type> <${RDFS}Resource> ." \
  "rdfs4a, emitted once"
run_case "rdfs4b-fires-at-all" "${WORKDIR}/e.nt" \
  "<${EX}o> <${RDF}type> <${RDFS}Resource> ." \
  "rdfs4b, emitted once"

echo
echo "rdfs emit-once / no-hoist pin: ${PASS} pass, ${FAIL} fail (out of ${TOTAL})"
if [[ "${FAIL}" -ne 0 ]]; then
  exit 1
fi
exit 0
