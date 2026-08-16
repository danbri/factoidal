#!/usr/bin/env bash
# tests/local/parquet_footer_version_gate_roundtrip.sh — end-to-end pin
# for issue #448 (assurance-triage wave 1, module 1 of 5: Parquet.Footer).
#
# What this covers, and why it exists alongside the F* proof:
#
# RDF.CottasStore.BaseWriter.lemma_version_field_roundtrip proves, in
# pure F*, that the writer's `write_field_i32 1 0 cottas_format_version`
# and Parquet.Footer's `parse_file_metadata_version_hex` agree on the
# compact-protocol encoding of the #445 format-version field, for the
# CONCRETE deployed constant (445). That lemma stops at the F*/OCaml
# boundary: it says nothing about whether a real disk write, followed
# by a real disk read and hex-encode (the `parquet_read_tail_hex`
# assume val's OCaml realisation), actually delivers the bytes the
# lemma assumes it delivers. This script is the other half: it writes
# a REAL store to REAL disk through the REAL CLI, and confirms the
# on-disk version gate (RDF.CottasStore.cottas_ondisk_version_ok,
# enforced by cottas_ondisk_open before any query can run) does its
# job against actual bytes.
#
#   Arm A  A freshly imported store has query access. This is the
#          POSITIVE case: the writer's own bytes pass its own gate.
#
#   Arm B  ANTI-VACUITY. Flip the single byte the #445 field-1 varint's
#          second byte occupies on disk (890 = zigzag(445) -> the two
#          varint bytes 0xFA,0x06; flipping the second changes the
#          decoded version away from 445) and require the SAME query
#          to be rejected with the version-gate error, not silently
#          served stale/wrong data. A degenerate "gate" that never
#          actually checks anything would pass Arm A and also pass
#          Arm B by accident (query would still work) -- Arm B is
#          written so that failure mode goes red.
#
# Rule anchors: #14 (no swallowed exit codes), #25 (labelled counts).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then
  BIN="${ROOT}/bin/linux-x86_64/factoidal"
fi
if [ ! -x "${BIN}" ]; then
  echo "parquet_footer_version_gate_roundtrip: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-version-gate-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0
report_pass() { PASS=$((PASS + 1)); echo "PASS  $1"; }
report_fail() { FAIL=$((FAIL + 1)); echo "FAIL  $1"; }

FIXTURE="${WORKDIR}/fixture.nq"
cat > "${FIXTURE}" <<'EOF'
<http://e/s1> <http://e/p> "one" .
<http://e/s2> <http://e/p> "two" .
<http://e/s3> <http://e/p> "three" .
EOF
EXPECTED_TRIPLES=3

STORE="${WORKDIR}/store"
"${BIN}" import --nq "${FIXTURE}" --out "${STORE}" > "${WORKDIR}/import.log" 2>&1
IMPORT_RC=$?
if [ "${IMPORT_RC}" -ne 0 ]; then
  report_fail "arm A: import exited ${IMPORT_RC}"
  cat "${WORKDIR}/import.log"
  echo
  echo "parquet_footer_version_gate_roundtrip: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
  exit 1
fi

ARTIFACT="$(find "${STORE}" -name 'data.cottas' | head -1)"
if [ -z "${ARTIFACT}" ]; then
  report_fail "arm A: no data.cottas artifact found under ${STORE}"
  echo
  echo "parquet_footer_version_gate_roundtrip: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
  exit 1
fi

# ---------------------------------------------------------------------
# Arm A: a freshly written store passes its own version gate.
# ---------------------------------------------------------------------
QOUT_GOOD="${WORKDIR}/query_good.out"
"${BIN}" query --data-cottas "${ARTIFACT}" \
  -e 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' > "${QOUT_GOOD}" 2>&1
QUERY_GOOD_RC=$?
N_GOOD="$(grep -oE '^[0-9]+ result' "${QOUT_GOOD}" | grep -oE '^[0-9]+')"
if [ "${QUERY_GOOD_RC}" -eq 0 ] && [ "${N_GOOD:-0}" = "${EXPECTED_TRIPLES}" ]; then
  report_pass "arm A: freshly written store queries cleanly (${EXPECTED_TRIPLES} rows)"
else
  report_fail "arm A: query on a freshly written store failed (rc=${QUERY_GOOD_RC}, rows=${N_GOOD:-<none>})"
  cat "${QOUT_GOOD}"
fi

# ---------------------------------------------------------------------
# Locate the field-1 (version) varint bytes on disk: header byte 0x15
# (short-form field header: delta=1, type=i32=5 -> (1<<4)|5=0x15),
# followed by the 2-byte LEB128 varint for zigzag_encode_nat(445)=890
# (0xFA, 0x06 -- see RDF.CottasStore.BaseWriter.write_field_i32 /
# Parquet.Footer.cottas_format_version). build_file_metadata always
# writes field 1 FIRST, so this 3-byte sequence should appear exactly
# once, at the start of the FileMetaData struct.
# ---------------------------------------------------------------------
CORRUPT="${WORKDIR}/corrupt.cottas"
python3 - "${ARTIFACT}" "${CORRUPT}" > "${WORKDIR}/corrupt.log" 2>&1 <<'PY'
import sys
src, dst = sys.argv[1], sys.argv[2]
data = bytearray(open(src, "rb").read())
pattern = bytes([0x15, 0xFA, 0x06])
occurrences = [i for i in range(len(data) - 2) if data[i:i+3] == pattern]
if len(occurrences) != 1:
    print(f"expected exactly one occurrence of {pattern.hex()}, found {len(occurrences)}: {occurrences}")
    sys.exit(1)
idx = occurrences[0]
# Flip the second varint byte (0x06 -> 0x07): payload changes from
# 6*128=768 to 7*128=896, so the decoded zigzag value becomes
# 122+896=1018, zigzag_decode_nat(1018)=509 -- not 445.
data[idx + 2] = 0x07
open(dst, "wb").write(data)
print(f"corrupted byte at offset {idx + 2}: 0x06 -> 0x07")
PY
CORRUPT_RC=$?
if [ "${CORRUPT_RC}" -ne 0 ]; then
  report_fail "arm B setup: could not locate/corrupt the version field bytes"
  cat "${WORKDIR}/corrupt.log"
  echo
  echo "parquet_footer_version_gate_roundtrip: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
  exit 1
fi
report_pass "arm B setup: located and flipped the version field's second varint byte"

# ---------------------------------------------------------------------
# Arm B: ANTI-VACUITY. The corrupted store must be REJECTED, not
# silently queried.
# ---------------------------------------------------------------------
QOUT_BAD="${WORKDIR}/query_bad.out"
"${BIN}" query --data-cottas "${CORRUPT}" \
  -e 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' > "${QOUT_BAD}" 2>&1
QUERY_BAD_RC=$?
if [ "${QUERY_BAD_RC}" -eq 0 ]; then
  report_fail "arm B: query on a store with a corrupted version field SUCCEEDED (rc=0) -- the version gate did not fire"
  cat "${QOUT_BAD}"
elif grep -qi "could not open on-disk COTTAS artifact" "${QOUT_BAD}"; then
  report_pass "arm B: query on a corrupted-version store is rejected with the version-gate error"
else
  report_fail "arm B: query on a corrupted-version store failed (rc=${QUERY_BAD_RC}) but not with the expected version-gate message"
  cat "${QOUT_BAD}"
fi

echo
echo "parquet_footer_version_gate_roundtrip: ${PASS} pass, ${FAIL} fail (out of $((PASS + FAIL)))"
[ "${FAIL}" -eq 0 ]
