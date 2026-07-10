#!/usr/bin/env bash
# tests/vc-api-shim/run.sh — smoke test for bin/vc-api-shim/server.mjs
# (task #88, canivc.com community-compatibility integration).
#
# Starts the shim, issues a credential, verifies it (expect verified
# true), tampers with it and verifies again (expect verified false),
# then kills the shim. Exits non-zero on any unexpected outcome.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PORT="${VC_API_SHIM_TEST_PORT:-40488}"
LOG="$(mktemp)"

cleanup() {
  if [[ -n "${SHIM_PID:-}" ]] && kill -0 "$SHIM_PID" 2>/dev/null; then
    kill "$SHIM_PID" 2>/dev/null || true
    wait "$SHIM_PID" 2>/dev/null || true
  fi
  rm -f "$LOG"
}
trap cleanup EXIT

node "$REPO_ROOT/bin/vc-api-shim/server.mjs" --port "$PORT" > "$LOG" 2>&1 &
SHIM_PID=$!

# Wait for the deterministic startup log line, capped at 10s.
for _ in $(seq 1 50); do
  if grep -q "vc-api-shim listening on" "$LOG" 2>/dev/null; then
    break
  fi
  sleep 0.2
done
if ! grep -q "vc-api-shim listening on" "$LOG" 2>/dev/null; then
  echo "FAIL: shim did not print its startup line within 10s"
  cat "$LOG"
  exit 1
fi

BASE="http://localhost:$PORT"

ISSUE_BODY='{"credential": {"@context": ["https://www.w3.org/ns/credentials/v2"], "type": ["VerifiableCredential"], "issuer": "did:example:issuer1", "credentialSubject": {"id": "did:example:subject1", "name": "Alice"}}}'
ISSUE_RESP="$(curl -sS -X POST "$BASE/credentials/issue" -H 'Content-Type: application/json' -d "$ISSUE_BODY")"

VC="$(python3 -c "import json,sys; print(json.dumps(json.loads(sys.argv[1])['verifiableCredential']))" "$ISSUE_RESP")"
if [[ -z "$VC" || "$VC" == "null" ]]; then
  echo "FAIL: issue did not return verifiableCredential"
  echo "$ISSUE_RESP"
  exit 1
fi

VERIFY_RESP="$(curl -sS -X POST "$BASE/credentials/verify" -H 'Content-Type: application/json' -d "{\"verifiableCredential\": $VC}")"
VERIFIED="$(python3 -c "import json,sys; print(json.loads(sys.argv[1])['verified'])" "$VERIFY_RESP")"
if [[ "$VERIFIED" != "True" ]]; then
  echo "FAIL: verify(correct credential) expected verified:true, got:"
  echo "$VERIFY_RESP"
  exit 1
fi
echo "PASS: issue + verify roundtrip -> verified:true"

TAMPERED_VC="$(python3 -c "
import json, sys
d = json.loads(sys.argv[1])
d['credentialSubject']['name'] = 'TAMPERED'
print(json.dumps(d))
" "$VC")"
TAMPER_RESP="$(curl -sS -X POST "$BASE/credentials/verify" -H 'Content-Type: application/json' -d "{\"verifiableCredential\": $TAMPERED_VC}")"
TAMPER_VERIFIED="$(python3 -c "import json,sys; print(json.loads(sys.argv[1])['verified'])" "$TAMPER_RESP")"
if [[ "$TAMPER_VERIFIED" != "False" ]]; then
  echo "FAIL: verify(tampered credential) expected verified:false, got:"
  echo "$TAMPER_RESP"
  exit 1
fi
echo "PASS: tampered credential -> verified:false"

echo "tests/vc-api-shim/run.sh: ALL PASS"
