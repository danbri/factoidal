#!/usr/bin/env bash
# tools/xmpp-interop.sh — drive the Factoidal XMPP server with a REAL
# third-party client library over a REAL socket, through the same socat
# carrier line the deployment uses.
#
# Exit codes:
#   0  the interop ran and passed
#   1  the interop ran and FAILED
#   2  the interop could NOT run, with the reason on stderr
#
# There is no green skip. A missing socat or a missing client library is
# exit 2, because "the interop did not run" and "the interop passed" are
# different facts and a suite that reports them the same way is lying
# about its coverage.
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$REPO/formal/lean4/.lake/build/bin/l4xmpp-serve"
CLIENT_TEST="$REPO/tests/xmpp/interop-client.mjs"

fail_setup () { echo "xmpp-interop: $1" >&2; exit 2; }

command -v node >/dev/null 2>&1 || fail_setup "node is not on PATH"

[ -x "$BIN" ] || fail_setup \
  "l4xmpp-serve is not built at $BIN — run: (cd $REPO/formal/lean4 && lake build l4xmpp-serve)"

command -v socat >/dev/null 2>&1 || fail_setup \
  "socat is not installed. It is the carrier: the deployment's whole
        non-Lean surface is one socat line (deploy/fly/xmpp/entrypoint.sh).
        Install it (Debian: apt-get install socat; macOS: brew install socat)
        and run again. This is exit 2, not a pass: the interop did not run."

# @xmpp/client is a test-only dependency. It is looked for in three
# places so a checkout that has not run `npm install` says so plainly.
CLIENT_DIR=""
for d in "$REPO/tests/xmpp" "$REPO" "${XMPP_CLIENT_PREFIX:-/nonexistent}"; do
  if [ -d "$d/node_modules/@xmpp/client" ]; then CLIENT_DIR="$d"; break; fi
done
[ -n "$CLIENT_DIR" ] || fail_setup \
  "@xmpp/client is not installed. It is a test-only dependency and the
        only third-party XMPP code this repository uses — its job is to be
        an implementation we did not write. Install it with:
          (cd $REPO/tests/xmpp && npm install)
        or point XMPP_CLIENT_PREFIX at a directory whose node_modules has
        it. This is exit 2, not a pass."

[ -f "$CLIENT_TEST" ] || fail_setup "missing $CLIENT_TEST"

STATE="$(mktemp -d "${TMPDIR:-/tmp}/l4xmpp-interop.XXXXXX")"
PORT="${XMPP_INTEROP_PORT:-15222}"
DOMAIN="${XMPP_INTEROP_DOMAIN:-localhost}"
printf 'juliet:r0m30\nromeo:juli3t\n' > "$STATE/accounts"

cleanup () {
  [ -n "${CARRIER_PID:-}" ] && kill "$CARRIER_PID" 2>/dev/null
  rm -rf "$STATE"
}
trap cleanup EXIT

# THE CARRIER LINE. This is the plaintext variant of what
# deploy/fly/xmpp/entrypoint.sh runs on 5223 with OPENSSL-LISTEN; the
# only difference is the TLS termination, which a local test does not
# need and @xmpp/client would need a certificate for.
socat "TCP-LISTEN:$PORT,reuseaddr,fork" \
  "EXEC:$BIN --domain $DOMAIN --state $STATE --plaintext,pipes" &
CARRIER_PID=$!

# Wait for the listener rather than sleeping a guess.
for _ in $(seq 1 50); do
  if node -e "require('net').connect($PORT,'127.0.0.1').on('connect',function(){this.end();process.exit(0)}).on('error',()=>process.exit(1))" 2>/dev/null; then
    break
  fi
  sleep 0.1
done

# `cd` rather than NODE_PATH: ES module resolution ignores NODE_PATH, so
# the import only resolves when node's working directory is inside a tree
# whose node_modules has the package (measured 2026-09-07 — the NODE_PATH
# form failed with ERR_MODULE_NOT_FOUND).
cd "$CLIENT_DIR" || fail_setup "cannot enter $CLIENT_DIR"
node "$CLIENT_TEST" "$PORT" "$DOMAIN"
RC=$?
exit $RC
