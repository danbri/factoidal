#!/usr/bin/env bash
# solid-client-interop.sh — run OUR Solid client against Community Solid
# Server, the Solid Protocol reference implementation.
# https://github.com/danbri/factoidal/issues/659
#
# `tests/solid/client/against-own-server.mjs` puts our client and our
# server on the two ends of one socket, so a shared misreading of the
# specification passes it. This script replaces the far end with CSS.
#
# EXIT CODES
#   0  the client operations passed against CSS
#   1  an operation failed
#   2  the run could not happen here, with the reason printed
#
# A run that could not happen is never a pass (anti-pattern 3).
#
# DISK
# `npx @solid/community-server` downloads about 250 MB into the npm cache
# on a machine that has never installed it. The script refuses to start
# that download with less than 2 GB free and says so.

set -u -o pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
if [ -z "$ROOT" ]; then
  echo "solid-client-interop: not inside a git checkout" >&2
  exit 2
fi
cd "$ROOT"

PORT="${SOLID_CSS_PORT:-3003}"
SCRATCH="${SOLID_CSS_DATA:-${TMPDIR:-/tmp}/factoidal-css-$$}"
CSS_LOG="$(mktemp -t css-log)"
CSS_PID=""

cleanup() {
  if [ -n "$CSS_PID" ]; then kill "$CSS_PID" 2> /dev/null || true; fi
  rm -rf "$SCRATCH"
  rm -f "$CSS_LOG"
}
trap cleanup EXIT

# ---------------------------------------------------------------- inputs

if ! command -v node > /dev/null 2>&1; then
  echo "solid-client-interop: node is not on PATH." >&2
  exit 2
fi
if ! command -v npx > /dev/null 2>&1; then
  echo "solid-client-interop: npx is not on PATH, so Community Solid Server" >&2
  echo "  cannot be started. Install it and rerun." >&2
  exit 2
fi

# Free space, in whole gigabytes, on the filesystem the npm cache is on.
FREE_KB="$(df -Pk "${HOME}" | awk 'NR==2 {print $4}')"
if [ -n "$FREE_KB" ] && [ "$FREE_KB" -lt 2097152 ]; then
  echo "solid-client-interop: only $((FREE_KB / 1024)) MB free under $HOME."
  echo "  Community Solid Server needs about 250 MB of npm cache and this"
  echo "  script refuses to start that download below 2 GB free."
  echo "solid-client vs community-solid-server: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi

# One probe before the download: a WebAssembly module without the Solid
# client operations cannot drive anything, and saying so costs seconds.
PROBE_RC=0
PROBE_OUT="$(node -e '
  const load = async () => {
    const { loadEngine } = await import("./npm/factoidal/bin/engine.mjs")
    const m = await import("./npm/factoidal/solid/client/index.mjs")
    const probe = await m.solidClientOpsAvailable(await loadEngine())
    if (!probe.available) { console.log(probe.reason); process.exitCode = 3 }
  }
  load().catch((error) => { console.log(error.message); process.exitCode = 3 })
' 2>&1)" || PROBE_RC=$?
if [ "$PROBE_RC" -ne 0 ]; then
  echo "solid-client-interop: our Solid client cannot run these operations."
  echo "  $PROBE_OUT"
  echo "solid-client vs community-solid-server: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi

# ------------------------------------------------- Community Solid Server

mkdir -p "$SCRATCH"
echo "solid-client-interop: starting Community Solid Server on port $PORT"
npx --yes @solid/community-server \
  -p "$PORT" -c @css:config/file-no-setup.json -f "$SCRATCH" \
  > "$CSS_LOG" 2>&1 &
CSS_PID=$!

ORIGIN="http://localhost:${PORT}"
UP=0
for _ in $(seq 1 120); do
  if curl -s -o /dev/null "$ORIGIN/"; then UP=1; break; fi
  if ! kill -0 "$CSS_PID" 2> /dev/null; then break; fi
  sleep 1
done

if [ "$UP" -ne 1 ]; then
  echo "solid-client-interop: Community Solid Server did not come up on $ORIGIN." >&2
  tail -n 20 "$CSS_LOG" | sed 's/^/  /' >&2
  echo "solid-client vs community-solid-server: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi
echo "solid-client-interop: Community Solid Server is at $ORIGIN"

# ------------------------------------------------------------ the client

RC=0
node tests/solid/client/against-community-server.mjs --origin "$ORIGIN" || RC=$?
exit "$RC"
