#!/usr/bin/env bash
# solid-conformance-harness.sh — run the Solid specification tests
# (solid-contrib/specification-tests, Gherkin, executed by
# solid-contrib/conformance-test-harness) against OUR Solid server.
# https://github.com/danbri/factoidal/issues/659
#
# The harness is a Java program distributed as the Docker image
# `solidconformancetestbeta/conformance-test-harness`. There is no
# Docker-free route: the image carries the Karate runtime and the report
# generator, and the tests are read from
# third_party/testing/solid-specification-tests.
#
# EXIT CODES
#   0  the harness ran and reported no failure
#   1  the harness ran and reported a failure
#   2  the harness could not be run here, with the reason printed
#
# A run that could not happen is never a pass (anti-pattern 3).
#
# AUTHENTICATION
# The specification tests log in as two agents through Solid-OIDC before
# their first request. Our server has no token verification yet (design
# record, section 2), so this script needs the credentials of a server
# that does, supplied through SOLID_HARNESS_ENV. Without them the harness
# is not started, and this script says so rather than reporting an empty
# pass.

set -u -o pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
if [ -z "$ROOT" ]; then
  echo "solid-conformance-harness: not inside a git checkout" >&2
  exit 2
fi
cd "$ROOT"

TESTS="$ROOT/third_party/testing/solid-specification-tests"
IMAGE="${SOLID_HARNESS_IMAGE:-solidconformancetestbeta/conformance-test-harness}"

if [ ! -f "$TESTS/run.sh" ]; then
  echo "solid-conformance-harness: third_party/testing/solid-specification-tests" >&2
  echo "  is not populated. Run tools/ensure-test-env.sh (needs network)." >&2
  exit 2
fi

if ! command -v docker > /dev/null 2>&1; then
  echo "solid-conformance-harness: docker is not on PATH."
  echo "  The Solid specification tests are executed by the Java harness"
  echo "  image $IMAGE and there is no Docker-free route."
  echo "solid-conformance-tests: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi

if ! docker info > /dev/null 2>&1; then
  echo "solid-conformance-harness: docker is installed but its daemon is not"
  echo "  reachable. Start it and rerun."
  echo "solid-conformance-tests: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi

ENV_FILE="${SOLID_HARNESS_ENV:-}"
if [ -z "$ENV_FILE" ] || [ ! -f "$ENV_FILE" ]; then
  echo "solid-conformance-harness: no test-subject environment file."
  echo "  The specification tests authenticate two agents through Solid-OIDC"
  echo "  before their first request, and our server has no token"
  echo "  verification yet. Point SOLID_HARNESS_ENV at a <subject>.env file"
  echo "  holding the credentials (see $TESTS/README.md)."
  echo "solid-conformance-tests: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi

# --------------------------------------------------------------- our server

PORT_FILE="$(mktemp -t solid-harness-port)"
SERVER_LOG="$(mktemp -t solid-harness-log)"
REPORTS="$(mktemp -d -t solid-harness-reports)"
SERVER_PID=""

cleanup() {
  if [ -n "$SERVER_PID" ]; then kill "$SERVER_PID" 2> /dev/null || true; fi
  rm -f "$PORT_FILE" "$SERVER_LOG"
}
trap cleanup EXIT

node npm/factoidal/bin/factoidal.mjs solid-serve "$(mktemp -d)" --port 0 \
  > "$PORT_FILE" 2> "$SERVER_LOG" &
SERVER_PID=$!

ORIGIN=""
for _ in $(seq 1 50); do
  ORIGIN="$(head -n 1 "$PORT_FILE" 2> /dev/null)"
  if [ -n "$ORIGIN" ]; then break; fi
  sleep 0.1
done
if [ -z "$ORIGIN" ]; then
  echo "solid-conformance-harness: our server did not report an origin." >&2
  sed 's/^/  /' "$SERVER_LOG" >&2
  echo "solid-conformance-tests: 0 pass, 0 fail (out of 0) - not run"
  exit 2
fi
echo "solid-conformance-harness: our Solid server is at $ORIGIN"

# ----------------------------------------------------------- the harness

# The container reaches the host's ephemeral port through the Docker
# host gateway; the tests directory and the report directory are mounted.
HOST_ORIGIN="$(printf '%s' "$ORIGIN" | sed 's#127\.0\.0\.1#host.docker.internal#')"

RC=0
docker run --rm \
  --add-host=host.docker.internal:host-gateway \
  -v "$TESTS:/data/tests:ro" \
  -v "$REPORTS:/reports" \
  --env-file "$ENV_FILE" \
  -e "SOLID_IDENTITY_PROVIDER=$HOST_ORIGIN" \
  -e "RESOURCE_SERVER_ROOT=$HOST_ORIGIN" \
  "$IMAGE" \
  --output=/reports --target=factoidal /data/tests || RC=$?

echo "solid-conformance-harness: reports under $REPORTS"
if [ "$RC" -eq 0 ]; then
  echo "solid-conformance-tests: the harness reported no failure"
else
  echo "solid-conformance-tests: the harness exited $RC; read the report under $REPORTS"
  RC=1
fi
exit "$RC"
