#!/usr/bin/env bash
#
# tests/stack/manifest_scaling.sh — manifest validation is sub-quadratic.
#
# `ShardManifest.valid` decides "no artifact key plays two roles" over every
# key in the manifest. The specification writes that as
# `keys.length == keys.eraseDups.length`, which is O(n^2); the shipped code
# runs `noDupKeysFast` (sort, then compare adjacent pairs) through `@[csimp]`,
# which is O(n log n). The 25.5 MB / 36,106-entry SKOS manifest of issue 670
# validated in 300 s under the list check and 34 s under the fast one.
#
# This gate builds SBM0 manifests of 10k, 20k and 40k DISTINCT-key entries
# straight from the wire format (the same bytes `gen_cases.py` assembles, so
# no packer and no blocks on disk), times `storeManifestInspect` on each
# through the native `l4wasm-cli`, and checks the growth.
#
#   O(n^2)      predicts t(40k)/t(10k) ~= 16
#   O(n log n)  predicts t(40k)/t(10k) ~= 4.6
#
# The gate FAILS if the ratio reaches MAX_RATIO (default 10), which a
# regression that unwires the `@[csimp]` — dropping `valid` back onto the
# quadratic list check — trips, while the fast path clears it with margin.
# A run that exceeds the per-size timeout is itself a failure: a quadratic
# scan on 40k keys is 1.6e9 String comparisons and does not finish quickly.
#
# Usage:  tests/stack/manifest_scaling.sh
# Env:    STACK_SCALING_SIZES   (default "10000 20000 40000")
#         STACK_SCALING_REPEATS (default 3; the minimum wall time is kept)
#         STACK_SCALING_TIMEOUT (default 120, seconds per run)
#         STACK_SCALING_MAX_RATIO (default 10)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN_DIR="$ROOT/formal/lean4"
CLI="$LEAN_DIR/.lake/build/bin/l4wasm-cli"
FIXTURES="${STACK_SCALING_FIXTURES:-${TMPDIR:-/tmp}/factoidal-manifest-scaling}"

if [ ! -x "$CLI" ]; then
  echo "=== building l4wasm-cli"
  ( cd "$LEAN_DIR" && lake build l4wasm-cli >/dev/null ) || { echo "lake build failed"; exit 2; }
fi
mkdir -p "$FIXTURES"

CLI="$CLI" FIXTURES="$FIXTURES" \
SIZES="${STACK_SCALING_SIZES:-10000 20000 40000}" \
REPEATS="${STACK_SCALING_REPEATS:-3}" \
TIMEOUT="${STACK_SCALING_TIMEOUT:-120}" \
MAX_RATIO="${STACK_SCALING_MAX_RATIO:-10}" \
python3 - <<'PY'
import os, json, struct, hashlib, subprocess, time, sys

CLI      = os.environ["CLI"]
FIXTURES = os.environ["FIXTURES"]
SIZES    = [int(x) for x in os.environ["SIZES"].split()]
REPEATS  = int(os.environ["REPEATS"])
TIMEOUT  = float(os.environ["TIMEOUT"])
MAX_RATIO = float(os.environ["MAX_RATIO"])


def u32(n):
    return struct.pack("<I", n)


def s(text):
    b = text.encode()
    return u32(len(b)) + b


def manifest(n):
    # SBM0 wire format of L4Factoidal/Storage/ShardManifest.lean: magic,
    # u8 version, source identity, term-registry version, layout, then a
    # u32 entry count and that many entries with DISTINCT artifact keys.
    out = bytearray()
    out += b"SBM0"
    out += bytes([0])
    out += s("stack-scaling")
    out += s("terms-v0")
    out += s("predicate-ibk2-v0")
    out += u32(n)
    for i in range(n):
        key = "blocks/p%d.ibk2" % i
        out += s("https://example.test/p%d" % i)
        out += s(key)
        out += u32(4096)
        out += hashlib.sha256(key.encode()).digest()
        out += u32(1)
        out += u32(i)
    return bytes(out)


def args_file(n):
    path = os.path.join(FIXTURES, "manifest-scaling-%d-args.json" % n)
    if not os.path.exists(path):
        with open(path, "w") as fh:
            json.dump([manifest(n).hex()], fh)
    return path


def time_run(args_path):
    # minimum wall time over REPEATS; a timeout or a non-ok envelope is fatal.
    best = None
    for _ in range(REPEATS):
        t0 = time.monotonic()
        try:
            p = subprocess.run([CLI, "call", "storeManifestInspect", args_path],
                               capture_output=True, text=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            print("FAIL: storeManifestInspect exceeded %.0fs on %s"
                  % (TIMEOUT, args_path))
            sys.exit(1)
        dt = time.monotonic() - t0
        if p.returncode != 0 or '"ok":true' not in p.stdout:
            print("FAIL: storeManifestInspect did not answer ok on %s: %s"
                  % (args_path, (p.stdout or p.stderr)[:160]))
            sys.exit(1)
        best = dt if best is None else min(best, dt)
    return best


times = {}
print("=== manifest validation scaling (native, min of %d runs)" % REPEATS)
for n in SIZES:
    t = time_run(args_file(n))
    times[n] = t
    print("  %8d entries  %8.3f s" % (n, t))

base = min(SIZES)
ok = True
for n in SIZES:
    if n == base:
        continue
    size_ratio = n / base
    time_ratio = times[n] / times[base] if times[base] > 0 else float("inf")
    quad = size_ratio ** 2
    verdict = "sub-quadratic" if time_ratio < MAX_RATIO else "QUADRATIC"
    print("  %dx entries: time x%.2f  (linear x%.1f, quadratic x%.1f)  %s"
          % (size_ratio, time_ratio, size_ratio, quad, verdict))
    if n == max(SIZES) and time_ratio >= MAX_RATIO:
        ok = False

if ok:
    print("manifest-scaling: PASS (largest/smallest time ratio below x%.0f)" % MAX_RATIO)
    sys.exit(0)
else:
    print("manifest-scaling: FAIL (time grows quadratically; is the @[csimp] "
          "wiring of noDupKeysFast still in place?)")
    sys.exit(1)
PY
