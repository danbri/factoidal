#!/usr/bin/env python3
"""Run a single subprocess, measuring wall time and peak RSS of its
process tree via getrusage(RUSAGE_CHILDREN).

Used by tools/bench-competitive.py (and reusable by any other bench
script) as a stand-in for `/usr/bin/time -v`, which is not installed in
this sandbox (see docs/designissues/2026-07-05-disk-backed-db-perf-review.md
Author-context note). Each invocation is a fresh Python process, so
RUSAGE_CHILDREN is scoped to exactly the one child command it runs --
no cross-measurement leakage.

Usage:
  bench_rusage_run.py <stdout_file> <stderr_file> <cmd...>

Prints one JSON object to its OWN stdout (not the child's):
  {"wall_s": <float>, "peak_rss_kb": <int>, "peak_rss_bytes": <int>,
   "rss_raw_unit": <string>, "returncode": <int>}

`ru_maxrss` is KiB on Linux but bytes on macOS. The normalized output preserves
both KiB and bytes, and records the platform-native unit so benchmark results
do not silently mislabel macOS measurements.
"""
import json
import platform
import resource
import subprocess
import sys
import time


def main() -> int:
    if len(sys.argv) < 4:
        print("usage: bench_rusage_run.py STDOUT STDERR CMD...", file=sys.stderr)
        return 2
    stdout_path, stderr_path = sys.argv[1], sys.argv[2]
    cmd = sys.argv[3:]

    t0 = time.perf_counter()
    with open(stdout_path, "wb") as out, open(stderr_path, "wb") as err:
        proc = subprocess.run(cmd, stdout=out, stderr=err)
    wall_s = time.perf_counter() - t0

    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    raw_rss = ru.ru_maxrss
    if platform.system() == "Darwin":
        peak_rss_bytes = raw_rss
        peak_rss_kb = raw_rss // 1024
        raw_unit = "bytes"
    else:
        peak_rss_kb = raw_rss
        peak_rss_bytes = raw_rss * 1024
        raw_unit = "kilobytes"
    print(json.dumps({
        "wall_s": wall_s,
        "peak_rss_kb": peak_rss_kb,
        "peak_rss_bytes": peak_rss_bytes,
        "rss_raw_unit": raw_unit,
        "returncode": proc.returncode,
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
