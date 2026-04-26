#!/usr/bin/env python3
"""Compare a fresh UK Parliament bench run against the baseline checked
into the repo on the diff base ref.

Used by .github/workflows/ukparliament-bench.yml. Pure tooling; no
semantic logic per CLAUDE.md rules #1, #5, #15.

Soft-mode by default: on regression, prints ::error:: annotations and
exits 0. Set env UKPAR_BENCH_HARD=1 to make regression a build failure.

Inputs:
  --new            path to freshly-written bench JSON
  --baseline-ref   git ref to fetch baseline from (e.g. origin/claude/main)
  --baseline-path  repo-relative path to baseline JSON on that ref
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


def fetch_baseline(ref: str, path: str) -> dict | None:
    """Return the baseline JSON or None if the ref/path doesn't have one."""
    try:
        out = subprocess.run(
            ["git", "show", f"{ref}:{path}"],
            check=False,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError:
        # No git on the runner; should be unreachable on GitHub Actions.
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--new", required=True, help="path to fresh bench JSON")
    ap.add_argument(
        "--baseline-ref",
        default="origin/claude/main",
        help="git ref to read baseline from",
    )
    ap.add_argument(
        "--baseline-path",
        default="docs/test-results/ukparliament-bench-modern.json",
        help="repo-relative path to baseline JSON on the ref",
    )
    args = ap.parse_args(argv)

    new_path = Path(args.new)
    if not new_path.exists():
        print(f"::error::fresh bench JSON not found at {new_path}")
        return 1
    with new_path.open() as f:
        new = json.load(f)

    base = fetch_baseline(args.baseline_ref, args.baseline_path)
    if base is None:
        print(
            f"No baseline found on {args.baseline_ref}:{args.baseline_path}; "
            "seeding clean (no regression check possible)."
        )
        return 0

    ns = new.get("summary", {}) or {}
    bs = base.get("summary", {}) or {}
    new_ok = int(ns.get("ok", 0) or 0)
    base_ok = int(bs.get("ok", 0) or 0)
    new_rgz = int(ns.get("rows_gt_zero", 0) or 0)
    base_rgz = int(bs.get("rows_gt_zero", 0) or 0)

    print(f"OK count:           baseline={base_ok}  new={new_ok}")
    print(f"rows_gt_zero count: baseline={base_rgz} new={new_rgz}")

    # Allow a 1-query slack against transient flakiness; drop of 2+ is
    # treated as a regression.
    regressed = False
    if new_ok < base_ok - 1:
        print(f"::error::OK count regression: {base_ok} -> {new_ok}")
        regressed = True
    if new_rgz < base_rgz - 1:
        print(f"::error::rows_gt_zero regression: {base_rgz} -> {new_rgz}")
        regressed = True

    hard = os.environ.get("UKPAR_BENCH_HARD", "0") == "1"
    if regressed and hard:
        print("UKPAR_BENCH_HARD=1; failing the build.")
        return 1
    if regressed:
        print("Soft-mode: regression detected but not failing build.")
    else:
        print("No regression vs baseline.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
