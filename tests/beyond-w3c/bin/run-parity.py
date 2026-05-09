#!/usr/bin/env python3
"""tests/beyond-w3c/bin/run-parity.py — Phase 2 orchestrator.

Walks a fixture manifest (tests/beyond-w3c/fixtures/<page>.json) and
invokes each runner under tests/beyond-w3c/runners/. Emits a per-(query,
runtime) pass/fail/skip grid as JSON.

This is a SCAFFOLD: enough plumbing to read manifests, dispatch to
runners, and emit a result document. Real result-comparison logic
(row-set normalisation, parity assertion, dashboard JSON shape) lands
with phases #243-#246.

Usage:
    run-parity.py --manifest tests/beyond-w3c/fixtures/index.json \\
                  --runners native,js-node[,wasm-node] \\
                  --output docs/test-results/beyond-w3c/latest.json

Exit code:
    0 — every non-allowlisted query passed on every runner
    1 — at least one non-allowlisted failure
    2 — orchestrator error (manifest missing, runner missing, etc.)
"""

from __future__ import annotations

import argparse
import json
import os
import shlex
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
RUNNERS = {
    "native":    REPO_ROOT / "tests/beyond-w3c/runners/run-native.sh",
    "js-node":   REPO_ROOT / "tests/beyond-w3c/runners/run-js-node.sh",
    "wasm-node": REPO_ROOT / "tests/beyond-w3c/runners/run-wasm-node.sh",
}


def load_manifest(path: Path) -> dict:
    with path.open() as fh:
        return json.load(fh)


def resolve_dataset_args(manifest: dict, dataset_name: str) -> list[str]:
    for ds in manifest.get("datasets", []):
        if ds["name"] == dataset_name:
            spec = f"{ds['file']}:{ds['format']}"
            if "graph" in ds:
                spec += f":{ds['graph']}"
            return ["--data", spec]
    raise SystemExit(f"manifest references unknown dataset: {dataset_name}")


def run_one(runner: Path, query_path: Path, dataset_args: list[str]) -> dict:
    cmd = [str(runner), "--query", str(query_path), *dataset_args]
    started = time.monotonic()
    proc = subprocess.run(cmd, capture_output=True, text=True)
    elapsed = (time.monotonic() - started) * 1000
    return {
        "rc": proc.returncode,
        "ms": round(elapsed, 1),
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def classify(query: dict, runner: str, run_result: dict) -> str:
    """Return one of: pass | fail | known-fail | skip | engine-crash."""
    rc = run_result["rc"]
    if rc == 77:
        return "skip"
    if rc != 0:
        kf = (query.get("known_failures") or {}).get(runner)
        return "known-fail" if kf else "engine-crash"
    # Phase 2a (#243) lands the row-set / row-count comparison logic
    # here. For now, the scaffold just reports the runner exited 0.
    return "pass"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", required=True, type=Path)
    ap.add_argument("--runners", default="native",
                    help="comma-separated subset of: native,js-node,wasm-node")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()

    args.manifest = args.manifest.resolve()
    if not args.manifest.exists():
        print(f"missing manifest: {args.manifest}", file=sys.stderr)
        return 2

    manifest = load_manifest(args.manifest)
    runners = [r.strip() for r in args.runners.split(",") if r.strip()]
    for r in runners:
        if r not in RUNNERS:
            print(f"unknown runner: {r}", file=sys.stderr)
            return 2

    grid: list[dict] = []
    any_actionable_fail = False

    for query in manifest["queries"]:
        dataset_args = resolve_dataset_args(manifest, query["dataset"])
        query_path = REPO_ROOT / query["file"]
        for runner in runners:
            result = run_one(RUNNERS[runner], query_path, dataset_args)
            status = classify(query, runner, result)
            cell = {
                "query": query["name"],
                "runner": runner,
                "status": status,
                "ms": result["ms"],
                "rc": result["rc"],
            }
            kf = (query.get("known_failures") or {}).get(runner)
            if kf:
                cell["known_failure_issue"] = kf.get("issue")
            grid.append(cell)
            if status in ("fail", "engine-crash"):
                any_actionable_fail = True
            print(f"{runner:>10}  {query['name']:<20}  {status}  ({result['ms']:.0f} ms)")

    summary = {
        "manifest": str(args.manifest.relative_to(REPO_ROOT)),
        "runners": runners,
        "grid": grid,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("w") as fh:
            json.dump(summary, fh, indent=2)

    return 1 if any_actionable_fail else 0


if __name__ == "__main__":
    sys.exit(main())
