#!/usr/bin/env python3
"""RDFS / OWL-RL closure (entailment materialisation) benchmark.

Why this exists
---------------
Until 2026-07-31 this repository had NO entailment or closure benchmark
at all: tools/bench-competitive.sh covers SPARQL query latency,
tools/bench-parse-serialize.sh covers parsing and serialization, and
tools/backend_benchmark.py covers storage. Closure had nothing. The
consequence was that an O(n^3) closure went undetected until it pushed
the W3C OWL test WebOnt-description-logic-501 over its refuter budget --
a performance defect discovered through a CONFORMANCE failure. Phase 0
of docs/designissues/2026-07-31-rdfs-performance-scalability.md makes
that the last time.

What it measures
----------------
`factoidal entail --data FILE --regime RDFS|OWL-RL` end-to-end (read +
parse + closure + serialize) against the COMMITTED platform binary --
no F* toolchain required, exactly like tools/bench-parse-serialize.sh.

Two families of input:

  * SYNTHETIC SHAPES, parameterised by n, each stressing a different
    rule interaction (see SHAPES below). Sweeping n gives the scaling
    EXPONENT -- the thing that turns into a wall.
  * REAL VOCABULARIES from third_party/, which give the answer to the
    only question that matters in practice: is the engine usable on
    the schemas people actually publish?

Per case it reports input triples, output triples, expansion ratio,
wall time, CPU time (user+sys of the child process, via os.wait4) and
peak RSS. Wall time and CPU time are reported separately on purpose:
the OWL cap-escape family is budgeted in CPU seconds, not wall clock,
and conflating the two cost a score regression in July 2026.

Discipline (CLAUDE.md anti-patterns)
------------------------------------
  * #17 every single run is capped with a hard deadline; a cap trip is
    RECORDED as a result ("did not complete in N s"), never a hang and
    never a silent omission.
  * #14 no `|| true` -- every exit status is captured and inspected.
  * #25 numerators and denominators are labelled everywhere.
  * This tool MEASURES. It changes no engine code and no suite score.

Usage
-----
  tools/bench-closure.sh                       # measure, print, write JSON
  tools/bench-closure.sh --check               # gate against the baseline
  tools/bench-closure.sh --update-baseline     # freeze a new baseline
  tools/bench-closure.sh --binary /path/to/factoidal   # control experiment
  tools/bench-closure.sh --quick               # small sizes, 1 run each

Outputs
-------
  stdout                                          human-readable tables
  docs/test-results/closure-bench.json            machine-readable, latest run
  docs/test-results/closure-bench.fragment.html   dashboard fragment
  docs/test-results/closure-bench-baseline.json   frozen baseline (--update-baseline)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import shutil
import statistics
import subprocess
import sys
import threading
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

RDFS = "http://www.w3.org/2000/01/rdf-schema#"
RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

# ---------------------------------------------------------------------------
# Synthetic shapes.
#
# Each shape isolates ONE rule interaction, so that when the curve bends
# the bend names its own cause. The RDFS rule numbers are the ones from
# the RDF 1.1 Semantics entailment-rule table.
# ---------------------------------------------------------------------------
SHAPE_SUMMARY = {
    "chain": "linear subClassOf chain + 1 individual (rdfs11 worst case)",
    "tree": "balanced binary class tree, depth log2(n) (rdfs11, small answer)",
    "diamond": "layered DAG, 2 parents per class (duplicate derivations)",
    "wideflat": "n individuals, depth-3 hierarchy (rdfs9 / rdfs4a / rdfs4b)",
    "dense": "n properties with domain/range/subPropertyOf (rdfs2 / rdfs3 / rdfs7)",
}

SHAPE_DOC = {
    "chain": (
        "C0 subClassOf C1 subClassOf ... subClassOf Cn, plus one typed "
        "individual. The rdfs11 (subClassOf transitivity) worst case: the "
        "transitive closure genuinely has n(n-1)/2 edges, so any exponent "
        "above 2 in TIME is work the engine did not need to do."
    ),
    "tree": (
        "Balanced binary class hierarchy, depth log2(n), one typed "
        "individual at the deepest leaf. Same rule as `chain` (rdfs11) but "
        "with an O(n log n) answer instead of O(n^2) -- separates 'the "
        "answer is big' from 'the engine is slow'."
    ),
    "diamond": (
        "Layered DAG, width 4, every class subClassOf two classes in the "
        "next layer up. Every derived edge is re-derived along several "
        "paths, so this is the duplicate-derivation case that semi-naive "
        "evaluation and emit-once both target."
    ),
    "wideflat": (
        "n individuals typed at the bottom of a depth-3 hierarchy. The "
        "rdfs9 (subClassOf + type) and rdfs4a/rdfs4b (everything is an "
        "rdfs:Resource) case: many facts, almost no schema. Should be "
        "linear; if it is not, the constant factors are the problem."
    ),
    "dense": (
        "n properties, each with rdfs:domain, rdfs:range and a "
        "subPropertyOf to a shared super-property, plus one instance "
        "triple each. The rdfs2 (domain), rdfs3 (range) and rdfs7 "
        "(subPropertyOf) case -- broad schema, shallow recursion."
    ),
}


def gen_chain(n: int) -> str:
    lines = [f"@prefix ex: <http://example.org/> .",
             f"@prefix rdfs: <{RDFS}> ."]
    for i in range(n):
        lines.append(f"ex:C{i} rdfs:subClassOf ex:C{i + 1} .")
    lines.append("ex:a a ex:C0 .")
    return "\n".join(lines) + "\n"


def gen_tree(n: int) -> str:
    """Balanced binary tree: class i has parent (i-1)//2. n classes total."""
    lines = [f"@prefix ex: <http://example.org/> .",
             f"@prefix rdfs: <{RDFS}> ."]
    for i in range(1, n):
        lines.append(f"ex:C{i} rdfs:subClassOf ex:C{(i - 1) // 2} .")
    lines.append(f"ex:a a ex:C{n - 1} .")
    return "\n".join(lines) + "\n"


def gen_diamond(n: int, width: int = 4) -> str:
    """Layered DAG, `width` classes per layer, two parents each."""
    layers = max(2, n // width)
    lines = [f"@prefix ex: <http://example.org/> .",
             f"@prefix rdfs: <{RDFS}> ."]
    for k in range(layers - 1):
        for j in range(width):
            lo = k * width + j
            for parent in (j, (j + 1) % width):
                hi = (k + 1) * width + parent
                lines.append(f"ex:C{lo} rdfs:subClassOf ex:C{hi} .")
    lines.append("ex:a a ex:C0 .")
    return "\n".join(lines) + "\n"


def gen_wideflat(n: int) -> str:
    lines = [f"@prefix ex: <http://example.org/> .",
             f"@prefix rdfs: <{RDFS}> .",
             "ex:Leaf rdfs:subClassOf ex:Mid .",
             "ex:Mid rdfs:subClassOf ex:Top ."]
    for i in range(n):
        lines.append(f"ex:i{i} a ex:Leaf .")
    return "\n".join(lines) + "\n"


def gen_dense(n: int) -> str:
    lines = [f"@prefix ex: <http://example.org/> .",
             f"@prefix rdfs: <{RDFS}> ."]
    for i in range(n):
        lines.append(f"ex:p{i} rdfs:domain ex:D{i % 8} .")
        lines.append(f"ex:p{i} rdfs:range ex:R{i % 8} .")
        lines.append(f"ex:p{i} rdfs:subPropertyOf ex:q .")
        lines.append(f"ex:s{i} ex:p{i} ex:o{i} .")
    return "\n".join(lines) + "\n"


GENERATORS = {
    "chain": gen_chain,
    "tree": gen_tree,
    "diamond": gen_diamond,
    "wideflat": gen_wideflat,
    "dense": gen_dense,
}

# n sweeps. Chosen so that the largest n of each shape lands in the
# seconds-to-tens-of-seconds band on the current binary: big enough that
# the exponent is visible above the ~20 ms process floor, small enough
# that a full run is minutes rather than hours.
DEFAULT_SIZES = {
    "chain": [20, 40, 80, 160],
    "tree": [128, 256, 512, 1024],
    "diamond": [32, 64, 128, 192],
    "wideflat": [500, 1000, 2000, 4000],
    "dense": [250, 500, 1000, 2000],
}

QUICK_SIZES = {
    "chain": [20, 40, 80],
    "tree": [128, 256, 512],
    "diamond": [32, 64, 128],
    "wideflat": [500, 1000, 2000],
    "dense": [250, 500, 1000],
}

# ---------------------------------------------------------------------------
# Real vocabularies. Provenance for the fetched ones lives in
# third_party/vocabularies/PROVENANCE.md (URL, retrieval date, SHA-256,
# licence) in the same style as third_party/qudt/PROVENANCE.md.
# ---------------------------------------------------------------------------
VOCABULARIES = [
    ("skos", "third_party/vocabularies/skos.rdf",
     "SKOS Core, W3C Recommendation vocabulary (254 triples)"),
    ("foaf", "third_party/vocabularies/foaf.rdf",
     "FOAF 0.99 specification RDF (635 triples)"),
    ("dcterms", "third_party/vocabularies/dublin_core_terms.ttl",
     "DCMI Metadata Terms (700 triples)"),
    ("schemaorg", "third_party/vocabularies/schemaorg-30.0-current-https.ttl",
     "schema.org 30.0, RDFS/OWL Turtle distribution (17,949 triples)"),
    ("qudt", "third_party/qudt/QUDT-all-in-one-OWL.ttl",
     "QUDT 3.4.0 all-in-one OWL, already vendored (130,404 triples)"),
]


# ---------------------------------------------------------------------------
# Measurement plumbing
# ---------------------------------------------------------------------------
class RunResult:
    __slots__ = ("status", "wall_s", "cpu_s", "peak_rss_kb", "out_lines",
                 "returncode", "stderr_tail")

    def __init__(self, status, wall_s, cpu_s, peak_rss_kb, out_lines,
                 returncode, stderr_tail):
        self.status = status
        self.wall_s = wall_s
        self.cpu_s = cpu_s
        self.peak_rss_kb = peak_rss_kb
        self.out_lines = out_lines
        self.returncode = returncode
        self.stderr_tail = stderr_tail


def run_measured(cmd, cap_seconds: float) -> RunResult:
    """Run `cmd`, counting stdout lines without ever touching disk.

    Returns wall seconds, CPU seconds (ru_utime + ru_stime of exactly
    this child, via os.wait4) and peak RSS. stdout is consumed by a
    reader thread so the pipe cannot fill and deadlock, and only the
    newline count is retained -- a closure of a large vocabulary can be
    hundreds of megabytes and this box is disk-constrained.

    A cap trip kills the whole process group and returns status
    "timeout". That is a RESULT, not an error (anti-pattern #17).
    """
    counter = {"lines": 0}
    stderr_chunks = []

    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )

    def drain_stdout():
        assert proc.stdout is not None
        while True:
            chunk = proc.stdout.read(1 << 20)
            if not chunk:
                break
            counter["lines"] += chunk.count(b"\n")
        proc.stdout.close()

    def drain_stderr():
        assert proc.stderr is not None
        while True:
            chunk = proc.stderr.read(1 << 16)
            if not chunk:
                break
            if len(stderr_chunks) < 16:
                stderr_chunks.append(chunk)
        proc.stderr.close()

    t_out = threading.Thread(target=drain_stdout, daemon=True)
    t_err = threading.Thread(target=drain_stderr, daemon=True)
    t_out.start()
    t_err.start()

    timed_out = {"hit": False}

    def on_cap():
        timed_out["hit"] = True
        try:
            os.killpg(os.getpgid(proc.pid), 9)
        except (ProcessLookupError, PermissionError):
            pass

    timer = threading.Timer(cap_seconds, on_cap)
    timer.start()

    t0 = time.perf_counter()
    _pid, status, ru = os.wait4(proc.pid, 0)
    wall_s = time.perf_counter() - t0
    timer.cancel()
    # Stop Popen from trying to reap an already-reaped pid.
    proc.returncode = os.waitstatus_to_exitcode(status) if not timed_out["hit"] else -9
    t_out.join(timeout=10)
    t_err.join(timeout=10)

    cpu_s = ru.ru_utime + ru.ru_stime
    stderr_tail = b"".join(stderr_chunks).decode("utf-8", "replace")[-2000:]

    if timed_out["hit"]:
        return RunResult("timeout", wall_s, cpu_s, ru.ru_maxrss,
                         counter["lines"], proc.returncode, stderr_tail)
    if proc.returncode != 0:
        return RunResult("error", wall_s, cpu_s, ru.ru_maxrss,
                         counter["lines"], proc.returncode, stderr_tail)
    return RunResult("ok", wall_s, cpu_s, ru.ru_maxrss,
                     counter["lines"], proc.returncode, stderr_tail)


def measure_case(binary: Path, data_path: Path, regime: str, runs: int,
                 cap_seconds: float, label: str) -> dict:
    """Run one closure case `runs` times; return a record dict."""
    cmd = [str(binary), "entail", "--data", str(data_path), "--regime", regime]
    walls, cpus, rsses = [], [], []
    out_lines = None
    for i in range(runs):
        r = run_measured(cmd, cap_seconds)
        if r.status == "timeout":
            print(f"    run {i + 1} of {runs}: DID NOT COMPLETE within "
                  f"{cap_seconds:g}s cap -- recorded as a cap trip")
            return {
                "status": "timeout",
                "cap_seconds": cap_seconds,
                "note": f"did not complete in {cap_seconds:g} s",
            }
        if r.status == "error":
            print(f"    run {i + 1} of {runs}: FAILED rc={r.returncode}")
            return {
                "status": "error",
                "returncode": r.returncode,
                "note": (r.stderr_tail.strip().splitlines() or ["(no stderr)"])[-1],
            }
        if out_lines is None:
            out_lines = r.out_lines
        elif out_lines != r.out_lines:
            return {
                "status": "error",
                "returncode": 0,
                "note": (f"non-deterministic output: run 1 produced {out_lines} "
                         f"lines, run {i + 1} produced {r.out_lines}"),
            }
        walls.append(r.wall_s)
        cpus.append(r.cpu_s)
        rsses.append(r.peak_rss_kb)

    return {
        "status": "ok",
        "output_triples": out_lines,
        "wall_s_median": round(statistics.median(walls), 4),
        "wall_s_min": round(min(walls), 4),
        "wall_s_max": round(max(walls), 4),
        "cpu_s_median": round(statistics.median(cpus), 4),
        "cpu_s_min": round(min(cpus), 4),
        "cpu_s_max": round(max(cpus), 4),
        "peak_rss_kb": max(rsses),
        "runs": runs,
    }


def count_input_triples(binary: Path, data_path: Path, cap_seconds: float) -> int | None:
    """`factoidal count FILE` -> integer, or None if it will not parse."""
    try:
        proc = subprocess.run(
            [str(binary), "count", str(data_path)],
            capture_output=True, timeout=cap_seconds, text=True,
        )
    except subprocess.TimeoutExpired:
        return None
    if proc.returncode != 0:
        return None
    for token in proc.stdout.replace(":", " ").split():
        if token.isdigit():
            return int(token)
    return None


# ---------------------------------------------------------------------------
# Scaling fit
# ---------------------------------------------------------------------------
def loglog_exponent(xs, ys):
    """Least-squares slope of log(y) against log(x) -- the exponent k in
    y ~ x^k. Returns None when there is nothing to fit."""
    pts = [(x, y) for x, y in zip(xs, ys) if x > 0 and y > 0]
    if len(pts) < 2:
        return None
    lx = [math.log(x) for x, _ in pts]
    ly = [math.log(y) for _, y in pts]
    mx = sum(lx) / len(lx)
    my = sum(ly) / len(ly)
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) ** 2 for a in lx)
    if den == 0:
        return None
    return round(num / den, 3)


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------
def fmt_case_row(case) -> str:
    name = case["case"]
    size = case.get("n", "")
    if case["status"] != "ok":
        note = case.get("note", case["status"])
        return (f"{name:<22} {str(size):>7} {'-':>10} {'-':>10} {'-':>8} "
                f"{'-':>9} {'-':>9}   {case['status'].upper()}: {note}")
    inp = case.get("input_triples")
    out = case.get("output_triples")
    ratio = case.get("expansion_ratio")
    return (f"{name:<22} {str(size):>7} "
            f"{(inp if inp is not None else '?'):>10} "
            f"{out:>10} "
            f"{(f'{ratio:.1f}x' if ratio is not None else '?'):>8} "
            f"{case['wall_s_median']:>9.3f} "
            f"{case['cpu_s_median']:>9.3f}")


HEADER = (f"{'case':<22} {'n':>7} {'in-trip':>10} {'out-trip':>10} "
          f"{'expand':>8} {'wall s':>9} {'cpu s':>9}")
RULE = (f"{'-' * 22} {'-' * 7} {'-' * 10} {'-' * 10} "
        f"{'-' * 8} {'-' * 9} {'-' * 9}")


def render_fragment(report: dict) -> str:
    out = []
    ts = report["timestamp"]
    commit = report["commit"]
    out.append(
        f'<h2>RDFS / OWL-RL closure benchmark '
        f'<span class="inline-numbers">measured {ts} &middot; commit '
        f'<a href="https://github.com/danbri/factoidal/commit/{commit}">'
        f'{commit[:7]}</a></span></h2>\n')
    out.append('<p style="margin: 0.3em 0 0.8em; color: var(--muted); '
               'font-size: 0.85em;">\n')
    out.append(
        f'  <code>factoidal entail --regime {report["regime"]}</code> against the '
        f'committed <code>bin/{report["platform"]}/factoidal</code> binary, '
        f'median of {report["runs_per_measurement"]} runs, each run capped at '
        f'{report["cap_seconds_per_run"]:g}s. End-to-end: read + parse + '
        f'closure + serialize. Wall time and CPU time are reported separately '
        f'because the OWL cap-escape family is budgeted in CPU seconds.\n')
    out.append('  Source: <a href="https://github.com/danbri/factoidal/blob/main/'
               'tools/bench-closure.sh">tools/bench-closure.sh</a>, raw data '
               '<a href="closure-bench.json">closure-bench.json</a>.\n')
    out.append('</p>\n')

    for kind, title in (("shape", "Synthetic shapes (scaling)"),
                        ("vocabulary", "Real vocabularies")):
        cases = [c for c in report["cases"] if c["kind"] == kind]
        if not cases:
            continue
        out.append(f'<h3 style="margin-top:1em;">{title}</h3>\n')
        out.append('<div style="overflow-x:auto;">\n')
        out.append('<table style="border-collapse:collapse; width:100%; '
                   'font-size:0.88em;">\n<thead><tr>')
        for h in ("Case", "n", "Input triples", "Output triples",
                  "Expansion", "Wall s (median)", "CPU s (median)"):
            out.append('<th style="text-align:left; border-bottom:1px solid '
                       f'var(--border); padding:0.3em 0.6em;">{h}</th>')
        out.append('</tr></thead>\n<tbody>\n')
        num = 'padding:0.25em 0.6em; text-align:right;'
        for c in cases:
            if c["status"] == "ok":
                ratio = c.get("expansion_ratio")
                ratio_cell = f"{ratio:.1f}x" if ratio is not None else "?"
                out.append(
                    '<tr>'
                    '<td style="padding:0.25em 0.6em; '
                    f'font-family:ui-monospace,monospace;">{c["case"]}</td>'
                    f'<td style="{num}">{c.get("n", "")}</td>'
                    f'<td style="{num}">{c.get("input_triples", "?")}</td>'
                    f'<td style="{num}">{c["output_triples"]}</td>'
                    f'<td style="{num}">{ratio_cell}</td>'
                    f'<td style="{num}">{c["wall_s_median"]:.3f}</td>'
                    f'<td style="{num}">{c["cpu_s_median"]:.3f}</td></tr>\n')
            else:
                note = (c.get("note", c["status"])
                        .replace("&", "&amp;").replace("<", "&lt;")
                        .replace(">", "&gt;"))
                out.append(
                    '<tr style="color:var(--muted);">'
                    f'<td style="padding:0.25em 0.6em; font-family:ui-monospace,'
                    f'monospace;">{c["case"]}</td>'
                    f'<td style="padding:0.25em 0.6em; text-align:right;">'
                    f'{c.get("n", "")}</td>'
                    f'<td colspan="5" style="padding:0.25em 0.6em;">'
                    f'<em>{c["status"]}: {note}</em></td></tr>\n')
        out.append('</tbody></table>\n</div>\n')

    if report.get("scaling"):
        out.append('<p style="margin:0.6em 0; font-size:0.85em; '
                   'color: var(--muted);">Fitted scaling exponents '
                   '(log-log least squares over the n sweep): ')
        bits = []
        for s in report["scaling"]:
            ew = s.get("exponent_wall")
            eo = s.get("exponent_output")
            if ew is None:
                continue
            bits.append(f'<strong>{s["shape"]}</strong> time n<sup>{ew}</sup>, '
                        f'output n<sup>{eo}</sup>')
        out.append("; ".join(bits))
        out.append('.</p>\n')
    return "".join(out)


# ---------------------------------------------------------------------------
# Regression check
# ---------------------------------------------------------------------------
def run_check(report: dict, baseline: dict, tol_pct: float, floor_s: float) -> int:
    """Compare `report` against `baseline`. Returns a process exit code.

    Three independent regression classes, in decreasing severity:

      1. STATUS  -- a case that used to complete now trips the cap or
                    errors. Always a failure, no tolerance.
      2. OUTPUT  -- the closure emits a different number of triples.
                    Zero tolerance: this benchmark is not a correctness
                    suite, but a silent change in derived-triple count is
                    the loudest signal a closure change can send.
      3. TIME    -- CPU seconds, then wall seconds, each allowed
                    tol_pct percent plus an absolute floor_s to keep
                    sub-100ms cases from tripping on scheduler noise.
                    CPU is the primary gate: the OWL cap-escape budget
                    is CPU, and CPU is the quieter of the two signals.
    """
    base_by_key = {(c["kind"], c["case"], c.get("n")): c
                   for c in baseline["cases"]}
    cur_by_key = {(c["kind"], c["case"], c.get("n")): c
                  for c in report["cases"]}

    failures = []
    checked = 0
    missing = []

    for key, base in base_by_key.items():
        cur = cur_by_key.get(key)
        label = f'{base["case"]}' + (f' n={base["n"]}' if base.get("n") else "")
        if cur is None:
            missing.append(label)
            continue
        checked += 1

        if base["status"] == "ok" and cur["status"] != "ok":
            failures.append(
                f'{label}: STATUS regression -- baseline completed, this run '
                f'is "{cur["status"]}" ({cur.get("note", "no note")})')
            continue
        if cur["status"] != "ok":
            continue
        if base["status"] != "ok":
            continue

        if base.get("output_triples") != cur.get("output_triples"):
            failures.append(
                f'{label}: OUTPUT changed -- baseline {base.get("output_triples")} '
                f'triples, this run {cur.get("output_triples")} triples')

        for metric, primary in (("cpu_s_median", True), ("wall_s_median", False)):
            b = base.get(metric)
            c = cur.get(metric)
            if b is None or c is None:
                continue
            budget = b * (1.0 + tol_pct / 100.0) + floor_s
            if c > budget:
                pct = 100.0 * (c / b - 1.0) if b > 0 else float("inf")
                failures.append(
                    f'{label}: {metric} regression -- baseline {b:.3f}s, this run '
                    f'{c:.3f}s (+{pct:.1f}%, budget {budget:.3f}s at '
                    f'{tol_pct:g}% + {floor_s:g}s floor)'
                    + ("  [primary gate]" if primary else ""))

    print()
    print("=== Regression check ===")
    print(f"  baseline: {baseline.get('timestamp', 'unknown')} "
          f"commit {baseline.get('commit', 'unknown')[:7]}")
    print(f"  tolerance: {tol_pct:g}% plus a {floor_s:g}s absolute floor, "
          f"applied to CPU and wall medians independently")
    print(f"  cases compared: {checked} of {len(base_by_key)} baseline cases")
    if missing:
        print(f"  cases in baseline but not in this run ({len(missing)}): "
              f"{', '.join(missing)}")
    print()
    if failures:
        for f in failures:
            print(f"  FAIL  {f}")
        print()
        print(f"closure bench --check: {len(failures)} regression(s) detected "
              f"(out of {checked} cases compared). FAIL")
        return 1
    print(f"closure bench --check: 0 regressions detected "
          f"(out of {checked} cases compared). PASS")
    return 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(
        description="RDFS / OWL-RL closure benchmark (Phase 0 of "
                    "docs/designissues/2026-07-31-rdfs-performance-scalability.md)")
    ap.add_argument("--binary", default=None,
                    help="factoidal binary to measure "
                         "(default: bin/<platform>/factoidal)")
    ap.add_argument("--regime", default="RDFS", choices=["RDFS", "OWL-RL"])
    ap.add_argument("--runs", type=int, default=3,
                    help="runs per measurement; the median is reported "
                         "(default 3)")
    ap.add_argument("--cap-seconds", type=float, default=120.0,
                    help="hard cap per single run; a trip is recorded as a "
                         "result (default 120)")
    ap.add_argument("--vocab-cap-seconds", type=float, default=None,
                    help="separate cap for real vocabularies "
                         "(default: same as --cap-seconds)")
    ap.add_argument("--only", choices=["shapes", "vocabularies"], default=None,
                    help="restrict to one family")
    ap.add_argument("--shapes", default=None,
                    help="comma-separated subset of "
                         + ",".join(GENERATORS))
    ap.add_argument("--quick", action="store_true",
                    help="smaller n sweep and 1 run per measurement")
    ap.add_argument("--check", action="store_true",
                    help="compare against the committed baseline and exit "
                         "non-zero on regression")
    ap.add_argument("--update-baseline", action="store_true",
                    help="write this run to the committed baseline file")
    ap.add_argument("--tolerance-pct", type=float, default=20.0,
                    help="regression tolerance in percent for --check "
                         "(default 20; see the baseline JSON for the "
                         "measured run-to-run variance it was chosen from)")
    ap.add_argument("--floor-seconds", type=float, default=0.05,
                    help="absolute slack added to the tolerance so that "
                         "sub-100ms cases do not trip on scheduler noise "
                         "(default 0.05)")
    ap.add_argument("--json-out", default=None,
                    help="override the machine-readable output path")
    ap.add_argument("--no-fragment", action="store_true",
                    help="do not write the dashboard HTML fragment")
    args = ap.parse_args()

    machine = platform.machine()
    system = platform.system()
    plat = {("Linux", "x86_64"): "linux-x86_64",
            ("Darwin", "arm64"): "darwin-arm64"}.get((system, machine))
    if plat is None:
        print(f"Unsupported platform {system}-{machine}; this bench targets the "
              f"committed bin/linux-x86_64 (or darwin-arm64) binaries.",
              file=sys.stderr)
        return 2

    binary = Path(args.binary) if args.binary else REPO_ROOT / "bin" / plat / "factoidal"
    if not binary.is_file() or not os.access(binary, os.X_OK):
        print(f"::error::factoidal binary missing or not executable: {binary}",
              file=sys.stderr)
        return 2

    runs = 1 if args.quick else args.runs
    sizes = QUICK_SIZES if args.quick else DEFAULT_SIZES
    vocab_cap = args.vocab_cap_seconds if args.vocab_cap_seconds is not None \
        else args.cap_seconds

    shape_names = list(GENERATORS)
    if args.shapes:
        shape_names = [s.strip() for s in args.shapes.split(",") if s.strip()]
        for s in shape_names:
            if s not in GENERATORS:
                print(f"Unknown shape: {s}", file=sys.stderr)
                return 2

    binary_sha = hashlib.sha256(binary.read_bytes()).hexdigest()
    commit = subprocess.run(["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"],
                            capture_output=True, text=True).stdout.strip() or "unknown"
    timestamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

    fixture_dir = Path(os.environ.get("TMPDIR", "/tmp")) / "factoidal-bench-closure"
    fixture_dir.mkdir(parents=True, exist_ok=True)

    print("Factoidal RDFS / OWL-RL closure benchmark")
    print(f"  binary:   {binary}")
    print(f"  sha256:   {binary_sha[:16]}...")
    print(f"  commit:   {commit}")
    print(f"  regime:   {args.regime}")
    print(f"  runs per measurement: {runs}   cap per run: "
          f"{args.cap_seconds:g}s (vocabularies: {vocab_cap:g}s)")
    print()

    cases = []

    # --- synthetic shapes --------------------------------------------------
    if args.only != "vocabularies":
        print("=== Synthetic shapes ===")
        for shape in shape_names:
            print(f"  {shape}: {SHAPE_SUMMARY[shape]}")
            for n in sizes[shape]:
                path = fixture_dir / f"{shape}-{n}.ttl"
                path.write_text(GENERATORS[shape](n), encoding="utf-8")
                inp = count_input_triples(binary, path, args.cap_seconds)
                rec = measure_case(binary, path, args.regime, runs,
                                   args.cap_seconds, f"{shape} n={n}")
                rec["kind"] = "shape"
                rec["case"] = shape
                rec["n"] = n
                rec["input_triples"] = inp
                if rec["status"] == "ok" and inp:
                    rec["expansion_ratio"] = round(rec["output_triples"] / inp, 3)
                cases.append(rec)
                if rec["status"] == "ok":
                    print(f"    n={n:<6} in {inp} triples -> out "
                          f"{rec['output_triples']} triples, "
                          f"wall {rec['wall_s_median']:.3f}s, "
                          f"cpu {rec['cpu_s_median']:.3f}s")
                path.unlink(missing_ok=True)
        print()

    # --- real vocabularies -------------------------------------------------
    if args.only != "shapes":
        print("=== Real vocabularies ===")
        for key, rel, desc in VOCABULARIES:
            path = REPO_ROOT / rel
            if not path.is_file():
                cases.append({
                    "kind": "vocabulary", "case": key, "status": "absent",
                    "path": rel, "description": desc,
                    "note": f"{rel} not present in this checkout",
                })
                print(f"  {key}: ABSENT ({rel})")
                continue
            inp = count_input_triples(binary, path, vocab_cap)
            rec = measure_case(binary, path, args.regime, runs, vocab_cap, key)
            rec["kind"] = "vocabulary"
            rec["case"] = key
            rec["path"] = rel
            rec["description"] = desc
            rec["input_triples"] = inp
            if rec["status"] == "ok" and inp:
                rec["expansion_ratio"] = round(rec["output_triples"] / inp, 3)
            cases.append(rec)
            if rec["status"] == "ok":
                print(f"  {key}: in {inp} triples -> out "
                      f"{rec['output_triples']} triples "
                      f"({rec['expansion_ratio']:.1f}x), "
                      f"wall {rec['wall_s_median']:.3f}s, "
                      f"cpu {rec['cpu_s_median']:.3f}s")
            elif rec["status"] == "timeout":
                print(f"  {key}: in {inp} triples -> DID NOT COMPLETE in "
                      f"{vocab_cap:g}s")
        print()

    # --- scaling fit -------------------------------------------------------
    scaling = []
    for shape in shape_names:
        pts = [c for c in cases
               if c["kind"] == "shape" and c["case"] == shape
               and c["status"] == "ok"]
        if len(pts) < 2:
            continue
        ns = [c["n"] for c in pts]
        scaling.append({
            "shape": shape,
            "n_from": min(ns),
            "n_to": max(ns),
            "exponent_wall": loglog_exponent(ns, [c["wall_s_median"] for c in pts]),
            "exponent_cpu": loglog_exponent(ns, [c["cpu_s_median"] for c in pts]),
            "exponent_output": loglog_exponent(ns, [c["output_triples"] for c in pts]),
            "fit": "log-log least squares of the median over the n sweep",
        })

    # --- run-to-run variance ----------------------------------------------
    wall_cvs, cpu_cvs = [], []
    for c in cases:
        if c["status"] != "ok" or c.get("runs", 1) < 2:
            continue
        # min/max/median are all we retain; use the spread as a proxy for CV.
        span_w = (c["wall_s_max"] - c["wall_s_min"]) / c["wall_s_median"] * 100 \
            if c["wall_s_median"] > 0 else None
        span_c = (c["cpu_s_max"] - c["cpu_s_min"]) / c["cpu_s_median"] * 100 \
            if c["cpu_s_median"] > 0 else None
        if span_w is not None:
            wall_cvs.append(span_w)
        if span_c is not None:
            cpu_cvs.append(span_c)
    variance = {
        "metric": "per-case (max - min) / median, as a percentage, over the "
                  "runs of this invocation",
        "wall_spread_pct_max": round(max(wall_cvs), 2) if wall_cvs else None,
        "wall_spread_pct_median": round(statistics.median(wall_cvs), 2) if wall_cvs else None,
        "cpu_spread_pct_max": round(max(cpu_cvs), 2) if cpu_cvs else None,
        "cpu_spread_pct_median": round(statistics.median(cpu_cvs), 2) if cpu_cvs else None,
        "cases_with_multiple_runs": len(wall_cvs),
    }

    report = {
        "schema": "factoidal-closure-bench/1",
        "timestamp": timestamp,
        "commit": commit,
        "platform": plat,
        "binary": str(binary),
        "binary_sha256": binary_sha,
        "regime": args.regime,
        "runs_per_measurement": runs,
        "cap_seconds_per_run": args.cap_seconds,
        "vocab_cap_seconds_per_run": vocab_cap,
        "note": ("End-to-end: read + parse + closure + serialize. There is no "
                 "closure-only entry point in the committed CLI, so parse cost "
                 "is included; tools/bench-parse-serialize.sh measures the "
                 "parse component separately. Wall and CPU are reported "
                 "separately because the OWL cap-escape family is budgeted in "
                 "CPU seconds."),
        "shape_summary": SHAPE_SUMMARY,
        "shape_documentation": SHAPE_DOC,
        "cases": cases,
        "scaling": scaling,
        "variance": variance,
    }

    # --- human table -------------------------------------------------------
    print("=== Summary ===")
    print(HEADER)
    print(RULE)
    for c in cases:
        print(fmt_case_row(c))
    print()
    if scaling:
        print("=== Fitted scaling exponents (log-log least squares) ===")
        print(f"{'shape':<12} {'n range':>12} {'time ~ n^k':>12} "
              f"{'cpu ~ n^k':>12} {'output ~ n^k':>14}")
        print(f"{'-' * 12} {'-' * 12} {'-' * 12} {'-' * 12} {'-' * 14}")
        for s in scaling:
            n_range = "%d-%d" % (s["n_from"], s["n_to"])
            print(f"{s['shape']:<12} {n_range:>12} "
                  f"{str(s['exponent_wall']):>12} {str(s['exponent_cpu']):>12} "
                  f"{str(s['exponent_output']):>14}")
        print()
    print("=== Run-to-run spread ((max-min)/median, this invocation) ===")
    if variance["cases_with_multiple_runs"] == 0:
        # Every case ran once (--quick), so there is no spread to report.
        # Say that, rather than print "None%" -- an unmeasured quantity must
        # not look like a measured one (skills/measuring-inference).
        print("  not measured: every case ran once "
              "(--runs 1); re-run without --quick for a spread figure")
    else:
        print(f"  wall: median {variance['wall_spread_pct_median']}%, "
              f"max {variance['wall_spread_pct_max']}%  "
              f"(over {variance['cases_with_multiple_runs']} cases with >1 run)")
        print(f"  cpu:  median {variance['cpu_spread_pct_median']}%, "
              f"max {variance['cpu_spread_pct_max']}%")
    print()

    # --- write artifacts ---------------------------------------------------
    out_dir = REPO_ROOT / "docs" / "test-results"
    out_dir.mkdir(parents=True, exist_ok=True)
    json_out = Path(args.json_out) if args.json_out else out_dir / "closure-bench.json"
    json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"JSON written: {json_out}")

    if not args.no_fragment:
        frag = out_dir / "closure-bench.fragment.html"
        frag.write_text(render_fragment(report), encoding="utf-8")
        print(f"Fragment written: {frag}")

    baseline_path = out_dir / "closure-bench-baseline.json"
    if args.update_baseline:
        baseline_path.write_text(json.dumps(report, indent=2) + "\n",
                                 encoding="utf-8")
        print(f"Baseline written: {baseline_path}")

    if args.check:
        if not baseline_path.is_file():
            print(f"::error::--check requested but no baseline at "
                  f"{baseline_path}. Run with --update-baseline first.",
                  file=sys.stderr)
            return 2
        baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
        return run_check(report, baseline, args.tolerance_pct,
                         args.floor_seconds)

    return 0


if __name__ == "__main__":
    sys.exit(main())
