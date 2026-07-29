#!/usr/bin/env python3
"""
RDF parser differential harness (issue #317, gate 4).

For each generated instance:
  - "graph" profile   -> rendered in N-Triples, Turtle, RDF/XML
  - "dataset" profile -> rendered in N-Quads, TriG

For every rendering we get TWO independent canonical forms:
  - factoidal's own RDFC-1.0 canonicalizer (`factoidal canonicalize FILE`)
  - pyoxigraph's RDFC-1.0 canonicalizer (Rust, Oxigraph project) applied to
    the SAME source bytes

and compare them via compare.diff_canonical (set-of-canonical-lines, never
raw string equality on the un-canonicalized input). We also cross-check
factoidal's own canonical output is IDENTICAL across all renderings of the
same abstract graph (cross-format self-consistency).

Usage:
  python3 rdf_diff.py --n 200 --seed-base 1000 --out .claude-runs/difftest
"""
from __future__ import annotations

import argparse
import json
import os
import random
import subprocess
import sys
import time

import rdfgen
import compare

FACTOIDAL_BIN = os.environ.get(
    "FACTOIDAL_BIN",
    os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "bin", "linux-x86_64", "factoidal"),
)

try:
    import pyoxigraph as ox
except ImportError:
    ox = None

RDF_FORMAT_MAP = {
    "nt": "N_TRIPLES",
    "ttl": "TURTLE",
    "rdf": "RDF_XML",
    "nq": "N_QUADS",
    "trig": "TRIG",
}


def factoidal_canonicalize(path: str, timeout: int = 20):
    # NOTE: this container's locale is POSIX/C (LANG unset), so
    # subprocess.run(text=True) without an explicit encoding decodes via
    # locale.getpreferredencoding() -- NOT UTF-8 -- and silently mangles
    # every multi-byte character in Factoidal's (correct) UTF-8 stdout.
    # Pass encoding="utf-8" explicitly. (First differential run here
    # mistook this harness bug for ~10 Factoidal "disagreements" --
    # verified false-positive by re-decoding the raw bytes; see ledger.)
    try:
        r = subprocess.run(
            [FACTOIDAL_BIN, "canonicalize", path],
            capture_output=True, text=True, encoding="utf-8", timeout=timeout,
        )
        return r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "TIMEOUT"


def factoidal_count(path: str, timeout: int = 20):
    try:
        r = subprocess.run(
            [FACTOIDAL_BIN, "count", path],
            capture_output=True, text=True, encoding="utf-8", timeout=timeout,
        )
        return r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "TIMEOUT"


def pyoxigraph_canonicalize(path: str, fmt_name: str):
    if ox is None:
        return None, "pyoxigraph not installed"
    fmt = getattr(ox.RdfFormat, fmt_name)
    try:
        d = ox.Dataset(ox.parse(path=path, format=fmt))
    except Exception as e:  # noqa: BLE001 -- reference impl parse errors are data, not our bug
        return None, f"pyoxigraph parse error: {e}"
    try:
        d.canonicalize(ox.CanonicalizationAlgorithm.RDFC_1_0)
    except Exception as e:  # noqa: BLE001
        return None, f"pyoxigraph canonicalize error: {e}"
    lines = []
    for q in d:
        if str(q.graph_name) == "<defaultGraph>" or isinstance(q.graph_name, ox.DefaultGraph):
            lines.append(f"{q.subject} {q.predicate} {q.object} .")
        else:
            lines.append(f"{q.subject} {q.predicate} {q.object} {q.graph_name} .")
    return "\n".join(lines), None


def run_one(seed: int, size: str, out_dir: str, findings: list, self_check_findings: list, soundness_findings: list):
    profile = "dataset" if seed % 3 == 0 else "graph"
    doc = rdfgen.generate_graph(seed=seed, profile=profile, size=size)
    rng = random.Random(seed * 7919 + 1)

    targets = rdfgen.SERIALIZERS_GRAPH if profile == "graph" else rdfgen.SERIALIZERS_DATASET
    inst_dir = os.path.join(out_dir, f"seed{seed}_{profile}_{size}")
    os.makedirs(inst_dir, exist_ok=True)

    factoidal_canonicals = {}
    per_format_result = {}

    for ext, serializer in targets.items():
        text = serializer(doc, rng)
        path = os.path.join(inst_dir, f"instance.{ext}")
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)

        rc, out, err = factoidal_canonicalize(path)
        ref_out, ref_err = pyoxigraph_canonicalize(path, RDF_FORMAT_MAP[ext])

        entry = {
            "seed": seed, "profile": profile, "size": size, "format": ext, "path": path,
            "factoidal_rc": rc, "factoidal_err": err.strip() if err else None,
            "reference": "pyoxigraph",
            "reference_err": ref_err,
        }

        if rc != 0 or err.strip():
            _, cnt_out, cnt_err = factoidal_count(path)
            entry["disposition"] = "runtime-error"
            entry["detail"] = f"factoidal canonicalize failed rc={rc} err={err!r} count_probe={cnt_out!r}/{cnt_err!r}"
            findings.append(entry)
            per_format_result[ext] = None
            continue

        factoidal_canonicals[ext] = out
        per_format_result[ext] = out

        if ref_out is None:
            # reference implementation itself rejected/errored -- log but
            # don't call it a Factoidal bug; could be a reference-side
            # limitation or (rarely) a genuinely invalid fuzz input.
            entry["disposition"] = "reference-error"
            entry["detail"] = ref_err
            findings.append(entry)
            continue

        agree, only_us, only_ref = compare.diff_canonical(out, ref_out)
        if not agree:
            entry["only_factoidal"] = only_us[:20]
            entry["only_reference"] = only_ref[:20]
            if compare.is_only_langtag_case_difference(only_us, only_ref):
                # Known, spec-acknowledged ambiguity (RDFC-1.0 sec on hash
                # instability from language-tag casing; RDF 1.2 Concepts
                # 3.4.1 permits either normalizing or preserving case) --
                # see docs/designissues/2026-07-29-differential-testing-ledger.md.
                # Still logged, never silently dropped, per the issue brief.
                entry["disposition"] = "spec-ambiguous-langtag-case"
                findings.append(entry)
                continue
            if compare.isomorphic_after_langtag_fold(out, ref_out):
                # The line-set diff can look like a sea of unrelated
                # disagreements even though the ONLY root cause is the
                # same known langtag-case ambiguity: RDFC-1.0's Hash
                # N-Degree Quads step feeds a literal's exact bytes into
                # its neighboring blank nodes' hashes, so one differently
                # -cased tag cascades into different canonical labels for
                # every blank node in its connected neighborhood. Confirmed
                # via a THIRD independent implementation (rdflib) doing a
                # real graph-isomorphism check after folding case on both
                # sides -- not just a same-line-count heuristic.
                entry["disposition"] = "spec-ambiguous-langtag-case-cascaded"
                findings.append(entry)
                continue
            entry["disposition"] = "disagreement"
            # Soundness flag per the task's own wording: "we produce a
            # triple no other implementation produces, OR drop one they
            # all produce." That is NOT only the one-sided cases (pure
            # extra / pure missing) -- a same-COUNT "swap" (we emit a
            # DIFFERENT, e.g. corrupted, triple in place of the correct
            # one) is triples-nobody-else-produces too, just with a
            # same-size only_ref alongside it. Catch both shapes.
            # (This fix landed AFTER the 2026-07-29 baseline run quoted in
            # the ledger; that run's soundness_suspects undercounts swap
            # cases -- e.g. the Turtle/TriG IRIREF mojibake bug, Finding 2,
            # which IS soundness-relevant and was still caught and reported
            # via manual inspection, just not by this counter at the time.)
            if only_us:
                if not only_ref:
                    entry["soundness_suspect"] = "factoidal produced quads pyoxigraph does not (extra output)"
                else:
                    entry["soundness_suspect"] = "factoidal produced DIFFERENT quads than pyoxigraph for the same input (swap, not pure add/drop)"
                soundness_findings.append(entry)
            elif only_ref:
                entry["soundness_suspect"] = "factoidal DROPPED quads pyoxigraph produces (missing output)"
                soundness_findings.append(entry)
            findings.append(entry)

    # cross-format self-consistency: all renderings of the SAME abstract
    # graph must canonicalize identically under factoidal itself.
    good = {k: v for k, v in factoidal_canonicals.items()}
    if len(good) >= 2:
        base_ext, base_text = next(iter(good.items()))
        base_lines = compare.normalize_canonical_lines(base_text)
        for ext, text in good.items():
            if ext == base_ext:
                continue
            lines = compare.normalize_canonical_lines(text)
            if lines != base_lines:
                self_check_findings.append({
                    "seed": seed, "profile": profile, "size": size,
                    "disposition": "self-inconsistency",
                    "detail": f"{base_ext} canonical form != {ext} canonical form for the SAME abstract graph",
                    "base_format": base_ext, "other_format": ext,
                })


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=100)
    ap.add_argument("--seed-base", type=int, default=1000)
    ap.add_argument("--out", default=".claude-runs/difftest/rdf-corpus")
    ap.add_argument("--sizes", default="small,medium,large")
    args = ap.parse_args()

    if ox is None:
        print("FATAL: pyoxigraph not importable -- cannot run RDF differential harness", file=sys.stderr)
        sys.exit(2)

    sizes = args.sizes.split(",")
    findings = []
    self_check_findings = []
    soundness_findings = []

    t0 = time.time()
    for i in range(args.n):
        seed = args.seed_base + i
        size = sizes[i % len(sizes)]
        run_one(seed, size, args.out, findings, self_check_findings, soundness_findings)
    elapsed = time.time() - t0

    report = {
        "harness": "rdf_diff",
        "n_instances": args.n,
        "elapsed_sec": round(elapsed, 1),
        "reference_implementation": f"pyoxigraph {ox.__name__}",
        "disagreements": findings,
        "self_inconsistencies": self_check_findings,
        "soundness_suspects": soundness_findings,
    }
    os.makedirs(args.out, exist_ok=True)
    report_path = os.path.join(args.out, "report.json")
    with open(report_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    from collections import Counter
    by_disp = Counter(f.get("disposition", "?") for f in findings)
    print(f"instances={args.n} elapsed={elapsed:.1f}s")
    print(f"findings by disposition: {dict(by_disp)}")
    print(f"self_inconsistencies={len(self_check_findings)} soundness_suspects={len(soundness_findings)}")
    print(f"report: {report_path}")
    if soundness_findings:
        print("!!! SOUNDNESS-SUSPICIOUS FINDINGS -- see report.json soundness_suspects !!!", file=sys.stderr)


if __name__ == "__main__":
    main()
