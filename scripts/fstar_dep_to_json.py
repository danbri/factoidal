#!/usr/bin/env python3
"""Convert `fstar.exe --dep graph` output into JSON for the D3 SPA viewer.

Input: a .graph file produced by:
    fstar.exe --dep graph $(ls *.fst *.fsti) > deps.graph

The .graph format is Graphviz dot. We parse it for nodes and edges,
classify each module by namespace (top-level dotted prefix), and emit
two JSON shapes:

  modules.json    : full per-module graph
  namespaces.json : aggregated by namespace, with edge weights

Both shapes:
  { "nodes": [{"id": str, "namespace": str, "inProject": bool, "deps": int, "rdeps": int}, ...],
    "links": [{"source": str, "target": str, "weight": int}, ...] }
"""
from __future__ import annotations

import json
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FSTAR_DIR = ROOT / "formal" / "fstar"
OUT_DIR = FSTAR_DIR / "dep-graph"

STDLIB_PREFIXES = (
    "FStar", "Prims", "LowStar", "Steel", "Lib", "Spec", "EverParse", "C", "WasmSupport",
)

NODE_RE = re.compile(r'^\s*"?([A-Z][\w.]*)"?\s*(?:\[[^\]]*\])?\s*;?\s*$')
EDGE_RE = re.compile(r'^\s*"?([A-Z][\w.]*)"?\s*->\s*"?([A-Z][\w.]*)"?\s*(?:\[[^\]]*\])?\s*;?\s*$')


def parse_dot(text: str) -> tuple[set[str], list[tuple[str, str]]]:
    nodes: set[str] = set()
    edges: list[tuple[str, str]] = []
    for line in text.splitlines():
        m = EDGE_RE.match(line)
        if m:
            a, b = m.group(1), m.group(2)
            nodes.add(a)
            nodes.add(b)
            edges.append((a, b))
            continue
        m = NODE_RE.match(line)
        if m:
            nodes.add(m.group(1))
    return nodes, edges


def is_stdlib(mod: str) -> bool:
    return mod.split(".", 1)[0] in STDLIB_PREFIXES


def project_modules() -> set[str]:
    return {p.stem for p in list(FSTAR_DIR.glob("*.fst")) + list(FSTAR_DIR.glob("*.fsti"))}


def ns_of(mod: str) -> str:
    return mod.split(".", 1)[0]


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: fstar_dep_to_json.py <deps.graph>", file=sys.stderr)
        return 2
    src = Path(argv[1]).read_text(encoding="utf-8", errors="replace")
    nodes, edges = parse_dot(src)
    proj = project_modules()

    keep_nodes = {n for n in nodes if n in proj or not is_stdlib(n)}
    keep_edges = [(a, b) for (a, b) in edges if a in proj and b in keep_nodes]

    in_proj_only_edges = [(a, b) for (a, b) in keep_edges if b in proj]

    deg_in: dict[str, int] = defaultdict(int)
    deg_out: dict[str, int] = defaultdict(int)
    for a, b in in_proj_only_edges:
        deg_out[a] += 1
        deg_in[b] += 1

    modules_json = {
        "nodes": sorted(
            (
                {
                    "id": m,
                    "namespace": ns_of(m),
                    "inProject": True,
                    "deps": deg_out.get(m, 0),
                    "rdeps": deg_in.get(m, 0),
                }
                for m in proj
            ),
            key=lambda d: d["id"],
        ),
        "links": [{"source": a, "target": b, "weight": 1} for (a, b) in sorted(set(in_proj_only_edges))],
    }

    ns_edges_w: dict[tuple[str, str], int] = defaultdict(int)
    ns_set: set[str] = set()
    for a, b in in_proj_only_edges:
        na, nb = ns_of(a), ns_of(b)
        ns_set |= {na, nb}
        if na != nb:
            ns_edges_w[(na, nb)] += 1
    ns_module_count = defaultdict(int)
    for m in proj:
        ns_module_count[ns_of(m)] += 1
    namespaces_json = {
        "nodes": sorted(
            (
                {"id": ns, "namespace": ns, "inProject": True,
                 "modules": ns_module_count[ns],
                 "deps": sum(w for (a, _), w in ns_edges_w.items() if a == ns),
                 "rdeps": sum(w for (_, b), w in ns_edges_w.items() if b == ns)}
                for ns in ns_set
            ),
            key=lambda d: d["id"],
        ),
        "links": [
            {"source": a, "target": b, "weight": w}
            for (a, b), w in sorted(ns_edges_w.items())
        ],
    }

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUT_DIR / "modules.json").write_text(json.dumps(modules_json, indent=2) + "\n")
    (OUT_DIR / "namespaces.json").write_text(json.dumps(namespaces_json, indent=2) + "\n")
    print(f"modules.json: {len(modules_json['nodes'])} nodes, {len(modules_json['links'])} links")
    print(f"namespaces.json: {len(namespaces_json['nodes'])} nodes, {len(namespaces_json['links'])} links")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
