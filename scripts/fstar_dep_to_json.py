#!/usr/bin/env python3
"""Convert `fstar.exe --dep graph` output into all the artefacts the
dep-graph viewer expects.

Input: a .graph file produced by:
    cd formal/fstar
    eval $(opam env --switch=fstar)
    fstar.exe --dep graph $(ls *.fst *.fsti)
    # writes ./dep.graph

Output (under formal/fstar/dep-graph/):
  modules.json, namespaces.json   - data for the D3 SPA (index.html)
  modules.dot, namespaces.dot     - Graphviz, in-project only
  modules.svg/png, namespaces.*   - rendered (if `dot` on PATH)
  modules.mmd, namespaces.mmd     - Mermaid
  modules.txt                     - plain-text adjacency list
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FSTAR_DIR = ROOT / "formal" / "fstar"
OUT_DIR = ROOT / "docs" / "web" / "demos" / "dep-graph"

STDLIB_PREFIXES = (
    "FStar", "Prims", "LowStar", "Steel", "Lib", "Spec", "EverParse",
    "C", "WasmSupport",
)

NODE_RE = re.compile(r'^\s*"([A-Za-z][\w.]*?)(?:\.fst[i]?)?"\s*(?:\[[^\]]*\])?\s*;?\s*$')
EDGE_RE = re.compile(
    r'^\s*"([A-Za-z][\w.]*?)(?:\.fst[i]?)?"\s*->\s*'
    r'"([A-Za-z][\w.]*?)(?:\.fst[i]?)?"\s*(?:\[[^\]]*\])?\s*;?\s*$'
)

NS_COLOR = {
    "Parser":   "#cfe8ff",
    "RDF":      "#d4f4dd",
    "SPARQL":   "#ffe6b3",
    "SPARQL11": "#ffd699",
    "OWL":      "#e6ccff",
    "RIF":      "#ffd1dc",
    "SHACL":    "#fff5b3",
    "Util":     "#eeeeee",
    "Tableau":  "#f5cba7",
    "Parquet":  "#c8d6e5",
}


def parse_dot(text: str) -> tuple[set[str], list[tuple[str, str]]]:
    nodes: set[str] = set()
    edges: list[tuple[str, str]] = []
    for line in text.splitlines():
        m = EDGE_RE.match(line)
        if m:
            a, b = m.group(1), m.group(2)
            if a == b:
                continue
            nodes.add(a); nodes.add(b)
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


def write_json(in_proj_edges, proj):
    deg_in: dict[str, int] = defaultdict(int)
    deg_out: dict[str, int] = defaultdict(int)
    for a, b in in_proj_edges:
        deg_out[a] += 1
        deg_in[b] += 1

    modules_json = {
        "nodes": sorted(
            ({"id": m, "namespace": ns_of(m), "inProject": True,
              "deps": deg_out.get(m, 0), "rdeps": deg_in.get(m, 0)} for m in proj),
            key=lambda d: d["id"]),
        "links": [{"source": a, "target": b, "weight": 1}
                  for (a, b) in sorted(set(in_proj_edges))],
    }

    ns_edges_w: dict[tuple[str, str], int] = defaultdict(int)
    ns_module_count: dict[str, int] = defaultdict(int)
    for m in proj:
        ns_module_count[ns_of(m)] += 1
    ns_set: set[str] = set(ns_module_count)
    for a, b in in_proj_edges:
        na, nb = ns_of(a), ns_of(b)
        ns_set |= {na, nb}
        if na != nb:
            ns_edges_w[(na, nb)] += 1
    namespaces_json = {
        "nodes": sorted(
            ({"id": ns, "namespace": ns, "inProject": True,
              "modules": ns_module_count[ns],
              "deps":  sum(w for (a, _), w in ns_edges_w.items() if a == ns),
              "rdeps": sum(w for (_, b), w in ns_edges_w.items() if b == ns)} for ns in ns_set),
            key=lambda d: d["id"]),
        "links": [{"source": a, "target": b, "weight": w}
                  for (a, b), w in sorted(ns_edges_w.items())],
    }

    (OUT_DIR / "modules.json").write_text(json.dumps(modules_json, indent=2) + "\n")
    (OUT_DIR / "namespaces.json").write_text(json.dumps(namespaces_json, indent=2) + "\n")
    return modules_json, namespaces_json, ns_edges_w


def write_dot_svg_png(modules_json, namespaces_json, in_proj_edges, ns_edges_w, proj):
    dot = ['digraph fstar_modules {',
           '  rankdir=LR;',
           '  node [shape=box, fontname="Helvetica", fontsize=10, style=filled, fillcolor="#ffffff"];',
           '  edge [color="#888888", arrowsize=0.6];']
    for m in sorted(proj):
        color = NS_COLOR.get(ns_of(m), "#ffffff")
        dot.append(f'  "{m}" [fillcolor="{color}"];')
    for a, b in sorted(set(in_proj_edges)):
        dot.append(f'  "{a}" -> "{b}";')
    dot.append("}")
    (OUT_DIR / "modules.dot").write_text("\n".join(dot) + "\n")

    ns_dot = ['digraph fstar_namespaces {',
              '  rankdir=LR;',
              '  node [shape=box, style="filled,rounded", fontname="Helvetica", fontsize=12];',
              '  edge [color="#666666"];']
    for ns in sorted({n["id"] for n in namespaces_json["nodes"]}):
        color = NS_COLOR.get(ns, "#ffffff")
        ns_dot.append(f'  "{ns}" [fillcolor="{color}"];')
    for (a, b), n in sorted(ns_edges_w.items()):
        ns_dot.append(f'  "{a}" -> "{b}" [label="{n}", penwidth={1 + min(n, 8) * 0.4:.1f}];')
    ns_dot.append("}")
    (OUT_DIR / "namespaces.dot").write_text("\n".join(ns_dot) + "\n")

    if shutil.which("dot"):
        for stem in ("modules", "namespaces"):
            src = OUT_DIR / f"{stem}.dot"
            subprocess.run(["dot", "-Tsvg", str(src), "-o", str(OUT_DIR / f"{stem}.svg")], check=True)
            subprocess.run(["dot", "-Tpng", str(src), "-o", str(OUT_DIR / f"{stem}.png")], check=True)


def write_mermaid_and_text(modules_json, namespaces_json, ns_edges_w, in_proj_edges, proj):
    mmd = ["%% F* module dependency graph (from fstar.exe --dep graph)", "graph LR"]
    for m in sorted(proj):
        mmd.append(f'  {m.replace(".", "_")}["{m}"]')
    for a, b in sorted(set(in_proj_edges)):
        mmd.append(f'  {a.replace(".", "_")} --> {b.replace(".", "_")}')
    (OUT_DIR / "modules.mmd").write_text("\n".join(mmd) + "\n")

    ns_mmd = ["%% F* namespace dependency graph (from fstar.exe --dep graph)", "graph LR"]
    for ns in sorted({n["id"] for n in namespaces_json["nodes"]}):
        ns_mmd.append(f'  {ns}["{ns}"]')
    for (a, b), n in sorted(ns_edges_w.items()):
        ns_mmd.append(f'  {a} -->|{n}| {b}')
    (OUT_DIR / "namespaces.mmd").write_text("\n".join(ns_mmd) + "\n")

    out = defaultdict(set)
    for a, b in in_proj_edges:
        out[a].add(b)
    lines = ["# F* module dependency graph (from fstar.exe --dep graph)",
             f"# {len(proj)} modules, {len(set(in_proj_edges))} in-project edges", ""]
    for m in sorted(proj):
        ds = sorted(out[m])
        lines.append(f"{m} -> {', '.join(ds) if ds else '(no in-project deps)'}")
    (OUT_DIR / "modules.txt").write_text("\n".join(lines) + "\n")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: fstar_dep_to_json.py <dep.graph>", file=sys.stderr)
        return 2
    src = Path(argv[1]).read_text(encoding="utf-8", errors="replace")
    nodes, edges = parse_dot(src)
    proj = project_modules()
    in_proj_edges = [(a, b) for (a, b) in edges if a in proj and b in proj]

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    modules_json, namespaces_json, ns_edges_w = write_json(in_proj_edges, proj)
    write_dot_svg_png(modules_json, namespaces_json, in_proj_edges, ns_edges_w, proj)
    write_mermaid_and_text(modules_json, namespaces_json, ns_edges_w, in_proj_edges, proj)

    print(f"modules:    {len(modules_json['nodes'])} nodes, {len(modules_json['links'])} links")
    print(f"namespaces: {len(namespaces_json['nodes'])} nodes, {len(namespaces_json['links'])} links")
    print(f"output:     {OUT_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
