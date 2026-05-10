#!/usr/bin/env python3
"""Extract F* module dependency graph from `open`/`include`/`module M = ...`
statements in .fst/.fsti files.

This is a lightweight stand-in for `fstar.exe --dep graph` for environments
without the F* toolchain. It misses `friend` declarations and any
inline_for_extraction cross-module triggers, but covers the bulk of
dependencies the build sees.

Outputs (under formal/fstar/dep-graph/):
  modules.txt           : adjacency list, plain text
  modules.dot           : Graphviz, all modules
  modules.svg           : rendered SVG (if `dot` is on PATH)
  modules.mmd           : Mermaid graph
  namespaces.dot        : Graphviz, aggregated by top-level namespace
  namespaces.svg
  namespaces.mmd
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FSTAR_DIR = ROOT / "formal" / "fstar"
OUT_DIR = FSTAR_DIR / "dep-graph"

OPEN_RE = re.compile(r"^\s*open\s+([A-Z][\w.]*)", re.MULTILINE)
INCLUDE_RE = re.compile(r"^\s*include\s+([A-Z][\w.]*)", re.MULTILINE)
ABBREV_RE = re.compile(r"^\s*module\s+[A-Z]\w*\s*=\s*([A-Z][\w.]*)", re.MULTILINE)

STDLIB_PREFIXES = (
    "FStar", "Prims", "LowStar", "Steel", "Lib", "Spec", "EverParse",
)


def strip_comments(src: str) -> str:
    """Strip F* (* ... *) block comments (nesting-aware) and // line comments."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        if depth == 0 and src.startswith("//", i):
            j = src.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        if src.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and src.startswith("*)", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "".join(out)


def module_name_of(path: Path) -> str:
    return path.stem  # e.g. "SPARQL11.Algebra"


def is_stdlib(mod: str) -> bool:
    head = mod.split(".", 1)[0]
    return head in STDLIB_PREFIXES


def extract_deps(path: Path) -> set[str]:
    text = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
    deps: set[str] = set()
    for rx in (OPEN_RE, INCLUDE_RE, ABBREV_RE):
        for m in rx.finditer(text):
            deps.add(m.group(1))
    return deps


def main() -> int:
    files = sorted(
        list(FSTAR_DIR.glob("*.fst")) + list(FSTAR_DIR.glob("*.fsti")),
        key=lambda p: p.name,
    )
    # Merge .fst + .fsti for the same module
    by_module: dict[str, list[Path]] = defaultdict(list)
    for f in files:
        by_module[module_name_of(f)].append(f)

    project_modules = set(by_module.keys())

    deps: dict[str, set[str]] = {}
    external: dict[str, set[str]] = defaultdict(set)
    for mod, paths in sorted(by_module.items()):
        merged: set[str] = set()
        for p in paths:
            merged |= extract_deps(p)
        merged.discard(mod)
        in_project = {d for d in merged if d in project_modules}
        outside = {d for d in merged if d not in project_modules and not is_stdlib(d)}
        deps[mod] = in_project
        if outside:
            external[mod] = outside

    OUT_DIR.mkdir(parents=True, exist_ok=True)

    # ---- adjacency list (plain text) ----
    lines = ["# F* module dependency graph (open/include/module-abbrev derived)",
             f"# {len(project_modules)} modules in formal/fstar/", ""]
    for mod in sorted(deps):
        ds = sorted(deps[mod])
        if ds:
            lines.append(f"{mod} -> {', '.join(ds)}")
        else:
            lines.append(f"{mod} -> (no in-project deps)")
    if any(external.values()):
        lines += ["", "# External / non-stdlib references (likely assume val realisations or missing modules):"]
        for mod in sorted(external):
            lines.append(f"{mod} ~> {', '.join(sorted(external[mod]))}")
    (OUT_DIR / "modules.txt").write_text("\n".join(lines) + "\n")

    # ---- Graphviz: all modules ----
    namespace_color = {
        "Parser": "#cfe8ff",
        "RDF": "#d4f4dd",
        "SPARQL": "#ffe6b3",
        "SPARQL11": "#ffd699",
        "OWL": "#e6ccff",
        "RIF": "#ffd1dc",
        "SHACL": "#fff5b3",
        "Util": "#eeeeee",
        "Tableau": "#f5cba7",
        "Parquet": "#c8d6e5",
    }

    def ns_of(mod: str) -> str:
        return mod.split(".", 1)[0]

    dot = ['digraph fstar_modules {',
           '  rankdir=LR;',
           '  node [shape=box, fontname="Helvetica", fontsize=10, style=filled, fillcolor="#ffffff"];',
           '  edge [color="#888888", arrowsize=0.6];']
    for mod in sorted(project_modules):
        color = namespace_color.get(ns_of(mod), "#ffffff")
        dot.append(f'  "{mod}" [fillcolor="{color}"];')
    for mod in sorted(deps):
        for d in sorted(deps[mod]):
            dot.append(f'  "{mod}" -> "{d}";')
    dot.append("}")
    (OUT_DIR / "modules.dot").write_text("\n".join(dot) + "\n")

    # ---- Graphviz: aggregated by namespace ----
    ns_edges: dict[tuple[str, str], int] = defaultdict(int)
    ns_nodes: set[str] = set()
    for mod, ds in deps.items():
        a = ns_of(mod)
        ns_nodes.add(a)
        for d in ds:
            b = ns_of(d)
            ns_nodes.add(b)
            if a != b:
                ns_edges[(a, b)] += 1
    ns_dot = ['digraph fstar_namespaces {',
              '  rankdir=LR;',
              '  node [shape=box, style="filled,rounded", fontname="Helvetica", fontsize=12];',
              '  edge [color="#666666"];']
    for ns in sorted(ns_nodes):
        color = namespace_color.get(ns, "#ffffff")
        ns_dot.append(f'  "{ns}" [fillcolor="{color}"];')
    for (a, b), n in sorted(ns_edges.items()):
        ns_dot.append(f'  "{a}" -> "{b}" [label="{n}", penwidth={1 + min(n, 8) * 0.4:.1f}];')
    ns_dot.append("}")
    (OUT_DIR / "namespaces.dot").write_text("\n".join(ns_dot) + "\n")

    # ---- Mermaid ----
    mmd = ["%% F* module dependency graph", "graph LR"]
    for mod in sorted(project_modules):
        safe = mod.replace(".", "_")
        mmd.append(f'  {safe}["{mod}"]')
    for mod in sorted(deps):
        a = mod.replace(".", "_")
        for d in sorted(deps[mod]):
            b = d.replace(".", "_")
            mmd.append(f"  {a} --> {b}")
    (OUT_DIR / "modules.mmd").write_text("\n".join(mmd) + "\n")

    ns_mmd = ["%% F* namespace dependency graph", "graph LR"]
    for ns in sorted(ns_nodes):
        ns_mmd.append(f'  {ns}["{ns}"]')
    for (a, b), n in sorted(ns_edges.items()):
        ns_mmd.append(f'  {a} -->|{n}| {b}')
    (OUT_DIR / "namespaces.mmd").write_text("\n".join(ns_mmd) + "\n")

    # ---- render SVGs if graphviz present ----
    if shutil.which("dot"):
        for stem in ("modules", "namespaces"):
            src = OUT_DIR / f"{stem}.dot"
            svg = OUT_DIR / f"{stem}.svg"
            png = OUT_DIR / f"{stem}.png"
            subprocess.run(["dot", "-Tsvg", str(src), "-o", str(svg)], check=True)
            subprocess.run(["dot", "-Tpng", str(src), "-o", str(png)], check=True)

    # ---- summary ----
    print(f"Modules: {len(project_modules)}")
    edges = sum(len(v) for v in deps.values())
    print(f"In-project edges: {edges}")
    print(f"Namespaces: {len(ns_nodes)}")
    print(f"Output: {OUT_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
