#!/usr/bin/env python3
"""Extract F* type-level dependency graph: which types reference which
other types in their body.

Each `type Foo = ...` / `noeq type Foo = ...` / `unopteq type Foo = ...`
declaration becomes a node. Edge A -> B is emitted whenever B's name
appears as a bare identifier inside A's body.

Limitations (intentional, called out in the SPA):
- regex-based, no real F* parser; doesn't track shadowing, doesn't
  follow `module M = X.Y` aliases.
- bodies are captured up to the next top-level declaration, so
  multi-line records with deeply nested types are fine, but anything
  that spans into a comment or pre-condition might over-count.
- only top-level types are nodes. fields and constructors are NOT
  separate nodes (they're listed inside the type they belong to).

Output (docs/web/demos/dep-graph/):
  terms.json    — data for the D3 SPA (every type, including isolated)
  terms.dot     — Graphviz, connected types only, rankdir=BT for
                  bottom-up "foundations below, consumers above"
                  layered package-structure planning
  terms.svg/png — rendered (if `dot` on PATH)

Run after fstar_dep_to_json.py (or stand-alone — they're independent).
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

TOP_LEVEL_KEYWORDS = (
    "let", "val", "type", "module", "open", "include", "effect",
    "assume", "private", "abstract",
)
TYPE_DECL_RE = re.compile(
    r"^\s*(?:\[@@?[^\]]+\]\s*)?"
    r"(?:(?:noeq|unopteq|inline_for_extraction|irreducible|private|abstract|new_effect|unfold)\s+)*"
    r"type\s+([a-z_][\w']*)\b"
)
ANY_TOP_RE = re.compile(
    r"^\s*(?:\[@@?[^\]]+\]\s*)?"
    r"(?:(?:noeq|unopteq|inline_for_extraction|irreducible|private|abstract|"
    r"new_effect|unfold|assume)\s+)*"
    r"(let|val|type|module|open|include|effect)\b"
)
TOKEN_RE = re.compile(r"[A-Za-z_][\w']*")
RECORD_FIELD_RE = re.compile(r"^\s*([a-z_][\w']*)\s*:\s*(.+?)\s*;?\s*$")
CTOR_RE = re.compile(r"^\s*\|\s*([A-Z][\w']*)\b\s*:?\s*(.*)$")

FSTAR_KEYWORDS = {
    "let", "in", "rec", "and", "fun", "match", "with", "if", "then", "else",
    "val", "type", "module", "open", "include", "begin", "end",
    "true", "false", "Tot", "Lemma", "ST", "Stack", "Pure", "GTot",
    "requires", "ensures", "modifies", "decreases", "by", "of",
    "list", "option", "string", "int", "nat", "bool", "unit", "char", "Type", "prop",
    "Some", "None", "exists", "forall", "fst", "snd", "Cons", "Nil",
    "function", "noeq", "unopteq", "inline_for_extraction", "irreducible",
    "private", "abstract", "assume", "unfold", "new_effect",
}


def strip_block_comments(src: str) -> str:
    """Remove F* (* ... *) comments (nesting-aware) and // line comments."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("//", i):
            j = src.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        if src.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth > 0 and src.startswith("*)", i):
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "".join(out)


def parse_module(path: Path):
    """Return list of (type_name, body_lines, kind, fields_or_ctors)."""
    src = strip_block_comments(path.read_text(encoding="utf-8", errors="replace"))
    lines = src.split("\n")
    decls = []
    i = 0
    while i < len(lines):
        m = TYPE_DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        body_lines = [lines[i]]
        j = i + 1
        while j < len(lines):
            ln = lines[j]
            if ln.strip() and ANY_TOP_RE.match(ln):
                break
            body_lines.append(ln)
            j += 1
        body = "\n".join(body_lines)
        # Classify and extract fields / ctors
        if "{" in body and "}" in body:
            kind = "record"
            members = []
            for ln in body_lines[1:]:
                fm = RECORD_FIELD_RE.match(ln)
                if fm and fm.group(1) not in FSTAR_KEYWORDS:
                    members.append(fm.group(1))
            fields_or_ctors = members
        elif any(CTOR_RE.match(ln) for ln in body_lines):
            kind = "variant"
            ctors = [m.group(1) for ln in body_lines for m in [CTOR_RE.match(ln)] if m]
            fields_or_ctors = ctors
        else:
            kind = "alias"
            fields_or_ctors = []
        decls.append((name, body, kind, fields_or_ctors))
        i = j
    return decls


def main() -> int:
    files = sorted(FSTAR_DIR.glob("*.fst")) + sorted(FSTAR_DIR.glob("*.fsti"))
    by_name: dict[str, dict] = {}
    by_module: dict[str, list[str]] = defaultdict(list)
    bodies: dict[str, str] = {}
    for f in files:
        mod = f.stem
        for name, body, kind, members in parse_module(f):
            if name in by_name:
                # Same name in multiple modules — keep first, log dup
                continue
            by_name[name] = {
                "id": name, "module": mod, "namespace": mod.split(".", 1)[0],
                "kind": kind, "members": members,
            }
            by_module[mod].append(name)
            bodies[name] = body

    # Build edges by tokenizing each body and matching against known type names
    edges: list[tuple[str, str]] = []
    for src_name, body in bodies.items():
        # Skip the head "type X =" line — we want the RHS only
        first_eq = body.find("=")
        rhs = body[first_eq + 1:] if first_eq != -1 else body
        seen_targets = set()
        for tok in TOKEN_RE.findall(rhs):
            if tok in FSTAR_KEYWORDS or tok == src_name:
                continue
            if tok in by_name and tok not in seen_targets:
                edges.append((src_name, tok))
                seen_targets.add(tok)

    deg_in: dict[str, int] = defaultdict(int)
    deg_out: dict[str, int] = defaultdict(int)
    for a, b in edges:
        deg_out[a] += 1
        deg_in[b] += 1

    nodes_out = []
    for name, info in sorted(by_name.items()):
        nodes_out.append({
            "id": name,
            "namespace": info["namespace"],
            "module": info["module"],
            "kind": info["kind"],
            "members": info["members"],
            "deps": deg_out.get(name, 0),
            "rdeps": deg_in.get(name, 0),
            "inProject": True,
        })
    out = {
        "nodes": nodes_out,
        "links": [{"source": a, "target": b, "weight": 1} for a, b in sorted(set(edges))],
    }
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUT_DIR / "terms.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"terms.json: {len(nodes_out)} nodes, {len(out['links'])} edges")

    write_layered_dot(nodes_out, out["links"])
    print(f"top referenced: " + ", ".join(
        f"{n['id']}({n['rdeps']})"
        for n in sorted(nodes_out, key=lambda n: -n["rdeps"])[:8]
    ))
    return 0


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
KIND_SHAPE = {"record": "box", "variant": "diamond", "alias": "ellipse"}


def write_layered_dot(nodes_out, links):
    """Layered Graphviz diagram, connected nodes only.

    rankdir=BT puts foundations at the bottom — types most-referenced
    by others sink to the floor, leaf consumers float to the top.
    Reading bottom-up traces dependency chains; horizontal neighbours
    at the same rank are "candidates for the same package" since they
    sit at the same depth and are likely used together.

    NO module clusters: the goal is to plan a NEW package layout, so
    forcing current-module groupings would obscure the natural
    cleavage planes. Node colour still indicates current namespace via
    a legend, so you can see "this type is currently in Parser but
    its neighbours are mostly RDF — move it" at a glance.
    """
    connected = {n["id"] for n in nodes_out if n["deps"] + n["rdeps"] > 0}
    node_info = {n["id"]: n for n in nodes_out if n["id"] in connected}
    edges = [(l["source"], l["target"]) for l in links
             if l["source"] in connected and l["target"] in connected]

    namespaces_present = sorted({n["namespace"] for n in node_info.values()})

    dot = ['digraph fstar_terms {',
           '  rankdir=BT;',
           '  concentrate=true;',
           '  nodesep=0.22; ranksep=0.7;',
           '  splines=spline;',
           '  graph [fontname="Helvetica", fontsize=11, bgcolor="#0f1115",'
           '         fontcolor="#cccccc", label="F* types — dependency hierarchy ('
           f'{len(connected)} types, {len(edges)} edges)\\n'
           'shape: ▭ record · ◇ variant · ◯ alias · '
           'colour: namespace · arrow: A uses B", labelloc=t];',
           '  node  [fontname="Helvetica", fontsize=11, style=filled,'
           '         color="#0c0e13", fontcolor="#0c0e13", margin="0.06,0.03"];',
           '  edge  [color="#5a6173", arrowsize=0.55, penwidth=0.7];']
    for name in sorted(node_info):
        n = node_info[name]
        shape = KIND_SHAPE.get(n["kind"], "ellipse")
        fill = NS_COLOR.get(n["namespace"], "#dddddd")
        # Tooltip = current module for hover (works in SVG, not PNG)
        dot.append(
            f'  "{name}" [shape={shape}, fillcolor="{fill}", '
            f'tooltip="{name} — {n["kind"]} in {n["module"]}"];'
        )
    for a, b in sorted(set(edges)):
        dot.append(f'  "{a}" -> "{b}";')
    # Legend cluster on the side
    dot.append('  subgraph cluster_legend {')
    dot.append('    label="namespace"; fontcolor="#9aa3b2"; fontsize=10;')
    dot.append('    style="rounded,dashed"; color="#3a4252";')
    dot.append('    rank=sink;')
    for ns in namespaces_present:
        fill = NS_COLOR.get(ns, "#dddddd")
        dot.append(
            f'    "_legend_{ns}" [label="{ns}", shape=box, '
            f'fillcolor="{fill}", style=filled, fontsize=10];'
        )
    # Invisible edges to vertically stack the legend
    for a, b in zip(namespaces_present, namespaces_present[1:]):
        dot.append(f'    "_legend_{a}" -> "_legend_{b}" [style=invis];')
    dot.append('  }')
    dot.append("}")
    (OUT_DIR / "terms.dot").write_text("\n".join(dot) + "\n")

    if shutil.which("dot"):
        subprocess.run(["dot", "-Tsvg", str(OUT_DIR / "terms.dot"),
                        "-o", str(OUT_DIR / "terms.svg")], check=True)
        subprocess.run(["dot", "-Tpng", "-Gdpi=110",
                        str(OUT_DIR / "terms.dot"),
                        "-o", str(OUT_DIR / "terms.png")], check=True)
        print(f"terms.dot/svg/png written (connected nodes: {len(connected)}, edges: {len(edges)})")


if __name__ == "__main__":
    sys.exit(main())
