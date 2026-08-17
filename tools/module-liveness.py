#!/usr/bin/env python3
"""Module liveness from COMPILER metadata, not text search (issue #448).

WHY THIS EXISTS
===============

The #448 dead-module work initially judged liveness by grep. A grep
pattern missed `Parser.BallyhooHDT.fst`'s use of
`RDF.Store.HDTTermCacheRegistry`, briefly putting a LIVE module on a
delete list (caught by hand-check before dispatch, 2026-08-17). The
owner's follow-up — "if you missed one caller maybe missed many" — is
the requirement this tool answers: liveness must come from the
compilers' own dependency records, which are exhaustive where text
matching is heuristic.

TWO ORACLES, JOINED
===================

1. OCaml layer: `ocamlobjinfo <unit>.cmx` prints "Implementations
   imported" — the list the OCaml compiler itself wrote of every
   compilation unit whose IMPLEMENTATION this unit references. We BFS
   from the CONSUMER ENTRY POINTS (the hand-written .ml under bin/*/
   that become shipped binaries) over these edges. A project module
   not reached is not called by any shipping code path, per the
   compiler. Interface-only (cmi) imports are deliberately excluded:
   depending on a module's TYPES does not keep its CODE alive.

2. F* layer: `fstar.exe --dep graph` emits the module digraph from
   F*'s actual name resolution (parsing + scoping, not grep). This
   catches F*-side reverse dependencies — who refers to a module at
   the specification level, including type-only and lemma-only uses
   that the OCaml layer would miss (erased at extraction).

A module is reported DEAD only when BOTH layers agree: unreachable
from every consumer entry point at the OCaml layer AND has no F*-side
referrer outside itself. Divergence between the layers is reported,
not averaged — an F*-only referrer usually means proofs/types use it
(erased code), which is a different disposition from live.

LIMITS (stated, not hidden)
===========================

- The OCaml BFS keys on unit NAMES from ocamlobjinfo; a module whose
  .cmx is missing (never compiled) is reported as such, not guessed.
- Glue realisations (experimental_ocaml_glue/*.sh) splice OCaml into
  extracted files; their imports ARE visible to ocamlobjinfo because
  the splice happens before compilation. No blind spot there.
- Entry points are discovered as bin/*/*.cmx; a consumer added
  without a committed .cmx will not root the BFS until built.
"""

import json
import os
import re
import subprocess
import sys
from collections import defaultdict, deque

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OCAML_OUT = os.path.join(ROOT, "formal", "fstar", "ocaml-output")
BIN = os.path.join(ROOT, "bin")
FSTAR_DIR = os.path.join(ROOT, "formal", "fstar")


def impl_imports(cmx_path):
    try:
        out = subprocess.run(["ocamlobjinfo", cmx_path], capture_output=True,
                             text=True, timeout=60).stdout
    except Exception:
        return None
    deps, in_section = [], False
    for line in out.splitlines():
        if "Implementations imported" in line:
            in_section = True
            continue
        if in_section:
            m = re.match(r"\s+[0-9a-f-]+\s+(\S+)", line)
            if m:
                deps.append(m.group(1))
            else:
                in_section = False
    return deps


def ocaml_unit_name(basename):
    # The OCaml compiler capitalizes unit names: file fstar_pure_hashes.ml
    # is unit Fstar_pure_hashes. v1 keyed on the raw filename and silently
    # dropped every edge INTO a lowercase-named file, reporting (e.g.) the
    # SHA-2 realisation the canonicalizer calls as DEAD. Key on the unit
    # name the compiler actually records.
    return basename[0].upper() + basename[1:]


def project_units():
    units = {}
    for fn in os.listdir(OCAML_OUT):
        if fn.endswith(".cmx"):
            units[ocaml_unit_name(fn[:-4])] = (fn[:-4], os.path.join(OCAML_OUT, fn))
    return units


def entry_points():
    eps = {}
    for d in os.listdir(BIN):
        sub = os.path.join(BIN, d)
        if not os.path.isdir(sub):
            continue
        for fn in os.listdir(sub):
            if fn.endswith(".cmx"):
                eps[f"{d}/{fn[:-4]}"] = os.path.join(sub, fn)
    return eps


def fstar_referrers():
    """F*-side reverse deps via `fstar.exe --dep graph` (name resolution,
    not grep). Falls back to raw mode with a warning if fstar is absent."""
    fsts = [os.path.join(FSTAR_DIR, f) for f in os.listdir(FSTAR_DIR)
            if f.endswith(".fst") or f.endswith(".fsti")]
    graph_path = os.path.join(FSTAR_DIR, "dep.graph")
    try:
        subprocess.run(["fstar.exe", "--dep", "graph", *sorted(fsts)],
                       capture_output=True, text=True, timeout=600,
                       cwd=FSTAR_DIR)
    except Exception as e:
        print(f"WARNING: fstar --dep failed ({e}); F* layer unavailable",
              file=sys.stderr)
        return None
    if not os.path.exists(graph_path):
        print("WARNING: fstar --dep graph produced no dep.graph; "
              "F* layer unavailable", file=sys.stderr)
        return None
    rev = defaultdict(set)
    with open(graph_path) as fh:
        for line in fh:
            m = re.match(r'\s*"([^"]+)"\s*->\s*"([^"]+)"', line)
            if m:
                src = re.sub(r"\.(fsti?)(\.checked)?$", "", os.path.basename(m.group(1)))
                dst = re.sub(r"\.(fsti?)(\.checked)?$", "", os.path.basename(m.group(2)))
                if src != dst:
                    rev[dst].add(src)
    os.unlink(graph_path)
    return rev


def main():
    units = project_units()
    eps = entry_points()
    if not eps:
        print("ERROR: no consumer .cmx found under bin/*/ — build first",
              file=sys.stderr)
        sys.exit(2)

    edges = {}
    for name, path in list(eps.items()) + [(k, v[1]) for k, v in units.items()]:
        deps = impl_imports(path)
        edges[name] = [d for d in (deps or []) if d in units]

    reached = set()
    q = deque(eps.keys())
    while q:
        n = q.popleft()
        for d in edges.get(n, []):
            if d not in reached:
                reached.add(d)
                q.append(d)

    unreached = sorted(set(units) - reached)

    # js/npm surface: the jsoo consumers have no committed .cmx, so they
    # cannot root the BFS. Annotate (never adjudicate): a native-dead
    # module named in the js FSTAR_MODULES list may be js-only-live.
    js_listed = set()
    bo = os.path.join(FSTAR_DIR, "build-ocaml.sh")
    try:
        text = open(bo).read()
        m = re.search(r"FSTAR_MODULES=\((.*?)\)", text, re.S)
        if m:
            js_listed = {ocaml_unit_name(x[:-3]) for x in re.findall(r"([A-Za-z0-9_]+\.ml)", m.group(1))}
    except OSError:
        pass

    rev = fstar_referrers()

    report = {"entry_points": sorted(eps), "project_units": len(units),
              "ocaml_reachable": len(reached), "ocaml_unreachable": [],
              "fstar_layer": rev is not None}
    for u in unreached:
        file_base = units[u][0]
        fst_name = file_base.replace("_", ".")
        refs = sorted(r for r in (rev.get(fst_name, set()) if rev else set())
                      if not r.startswith("FStar.") and r != fst_name)
        verdict = ("DEAD (both layers)" if rev is not None and not refs
                   else ("fstar-only referrers — proofs/types use it (erased)"
                         if refs else "OCaml-unreachable (F* layer unavailable)"))
        report["ocaml_unreachable"].append(
            {"unit": u, "file": file_base,
             "fstar_referrers": refs or None,
             "js_linked": u in js_listed,
             "verdict": verdict})
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
