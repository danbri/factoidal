#!/usr/bin/env python3
"""Module liveness from SOURCE, checked by a VERIFIED core (issue #448).

WHY THIS CHANGED (v2 -> v3)
============================

v2's OCaml-layer oracle was `ocamlobjinfo <unit>.cmx` — compiler
metadata that only exists AFTER a full native build of every consumer
and every extracted module (`bin/*/*.cmx` + `ocaml-output/*.cmx`). That
made the tool unusable on a checkout that has not run the full
extract+compile pipeline, and put an unverified hand-written Python
BFS in charge of the one property the tool exists to certify: "this
module is unreachable from every shipping entry point."

v3 removes BOTH problems:

1. SOURCE-ONLY dependency extraction. The OCaml-layer graph now comes
   from `ocamldep -modules` run directly over `bin/*/*.ml` (consumer
   entry points) and `formal/fstar/ocaml-output/*.ml` (F*-extracted
   project units) — no `.cmx`, no prior build, no `ocamlobjinfo`.
   `ocamldep` reads the SAME `open`/qualified-name syntax the OCaml
   compiler itself reads and prints the OCaml compiler's own
   capitalized unit names, so there is no possibility of the v1
   basename-casing bug (`RDF.Store.HDTTermCacheRegistry` briefly
   reported DEAD, 2026-08-17) recurring here: capitalization is
   `ocamldep`'s job now, not this script's string manipulation.

   HONESTY NOTE on what counts as "source" here: the `.ml` files under
   `formal/fstar/ocaml-output/` are COMMITTED INTERMEDIATES, extracted
   from the `.fst` files by `fstar.exe --codegen OCaml` (iron rule #9
   — committed so a fresh clone runs without the F* toolchain). They
   are not hand-written and are not the project's primary source; the
   `.fst` files are. The hand-written consumers under `bin/*/*.ml` and
   the F* layer itself (`formal/fstar/*.fst`) ARE primary source. This
   tool treats the extracted `.ml` as a reliable STAND-IN for "what the
   corresponding `.fst` module compiles to" (true by construction, per
   rule #2 — extraction, not hand-writing) purely so the OCaml-layer
   graph can be built without a build step.

2. An F*-VERIFIED reachability core (formal/fstar/Dep.Reachability.fst)
   computes the actual BFS, via the `bin/depcheck` consumer this script
   shells out to. `depcheck` calls the extracted `reachable`, then
   RE-CHECKS `is_closed`/`all_mem` on its own output before printing
   anything and REFUSES (exit 2) if either check fails — see that
   module's `closed_set_catches_all` theorem and `depcheck.ml`'s
   header. That refusal is what makes this script's DEAD verdicts
   trustworthy beyond "a Python loop appeared to terminate correctly":
   neither `depcheck`'s fuel bound nor its closure algorithm is
   trusted for soundness, only the theorem plus the runtime recheck of
   its (decidable) premises against the actual output are.

`depcheck` is cheap to build standalone — it links only
`Dep_Reachability.ml` (zero project-module dependencies) plus its own
~50-line `.ml`, not the ~150-module `$COMMON_MODULES` chain every other
consumer in `build-ocaml.sh` links against. This script builds that
standalone binary itself (cached under `tools/.depcheck-cache/`) if
neither `bin/<platform>/depcheck` nor a build-produced
`ocaml-output/depcheck` symlink is already present, so running this
tool does NOT require the full project extract+compile pipeline — only
`formal/fstar/ocaml-output/Dep_Reachability.ml` (committed, per iron
rule #9) and an `ocamlfind`/`fstar.lib` toolchain.

THE F* LAYER (unchanged from v2)
=================================

`fstar.exe --dep graph` still supplies the reverse-dependency check:
who refers to a module at the specification level, including
type-only/lemma-only uses the OCaml layer erases at extraction. A
module is reported DEAD only when BOTH layers agree.

LIMITS (stated, not hidden)
=============================

- `ocamldep -modules` sees every name a file's `open`/qualified
  references mention, including ones that are not project units
  (`Prims`, `FStar_*`, stdlib `List`/`Printf`/...). Those are filtered
  out by intersecting against the actual project-unit set, exactly as
  v2 filtered `ocamlobjinfo`'s "Implementations imported" section
  against `units`.
- `ocamldep` is a text/syntax-level tool: it does not know which
  `open`d names are actually USED vs merely opened-and-unused. This
  means v3 can OVER-approximate liveness (see the ocamldep-over-
  approximates note in the gate section) relative to v2's true-call
  BFS — that direction is safe (report fewer DEAD, not more); the
  reverse would not be.
- Interface-only intent (a module referenced only through a comment or
  string) is invisible to both `ocamldep` and `ocamlobjinfo` — this
  was already true of v2 and remains a limit of tree-agnostic parsing,
  not something v3 changes.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import defaultdict, deque

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OCAML_OUT = os.path.join(ROOT, "formal", "fstar", "ocaml-output")
BIN = os.path.join(ROOT, "bin")
FSTAR_DIR = os.path.join(ROOT, "formal", "fstar")
DEPCHECK_CACHE = os.path.join(ROOT, "tools", ".depcheck-cache")
DEPCHECK_SRC = os.path.join(ROOT, "bin", "depcheck", "depcheck.ml")


def ocaml_unit_name(basename):
    # The OCaml compiler capitalizes unit names: file fstar_pure_hashes.ml
    # is unit Fstar_pure_hashes. Only used here for a project unit's OWN
    # name (from its filename) — every DEPENDENCY name comes straight out
    # of `ocamldep -modules`, which already applies this rule itself, so
    # there is no v1-style "forgot to apply it on one side" bug surface.
    return basename[0].upper() + basename[1:]


def project_units():
    """unit name -> (basename, .ml path) for every extracted module."""
    units = {}
    for fn in os.listdir(OCAML_OUT):
        if fn.endswith(".ml"):
            units[ocaml_unit_name(fn[:-3])] = (fn[:-3], os.path.join(OCAML_OUT, fn))
    return units


def entry_points():
    """"dir/basename" -> .ml path for every hand-written consumer source."""
    eps = {}
    for d in os.listdir(BIN):
        sub = os.path.join(BIN, d)
        if not os.path.isdir(sub):
            continue
        for fn in os.listdir(sub):
            if fn.endswith(".ml"):
                eps[f"{d}/{fn[:-3]}"] = os.path.join(sub, fn)
    return eps


def ocamldep_modules(ml_path):
    """`ocamldep -modules FILE` -> list of module names it references.
    Pure source parsing — no compilation, no .cmx, no ocamlobjinfo."""
    try:
        out = subprocess.run(["ocamldep", "-modules", ml_path],
                              capture_output=True, text=True, timeout=60).stdout
    except Exception as e:
        print(f"WARNING: ocamldep failed on {ml_path} ({e})", file=sys.stderr)
        return []
    # Output form: "path/File.ml: Mod1 Mod2 Mod3" (possibly wrapped with
    # trailing backslash-newline continuations for long lines).
    text = out.replace("\\\n", " ")
    if ":" not in text:
        return []
    return text.split(":", 1)[1].split()


def ensure_depcheck():
    """Return a path to a working `depcheck` binary, building a standalone
    copy (Dep_Reachability.ml + depcheck.ml only — NOT $COMMON_MODULES,
    NOT the full project) if no build-produced one is already present.
    Returns None if it cannot be built (missing extracted module or
    toolchain), in which case the caller degrades honestly rather than
    silently trusting an unverified fallback."""
    for candidate in (
        os.path.join(OCAML_OUT, "depcheck"),
        os.path.join(BIN, "linux-x86_64", "depcheck"),
        os.path.join(BIN, "darwin-arm64", "depcheck"),
        os.path.join(BIN, "linux-arm64", "depcheck"),
        os.path.join(BIN, "darwin-x86_64", "depcheck"),
    ):
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate

    dep_ml = os.path.join(OCAML_OUT, "Dep_Reachability.ml")
    if not os.path.isfile(dep_ml):
        print("WARNING: formal/fstar/ocaml-output/Dep_Reachability.ml not "
              "found (extract Dep.Reachability.fst first); cannot build "
              "the verified depcheck core.", file=sys.stderr)
        return None
    if shutil.which("ocamlfind") is None:
        print("WARNING: ocamlfind not on PATH (activate the fstar opam "
              "switch); cannot build depcheck.", file=sys.stderr)
        return None

    os.makedirs(DEPCHECK_CACHE, exist_ok=True)
    out_bin = os.path.join(DEPCHECK_CACHE, "depcheck")
    newest_src = max(os.path.getmtime(dep_ml), os.path.getmtime(DEPCHECK_SRC))
    if os.path.isfile(out_bin) and os.path.getmtime(out_bin) >= newest_src:
        return out_bin

    print("module-liveness: building standalone depcheck (2 files, not "
          "the full project) ...", file=sys.stderr)
    # Compile from COPIES inside the cache dir, never in-place: ocamlopt
    # writes .cmi/.cmx/.o beside its source by default, and building
    # in-place inside formal/fstar/ocaml-output/ would race a concurrent
    # ./build-ocaml.sh compile writing the same directory (hazard: shared
    # .checked/.cmx cache across worktrees/agents).
    shutil.copy(dep_ml, os.path.join(DEPCHECK_CACHE, "Dep_Reachability.ml"))
    shutil.copy(DEPCHECK_SRC, os.path.join(DEPCHECK_CACHE, "depcheck.ml"))
    cmd = ["ocamlfind", "ocamlopt",
           "-package", "fstar.lib,str,zarith,sha,digestif.c,unix,uucp",
           "-linkpkg", "-w", "-8-14-26",
           "Dep_Reachability.ml", "depcheck.ml", "-o", "depcheck"]
    try:
        r = subprocess.run(cmd, cwd=DEPCHECK_CACHE, capture_output=True,
                            text=True, timeout=180)
    except Exception as e:
        print(f"WARNING: depcheck standalone build failed to run ({e})",
              file=sys.stderr)
        return None
    if r.returncode != 0 or not os.path.isfile(out_bin):
        print("WARNING: depcheck standalone build failed:", file=sys.stderr)
        print(r.stdout, file=sys.stderr)
        print(r.stderr, file=sys.stderr)
        return None
    os.chmod(out_bin, 0o755)
    return out_bin


def run_depcheck(depcheck_bin, edges, roots):
    """Shell out to the VERIFIED reachability core. Returns (reachable_set,
    refused, message). `refused=True` means depcheck's own runtime
    recheck of is_closed/all_mem rejected its own computed output —
    the anti-vacuity guarantee firing for real, not hypothetically."""
    stamp = str(int(time.time() * 1000))
    edges_path = os.path.join(DEPCHECK_CACHE, f"edges-{stamp}.txt")
    roots_path = os.path.join(DEPCHECK_CACHE, f"roots-{stamp}.txt")
    os.makedirs(DEPCHECK_CACHE, exist_ok=True)
    try:
        with open(edges_path, "w") as fh:
            for s, d in edges:
                fh.write(f"{s} {d}\n")
        with open(roots_path, "w") as fh:
            for r in roots:
                fh.write(f"{r}\n")
        r = subprocess.run([depcheck_bin, edges_path, roots_path],
                            capture_output=True, text=True, timeout=120)
    finally:
        for p in (edges_path, roots_path):
            try:
                os.unlink(p)
            except OSError:
                pass
    if r.returncode == 2:
        return None, True, r.stderr.strip()
    if r.returncode != 0:
        return None, True, f"depcheck exited {r.returncode}: {r.stderr.strip()}"
    reachable = set(line.strip() for line in r.stdout.splitlines() if line.strip())
    return reachable, False, None


def fstar_referrers():
    """F*-side reverse deps via `fstar.exe --dep graph` (name resolution,
    not grep). Falls back to raw mode with a warning if fstar is absent.
    Unchanged from v2."""
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
        print("ERROR: no consumer .ml found under bin/*/", file=sys.stderr)
        sys.exit(2)

    # ---- Part 1: source-only dependency extraction (no .cmx, no build) --
    unit_names = set(units)
    edges = []  # list of (src, dst) node-name pairs for depcheck
    all_nodes = set(eps) | unit_names
    for name, path in eps.items():
        for dep in ocamldep_modules(path):
            if dep in unit_names:
                edges.append((name, dep))
    for uname, (_, path) in units.items():
        for dep in ocamldep_modules(path):
            if dep in unit_names and dep != uname:
                edges.append((uname, dep))

    # ---- Part 2: verified reachability core (bin/depcheck) --------------
    depcheck_bin = ensure_depcheck()
    if depcheck_bin is None:
        print("ERROR: could not obtain a depcheck binary (verified core "
              "unavailable). See warnings above.", file=sys.stderr)
        sys.exit(2)

    reached, refused, msg = run_depcheck(depcheck_bin, edges, list(eps))
    if refused:
        print(f"ERROR: depcheck REFUSED its own output: {msg}", file=sys.stderr)
        print("This means the reachability computation produced a set that "
              "failed its own runtime is_closed/all_mem recheck -- refusing "
              "to report any liveness verdict rather than trust it.",
              file=sys.stderr)
        sys.exit(2)

    reached_units = (reached & unit_names)
    unreached = sorted(unit_names - reached_units)

    # js/npm surface annotation (unchanged from v2): a native-dead module
    # named in the js FSTAR_MODULES list may be js-only-live.
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

    report = {"engine": "depcheck (Dep.Reachability, F*-verified)",
              "source_only": True, "cmx_reads": 0,
              "entry_points": sorted(eps), "project_units": len(units),
              "ocaml_reachable": len(reached_units), "ocaml_unreachable": [],
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
