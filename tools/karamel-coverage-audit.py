#!/usr/bin/env python3
"""KaRaMeL coverage audit — see tools/karamel-coverage-audit.sh for the
foreground entry point and docs/designissues/2026-07-06-karamel-coverage-audit.md
for the write-up this script's output feeds.

For every formal/fstar/*.fst module, determine whether it (and its full
dependency closure) extracts through F* --codegen krml and then lowers
through krml to C. Every module is tested for real (no inference): an
earlier draft shortcut-marked dependents of a blocked module as
transitively blocked without testing them, and that produced a measured
false positive — RDFS.Closure lowers fine even though its dependency
RDF.Vocabulary.Axioms times out when IT is the bundle root, because a
consumer's bundle only monomorphizes the dep's REACHABLE definitions.
So: test everything, and use the dependency DAG only to LABEL failures:
BLOCKED_SELF when every in-set dependency lowers clean (the module's own
closure is the problem) vs BLOCKED_TRANSITIVE when at least one
dependency is itself blocked (fixing the dependency is the cheaper
unlock candidate; retest after). Note the .fsti caveat: --dep full
reports interface-backed dependencies as .fsti.checked edges, which
this parser (like build-ocaml.sh's) drops — as of 2026-07-06 all eight
.fsti-backed modules PASS, so no label is affected.

Reads formal/fstar/*.fst directly and writes all krml/.krml/.c scratch
output under --scratch (outside formal/fstar/, so this script never
touches build-ocaml.sh's .checked cache, .extract-state manifest, or
ocaml-output/ symlinks). It DOES read the existing formal/fstar/*.fst.checked
cache read-only (via --cache_checked_modules) the same way build-ocaml.sh
does, so F* extraction is fast (no re-verification) — it does not write
new .checked files anywhere but formal/fstar/ itself, matching normal
`fstar.exe` behavior on an unmodified tree.

Usage:
  eval $(opam env --switch=fstar)
  python3 tools/karamel-coverage-audit.py --fstar-dir formal/fstar \
      --scratch /path/to/scratch --out-tsv <path> --out-log <path>
"""
import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
import time

KRML_WARN_ERROR = "-9-11-15+2"
# -9  : static initializers needed (harmless per c-output/README.md)
# -11 : closures/lambdas not in Low* (RDF.Graph.Executable's own
#       Makefile target already suppresses this; the project accepts
#       non-Low* C as "logically correct but not standalone" per that
#       Makefile's comment)
# -15 : GC types / mathematical integers (same acceptance)
# +2  : promote "extern without implementation" to fatal->warning per
#       tools/karamel-c-build.sh's pilot rationale (assume val externs
#       get C-side stubs at link time; that is a KNOWN, separate later
#       step, not a lowering blocker)
FSTAR_TIMEOUT_S = 120
KRML_TIMEOUT_S = 120


def run(cmd, cwd, timeout_s):
    t0 = time.time()
    try:
        p = subprocess.run(
            cmd, cwd=cwd, timeout=timeout_s,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        return p.returncode, p.stdout.decode("utf-8", "replace"), time.time() - t0, False
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode("utf-8", "replace")
        return None, out, time.time() - t0, True


def parse_depend_make(depend_path, mod_set):
    """Mirror build-ocaml.sh's DEPS[] parser: join line continuations,
    read '<Mod>.fst.checked: <deps...>' targets, keep only in-set deps."""
    with open(depend_path) as f:
        raw = f.read()
    joined_lines = []
    buf = ""
    for line in raw.splitlines():
        if line.endswith("\\"):
            buf += line[:-1] + " "
        else:
            joined_lines.append(buf + line)
            buf = ""
    deps = {}
    for line in joined_lines:
        if ".fst.checked:" not in line:
            continue
        target, _, rest = line.partition(":")
        target = os.path.basename(target)
        if not target.endswith(".fst.checked"):
            continue
        target_mod = target[: -len(".fst.checked")]
        if target_mod not in mod_set:
            continue
        mod_deps = []
        for tok in rest.split():
            if tok.endswith(".fst.checked"):
                d = os.path.basename(tok)[: -len(".fst.checked")]
                if d in mod_set and d != target_mod:
                    mod_deps.append(d)
        deps[target_mod] = sorted(set(mod_deps))
    for m in mod_set:
        deps.setdefault(m, [])
    return deps


def kahn_layers(deps, mod_set):
    placed = set()
    remaining = set(mod_set)
    layers = []
    while remaining:
        layer = sorted(m for m in remaining if all(d in placed for d in deps[m]))
        if not layer:
            raise SystemExit(f"FATAL: dependency cycle among: {sorted(remaining)}")
        layers.append(layer)
        placed.update(layer)
        remaining -= set(layer)
    return layers


CLASSIFY_RULES = [
    (re.compile(r"Fatal error: exception Stack overflow"), "monomorphization stack overflow"),
    (re.compile(r"[Oo]ut of memory"), "monomorphization OOM"),
    (re.compile(r"Warning (\d+) is fatal, exiting"), "warn-fatal-{0}"),
    (re.compile(r"Fatal error: exception (\S+)"), "krml fatal: {0}"),
    (re.compile(r"\* Error (\d+) at"), "F* codegen-krml error {0}"),
    (re.compile(r"^(Error \d+.*)$", re.M), "F* extraction error"),
    (re.compile(r"is not supported by Kre?MLin|not supported by KaRaMeL"), "unsupported construct"),
]


def classify(log_text):
    for pat, label in CLASSIFY_RULES:
        m = pat.search(log_text)
        if m:
            try:
                cat = label.format(*m.groups())
            except (IndexError, KeyError):
                cat = label
            # first_error: the full line containing the match
            ls = log_text.rfind("\n", 0, m.start()) + 1
            le = log_text.find("\n", m.end())
            if le == -1:
                le = len(log_text)
            return cat, log_text[ls:le].strip()[:220]
    # fallback: first line mentioning error/exception, else last non-empty line
    for line in log_text.splitlines():
        if re.search(r"error|exception|fatal", line, re.I):
            return "other (see raw log)", line.strip()[:220]
    nonempty = [l for l in log_text.splitlines() if l.strip()]
    return "other (see raw log)", (nonempty[-1].strip()[:220] if nonempty else "(empty log)")


def test_module(mod_name, fstar_dir, scratch):
    """Returns dict with status/category/first_error/timings for one module,
    tested in isolation (F* resolves and extracts its full .checked-cache
    dependency closure; krml lowers with a single-module wildcard bundle,
    which is what actually triggers cross-module monomorphization)."""
    modir = os.path.join(scratch, mod_name.replace(".", "_"))
    os.makedirs(modir, exist_ok=True)
    fstar_odir = os.path.join(modir, "fstar-out")
    krml_odir = os.path.join(modir, "krml-out")
    os.makedirs(fstar_odir, exist_ok=True)
    os.makedirs(krml_odir, exist_ok=True)

    rc, out, dt, timed_out = run(
        ["fstar.exe", "--z3version", "4.13.3", "--codegen", "krml",
         "--odir", fstar_odir, "--cache_checked_modules", "--extract", "krml:*",
         f"{mod_name}.fst"],
        cwd=fstar_dir, timeout_s=FSTAR_TIMEOUT_S,
    )
    full_log = f"=== fstar.exe --codegen krml ({mod_name}) rc={rc} dt={dt:.1f}s timeout={timed_out} ===\n{out}\n"
    if timed_out:
        return dict(status="TIMEOUT_SELF", stage="fstar", category=f"timeout ({FSTAR_TIMEOUT_S}s cap, F* codegen krml)",
                     first_error="(timed out)", log=full_log, fstar_s=dt, krml_s=0.0)
    out_krml = os.path.join(fstar_odir, "out.krml")
    if rc != 0 or not os.path.exists(out_krml) or f"Verified module: {mod_name}" not in out:
        cat, err = classify(out)
        return dict(status="BLOCKED_SELF", stage="fstar", category=cat, first_error=err,
                     log=full_log, fstar_s=dt, krml_s=0.0)

    rc2, out2, dt2, timed_out2 = run(
        ["krml", "-skip-compilation", "-skip-makefiles", "-tmpdir", krml_odir,
         "-warn-error", KRML_WARN_ERROR,
         "-bundle", f"{mod_name}=*[rename=Audit]", out_krml],
        cwd=fstar_dir, timeout_s=KRML_TIMEOUT_S,
    )
    full_log += f"=== krml lowering ({mod_name}) rc={rc2} dt={dt2:.1f}s timeout={timed_out2} ===\n{out2}\n"
    if timed_out2:
        return dict(status="TIMEOUT_SELF", stage="krml", category=f"timeout ({KRML_TIMEOUT_S}s cap, krml lowering)",
                     first_error="(timed out)", log=full_log, fstar_s=dt, krml_s=dt2)
    # rc2==0 is authoritative: -warn-error already promotes/demotes the
    # warnings this project has decided are or are not fatal (see
    # KRML_WARN_ERROR above), so a clean exit means krml itself accepted
    # the AST. Do NOT additionally require an Audit.c file to exist —
    # a module that is 100% `assume val` (no pure definitions reaching
    # the bundle, e.g. JSONLD.Loader's single I/O seam) legitimately
    # lowers to only a header (Audit.h) with an extern declaration, and
    # that is success, not a blocker.
    if rc2 != 0:
        cat, err = classify(out2)
        return dict(status="BLOCKED_SELF", stage="krml", category=cat, first_error=err,
                     log=full_log, fstar_s=dt, krml_s=dt2)
    header_only = (not os.path.exists(os.path.join(krml_odir, "Audit.c"))
                   and os.path.exists(os.path.join(krml_odir, "Audit.h")))
    note = "header-only (all-assume-val module, no C body emitted)" if header_only else ""
    return dict(status="PASS", stage="", category=note, first_error="", log=full_log, fstar_s=dt, krml_s=dt2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fstar-dir", required=True)
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--out-tsv", required=True)
    ap.add_argument("--out-log", required=True)
    ap.add_argument("--jobs", type=int, default=max(1, os.cpu_count() or 1))
    ap.add_argument("--depend-file", default=None,
                     help="Reuse an existing `fstar.exe --dep full` output instead of recomputing.")
    args = ap.parse_args()

    fstar_dir = os.path.abspath(args.fstar_dir)
    scratch = os.path.abspath(args.scratch)
    os.makedirs(scratch, exist_ok=True)

    modules = sorted(
        f[:-4] for f in os.listdir(fstar_dir)
        if f.endswith(".fst") and os.path.isfile(os.path.join(fstar_dir, f))
    )
    mod_set = set(modules)
    print(f"[audit] {len(modules)} .fst modules found in {fstar_dir}", file=sys.stderr)

    depend_path = args.depend_file or os.path.join(scratch, "depend.make")
    if not args.depend_file:
        rc = subprocess.run(
            ["fstar.exe", "--dep", "full"] + [f"{m}.fst" for m in modules],
            cwd=fstar_dir, stdout=open(depend_path, "w"),
            stderr=open(os.path.join(scratch, "depend.log"), "w"),
        ).returncode
        if rc != 0:
            raise SystemExit(f"FATAL: fstar.exe --dep full failed (rc={rc}); see {scratch}/depend.log")

    deps = parse_depend_make(depend_path, mod_set)
    layers = kahn_layers(deps, mod_set)
    print(f"[audit] {len(layers)} dependency layers", file=sys.stderr)

    # Test EVERY module for real. Order by dependency layer only so log
    # output reads bottom-up; the result of one module never suppresses
    # the test of another (see docstring for why the shortcut was removed).
    results = {}
    n_tested = 0
    with open(args.out_log, "w") as logf:
        for layer_idx, layer in enumerate(layers):
            print(f"[audit] layer {layer_idx}: {len(layer)} module(s)", file=sys.stderr)
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
                futs = {ex.submit(test_module, m, fstar_dir, scratch): m for m in layer}
                for fut in concurrent.futures.as_completed(futs):
                    m = futs[fut]
                    r = fut.result()
                    n_tested += 1
                    results[m] = r
                    logf.write(r["log"])
                    logf.flush()
                    print(f"    [{m}] {r['status']} "
                          f"fstar={r['fstar_s']:.1f}s krml={r['krml_s']:.1f}s "
                          f"{r['category']}", file=sys.stderr)

    # Label: a failed module whose in-set dependency closure contains a
    # failed module is BLOCKED_TRANSITIVE (unlock candidate: fix the dep,
    # retest); a failed module all of whose deps pass is BLOCKED_SELF.
    def closure(m, seen=None):
        if seen is None:
            seen = set()
        for d in deps[m]:
            if d not in seen:
                seen.add(d)
                closure(d, seen)
        return seen

    status = {}
    category = {}
    first_error = {}
    timings = {}
    for m in modules:
        r = results[m]
        timings[m] = (r["fstar_s"], r["krml_s"])
        first_error[m] = r["first_error"]
        if r["status"] == "PASS":
            status[m] = "PASS"
            category[m] = r["category"]
            continue
        blocked_deps = sorted(d for d in closure(m) if results[d]["status"] != "PASS")
        if r["status"] == "TIMEOUT_SELF":
            status[m] = "TIMEOUT"
        elif blocked_deps:
            status[m] = "BLOCKED_TRANSITIVE"
        else:
            status[m] = "BLOCKED_SELF"
        category[m] = r["category"]
        if blocked_deps and r["status"] != "TIMEOUT_SELF":
            category[m] += " [failing deps in closure: " + ", ".join(blocked_deps) + "]"

    with open(args.out_tsv, "w") as tf:
        tf.write("module\tstatus\tblocker_category\tfirst_error\tdirect_deps\tn_direct_deps\tfstar_s\tkrml_s\n")
        for m in modules:
            st = status.get(m, "UNKNOWN")
            fs, ks = timings.get(m, (0.0, 0.0))
            tf.write("\t".join([
                m, st, category.get(m, ""), first_error.get(m, ""),
                ",".join(deps[m]), str(len(deps[m])),
                f"{fs:.2f}", f"{ks:.2f}",
            ]) + "\n")

    n_pass = sum(1 for m in modules if status.get(m) == "PASS")
    n_blocked_self = sum(1 for m in modules if status.get(m) == "BLOCKED_SELF")
    n_timeout = sum(1 for m in modules if status.get(m) == "TIMEOUT")
    n_transitive = sum(1 for m in modules if status.get(m) == "BLOCKED_TRANSITIVE")
    print(f"[audit] DONE: {len(modules)} modules total, all {n_tested} tested with krml", file=sys.stderr)
    print(f"[audit] PASS={n_pass} BLOCKED_SELF={n_blocked_self} TIMEOUT={n_timeout} "
          f"BLOCKED_TRANSITIVE={n_transitive}", file=sys.stderr)
    print(f"[audit] TSV: {args.out_tsv}", file=sys.stderr)
    print(f"[audit] raw log: {args.out_log}", file=sys.stderr)


if __name__ == "__main__":
    main()
