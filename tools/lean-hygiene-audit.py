#!/usr/bin/env python3
"""Fail the build on a Lean escape hatch that `lake build` does not fail on.

WHY THIS EXISTS (2026-09-03). `.github/workflows/verify-lean4.yml` ran
`lake build L4Factoidal` and nothing else. A `sorry` fails that build,
because Lean emits it with an elaboration error. A DELIBERATE user
`axiom` does not: it compiles, and its appearance in a `#print axioms`
line is an informational message. `native_decide`, `unsafe`,
`@[implemented_by]` and a new `partial def` are all likewise invisible
to the gate. The tree was clean when this was written; the gate would
not have caught the next regression.

WHAT IT CHECKS

  1. `sorry`               -- must be 0
  2. user `axiom`          -- must be 0
  3. `native_decide`       -- must be 0
  4. `unsafe`              -- must be 0
  5. `@[implemented_by]`   -- must be 0
  6. `partial def`         -- must be <= the committed baseline
  7. `#print axioms` output in a build log, when one is given -- every
     reported axiom must be `propext`, `Classical.choice` or
     `Quot.sound`.

Check 7 is not optional decoration. A grep cannot see through an
import: a clean-looking theorem can rest on a lemma in another file
that carries the hatch, and only `#print axioms` reports that
(`third_party/skills/lean-agent-skills/lean-review/SKILL.md`). Checks
1 to 6 count DECLARATIONS in this tree; check 7 reports what the
proofs DEPEND on. Neither alone is the answer.

COMMENTS AND STRINGS ARE STRIPPED FIRST. The project writes "no
`sorry`, no `axiom`, no `native_decide`" as a header comment on nearly
every file. A naive grep saw 179 `sorry`, 280 `axiom` and 153
`native_decide` hits that were ALL prose, and 4 `unsafe` hits that
were all the string literal "unsafe manifest artifact key: ...". So
this tool removes nested `/- -/` block comments, `--` line comments
and string literals before it looks for anything.

THE `partial def` BASELINE is `tools/lean-partial-def-baseline.txt`.
A `partial def` compiles to an opaque constant with no equation
lemmas, so no theorem can be stated about the function it declares.
The owner has asked for the backlog to come down
(https://github.com/danbri/factoidal/issues/617), so the baseline is a
number a commit LOWERS deliberately and can never raise silently. When
the count drops, this tool says so and tells you to lower the file.

USAGE
    tools/lean-hygiene-audit.py [--build-log PATH]

Exit 0 clean, 1 on any violation. An empty walk is a hard error, not
an empty report (anti-pattern 30).
"""
import argparse, re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_ROOT = ROOT / "formal" / "lean4"
SCAN_DIRS = ["L4Factoidal", "Harness", "Wasm"]
BASELINE_FILE = ROOT / "tools" / "lean-partial-def-baseline.txt"

# The three axioms Lean's own standard library uses. Anything else in a
# `#print axioms` line is a user axiom, a `sorryAx`, or the
# `Lean.ofReduceBool` that `native_decide` adds.
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# A Lean character literal. `'` is also the prime in an identifier.
CHAR_LIT = re.compile(r"'(?:\\\\[^']{1,8}|[^'\\\\])'")


def strip_comments_and_strings(src: str) -> str:
    """Blank out nested `/- -/` comments, `--` comments and string
    literals, keeping newlines so line numbers survive."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
            continue
        if c == "'":
            # A Lean character literal: `'a'`, `'\\n'`, `'\"'`. A lone `'`
            # is a prime in an identifier (`cs'`) and is NOT a literal.
            # Getting this wrong is what made an early version treat
            # `escapeChar '\"'` as the start of a string and blank the
            # next 200 lines of real code (caught 2026-09-03).
            m = CHAR_LIT.match(src, i)
            if m:
                out.append(" " * (m.end() - i)); i = m.end(); continue
            out.append(c); i += 1; continue
        if c == '"':
            out.append(" "); i += 1
            while i < n:
                if src[i] == "\\" and i + 1 < n:
                    out.append("  "); i += 2; continue
                if src[i] == '"':
                    out.append(" "); i += 1; break
                out.append("\n" if src[i] == "\n" else " "); i += 1
            continue
        out.append(c); i += 1
    return "".join(out)


CHECKS = [
    ("sorry",            re.compile(r'\bsorry\b')),
    ("user axiom",       re.compile(r'^[ \t]*(?:@\[[^\]]*\][ \t]*)?'
                                    r'(?:private[ \t]+|protected[ \t]+|'
                                    r'noncomputable[ \t]+)*axiom\b', re.M)),
    ("native_decide",    re.compile(r'\bnative_decide\b')),
    ("unsafe",           re.compile(r'(?:^|[^A-Za-z0-9_.])unsafe[ \t]+'
                                    r'(?:def|theorem|lemma|abbrev|instance|'
                                    r'structure|inductive|opaque)\b', re.M)),
    ("@[implemented_by]", re.compile(r'@\[[^\]]*\bimplemented_by\b')),
]
PARTIAL_DEF = re.compile(r'\bpartial[ \t]+def\b')


def read_baseline() -> int:
    if not BASELINE_FILE.exists():
        sys.exit(f"lean-hygiene-audit: missing baseline {BASELINE_FILE}")
    for line in BASELINE_FILE.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            return int(line)
    sys.exit(f"lean-hygiene-audit: {BASELINE_FILE} carries no number")


def scan_build_log(path: pathlib.Path):
    """Every `#print axioms` line in a build log, and the axioms it names."""
    if not path.exists():
        sys.exit(f"lean-hygiene-audit: build log not found: {path}")
    text = path.read_text(errors="replace")
    seen, bad = 0, []
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        seen += 1
        names = [a.strip() for a in m.group(2).split(",") if a.strip()]
        extra = [a for a in names if a not in ALLOWED_AXIOMS]
        if extra:
            bad.append((m.group(1), extra))
    seen += len(re.findall(r"'[^']+' does not depend on any axioms", text))
    return seen, bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build-log", type=pathlib.Path, default=None,
                    help="a `lake build` log to read #print axioms output from")
    args = ap.parse_args()

    files = []
    for d in SCAN_DIRS:
        p = LEAN_ROOT / d
        if p.exists():
            files.extend(sorted(p.rglob("*.lean")))
    if not files:
        sys.exit("lean-hygiene-audit: no .lean files found under "
                 f"{LEAN_ROOT} -- broken checkout, nothing was measured")

    violations = {name: [] for name, _ in CHECKS}
    partials = []
    for f in files:
        code = strip_comments_and_strings(f.read_text(errors="replace"))
        lines = code.split("\n")
        for name, rx in CHECKS:
            for m in rx.finditer(code):
                ln = code.count("\n", 0, m.start()) + 1
                violations[name].append(f"{f.relative_to(ROOT)}:{ln}")
        for m in PARTIAL_DEF.finditer(code):
            ln = code.count("\n", 0, m.start()) + 1
            partials.append(f"{f.relative_to(ROOT)}:{ln}")
        del lines

    baseline = read_baseline()
    failed = False

    print(f"lean-hygiene-audit: {len(files)} .lean files scanned "
          f"(comments and string literals stripped first)")
    for name, _ in CHECKS:
        hits = violations[name]
        print(f"  {name:20s} {len(hits)} (must be 0)")
        if hits:
            failed = True
            for h in hits[:40]:
                print(f"      {h}")
            if len(hits) > 40:
                print(f"      ... and {len(hits) - 40} more")
    print(f"  {'partial def':20s} {len(partials)} "
          f"(baseline {baseline}, must not increase)")
    if len(partials) > baseline:
        failed = True
        print(f"      REGRESSION: {len(partials) - baseline} more than the "
              f"baseline in {BASELINE_FILE.relative_to(ROOT)}.")
        print("      A partial def compiles to an opaque constant, so no "
              "theorem can be stated about it.")
        print("      Give the definition a termination measure, or lower "
              "the count elsewhere. Raising the baseline needs the owner.")
    elif len(partials) < baseline:
        print(f"      IMPROVED by {baseline - len(partials)}. Lower "
              f"{BASELINE_FILE.relative_to(ROOT)} to {len(partials)} in this "
              "commit, so the gain cannot be given back silently.")

    if args.build_log is not None:
        seen, bad = scan_build_log(args.build_log)
        print(f"  {'#print axioms':20s} {seen} outputs read from "
              f"{args.build_log}")
        if seen == 0:
            failed = True
            print("      NOTHING READ. The build log carries no #print axioms "
                  "output, so this check measured nothing.")
        for decl, extra in bad:
            failed = True
            print(f"      {decl} depends on {', '.join(extra)}")
    else:
        print("  #print axioms        SKIPPED (no --build-log). A grep cannot "
              "see through an import; this run did not check dependencies.")

    if failed:
        print("\nlean-hygiene-audit: FAILED")
        return 1
    print("\nlean-hygiene-audit: clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
