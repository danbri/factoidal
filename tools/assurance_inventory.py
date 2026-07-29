#!/usr/bin/env python3
"""Machine-derived per-module assurance inventory for the F* corpus.

Issue #315 (sub-issue of the #313 claim-discipline epic). The review's
central finding is that three different claims blur together in our
docs:

  1. implemented in F*
  2. accepted by the F* verifier
  3. proved correct against a formalisation of the W3C specification

This tool derives, for every .fst/.fsti under formal/fstar/, the fields
that keep those three apart. ZERO rows are hand-written: every field is
computed from the F* source, the extracted OCaml, the build module list,
the per-suite manifests and the committed suite logs.

The load-bearing decision is what counts as "a theorem about the
shipping function" as opposed to "a lemma that happens to be stated".
The oracle used here is EXTRACTION, not naming:

  * A name that appears as a top-level VALUE binding in
    formal/fstar/ocaml-output/<Module>.ml is a SHIPPING FUNCTION. It is
    literally the code that runs. Extracted *types* do not count -- a
    lemma that mentions `rdf_graph` says nothing about an algorithm.
  * A top-level F* definition that does NOT survive into the extracted
    .ml, and whose return type is prop / Type0 / logical, is a
    DECLARATIVE RELATION -- a piece of formalised specification. F*
    erases exactly these.
  * A module that is in the build's module list and yet extracts to NO
    .ml at all is a PURE FORMALISATION MODULE: it is verified on every
    extract run and contributes no executable code.

Lemma classes, strongest first:

  * w3c_refinement       -- names a shipping function AND a declarative
                            relation defined in a *different* pure
                            formalisation module. The specification is
                            stated independently of both the code and
                            the proof; this is the pilot's discipline.
  * internal_refinement  -- names a shipping function and a declarative
                            relation, but the relation lives beside the
                            code it constrains (an invariant, not an
                            independent formalisation).
  * algorithm_correctness-- relates two or more shipping functions with
                            no declarative relation at all.
  * local_refinement     -- everything else stated in the module.
  * unclassified         -- the tool could not resolve the statement.

Classification is CONSERVATIVE by construction. Name resolution is
restricted to the host module plus the modules it opens or aliases; an
identifier that resolves ambiguously is dropped rather than counted,
and a module whose extracted .ml is missing is reported as
"unclassified (oracle unavailable)" rather than assumed either way. A
false "has a correctness theorem" is worse than an honest gap.

Usage:
    tools/assurance_inventory.py [--repo-root DIR]
                                 [--json PATH] [--markdown PATH]
                                 [--html PATH] [--eleventy] [--check]

--check exits non-zero if any active admission / lax region is found
(iron rule #10 proved rather than asserted).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import defaultdict

# --------------------------------------------------------------------------
# F* lexing: comments and strings
# --------------------------------------------------------------------------

# F* block comments NEST (CLAUDE.md syntax trap #1). A naive regex strip
# corrupts every count downstream, so this is a real scanner.


def strip_comments(src: str) -> tuple[str, str]:
    """Return (decommented, decommented_and_destringed).

    Comments are replaced by spaces (newlines preserved) so that line
    numbers survive. The second return value additionally blanks string
    literal contents, so identifier scanning never sees prose. The first
    keeps string contents, because #set-options flags live inside them.
    """
    out_keep: list[str] = []
    out_blank: list[str] = []
    i = 0
    n = len(src)
    depth = 0  # block-comment nesting depth
    in_line_comment = False
    in_string = False
    while i < n:
        ch = src[i]
        two = src[i : i + 2]
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out_keep.append(ch)
                out_blank.append(ch)
            else:
                out_keep.append(" ")
                out_blank.append(" ")
            i += 1
            continue
        if depth > 0:
            if two == "(*":
                depth += 1
                out_keep.append("  ")
                out_blank.append("  ")
                i += 2
                continue
            if two == "*)":
                depth -= 1
                out_keep.append("  ")
                out_blank.append("  ")
                i += 2
                continue
            out_keep.append("\n" if ch == "\n" else " ")
            out_blank.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_string:
            out_keep.append(ch)
            out_blank.append(" " if ch != "\n" else "\n")
            if ch == "\\" and i + 1 < n:
                out_keep.append(src[i + 1])
                out_blank.append(" " if src[i + 1] != "\n" else "\n")
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        # plain code
        if two == "(*":
            depth = 1
            out_keep.append("  ")
            out_blank.append("  ")
            i += 2
            continue
        if two == "//":
            in_line_comment = True
            out_keep.append("  ")
            out_blank.append("  ")
            i += 2
            continue
        if ch == '"':
            in_string = True
            out_keep.append(ch)
            out_blank.append(ch)
            i += 1
            continue
        # char literal: '"' or '\'' would otherwise open a bogus string
        if ch == "'" and i + 2 < n:
            prev = src[i - 1] if i > 0 else " "
            if not (prev.isalnum() or prev in "_'"):
                if src[i + 1] == "\\" and i + 3 < n and src[i + 3] == "'":
                    out_keep.append(src[i : i + 4])
                    out_blank.append("    ")
                    i += 4
                    continue
                if src[i + 2] == "'":
                    out_keep.append(src[i : i + 3])
                    out_blank.append("   ")
                    i += 3
                    continue
        out_keep.append(ch)
        out_blank.append(ch)
        i += 1
    return "".join(out_keep), "".join(out_blank)


IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")

FSTAR_KEYWORDS = {
    "let", "rec", "and", "in", "val", "type", "match", "with", "if", "then",
    "else", "fun", "begin", "end", "module", "open", "assume", "new", "of",
    "Lemma", "Tot", "GTot", "ST", "STATE", "Pure", "Ghost", "Div", "Type",
    "Type0", "Type1", "prop", "logical", "requires", "ensures", "decreases",
    "forall", "exists", "true", "false", "unit", "bool", "int", "nat",
    "string", "list", "option", "Some", "None", "Nil", "Cons", "returns",
    "squash", "eq2", "op_Equality", "assert", "admit", "magic", "when",
    "private", "noeq", "unopteq", "abstract", "irreducible", "unfold",
    "inline_for_extraction", "noextract", "total", "as", "attributes",
    "by", "calc", "friend", "include", "instance", "layered_effect",
    "effect", "sub_effect", "exception", "try", "function", "assume_val",
}


def idents_of(text: str) -> list[str]:
    return IDENT_RE.findall(text)


# --------------------------------------------------------------------------
# Top-level declaration scanning
# --------------------------------------------------------------------------

QUALIFIERS = (
    "private", "noextract", "inline_for_extraction", "irreducible", "unfold",
    "abstract", "total", "noeq", "unopteq", "new", "assume", "instance",
    "logic",
)

DECL_START_RE = re.compile(
    r"^(?P<quals>(?:(?:%s)\s+)*)"
    r"(?P<kw>val|let|and|type|effect|exception|new_effect|sub_effect)"
    r"(?:\s+rec)?\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*|\(\s*[^)]*\s*\))"
    % "|".join(QUALIFIERS)
)

ATTR_LINE_RE = re.compile(r"^\[@")


def scan_decls(text: str) -> list[dict]:
    """Split a decommented F* module into top-level declaration blocks."""
    lines = text.split("\n")
    starts: list[tuple[int, dict]] = []
    for idx, line in enumerate(lines):
        if not line or line[0].isspace():
            continue
        m = DECL_START_RE.match(line)
        if not m:
            continue
        starts.append(
            (
                idx,
                {
                    "kw": m.group("kw"),
                    "name": m.group("name").strip(),
                    "quals": m.group("quals").split(),
                    "line": idx + 1,
                },
            )
        )
    decls = []
    for pos, (idx, info) in enumerate(starts):
        end = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        info["block"] = "\n".join(lines[idx:end])
        decls.append(info)
    return decls


BALANCE_OPEN = "([{"
BALANCE_CLOSE = ")]}"


def signature_of(decl: dict) -> str:
    """Signature text: for `val`, the whole block; for `let`, up to the
    top-level `=` that begins the body."""
    block = decl["block"]
    if decl["kw"] in ("val", "type", "effect", "exception"):
        return block
    depth = 0
    i = 0
    n = len(block)
    while i < n:
        ch = block[i]
        if ch in BALANCE_OPEN:
            depth += 1
        elif ch in BALANCE_CLOSE:
            depth -= 1
        elif ch == "=" and depth == 0:
            prev = block[i - 1] if i else " "
            nxt = block[i + 1] if i + 1 < n else " "
            # skip ==, =>, <=, >=, :=, =!=, <==>, ^=, |=
            if prev in "<>=!:^|+-*/&" or nxt in "=>":
                i += 1
                continue
            return block[:i]
        i += 1
    return block


def strip_balanced(text: str) -> str:
    """Remove balanced (), [], {} groups -- used to expose the top-level
    return-type annotation of a signature."""
    out = []
    depth = 0
    for ch in text:
        if ch in BALANCE_OPEN:
            depth += 1
            continue
        if ch in BALANCE_CLOSE:
            depth = max(0, depth - 1)
            continue
        if depth == 0:
            out.append(ch)
    return "".join(out)


WORD = lambda w: re.compile(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(w))

LEMMA_RE = WORD("Lemma")
REQUIRES_RE = WORD("requires")
SQUASH_RE = WORD("squash")

PROP_RETURN_RE = re.compile(
    r":\s*(?:GTot\s+|Tot\s+)?(prop|Type0|logical)\s*$"
)


def return_type_head(sig: str) -> str:
    """Best-effort head of the declared return type, or '' when unknown."""
    flat = " ".join(strip_balanced(sig).split())
    # everything after the last top-level ':'
    if ":" not in flat:
        return ""
    tail = flat.rsplit(":", 1)[1].strip()
    toks = tail.split()
    if not toks:
        return ""
    if toks[0] in ("Tot", "GTot") and len(toks) > 1:
        return toks[1]
    return toks[0]


# --------------------------------------------------------------------------
# Repository inputs
# --------------------------------------------------------------------------


def module_name_of(path: str, decommented: str) -> str:
    m = re.search(r"^module\s+([A-Za-z_][A-Za-z0-9_'.]*)", decommented, re.M)
    if m:
        return m.group(1)
    base = os.path.basename(path)
    return base.rsplit(".fst", 1)[0].rsplit(".fsti", 1)[0]


def read_all_modules(build_sh: str) -> set[str]:
    """Parse the ALL_MODULES=( ... ) array out of build-ocaml.sh."""
    try:
        src = open(build_sh, encoding="utf-8", errors="replace").read()
    except OSError:
        return set()
    m = re.search(r"ALL_MODULES=\((.*?)^\s*\)", src, re.S | re.M)
    if not m:
        return set()
    return {
        tok[:-4]
        for tok in re.findall(r"[A-Za-z0-9_.]+\.fst\b", m.group(1))
    }


def read_expected_ml(build_sh: str) -> set[str]:
    """Every `<Module>.ml` the build script expects to compile and link.

    A module named here whose `.ml` is missing from ocaml-output/ means
    the extraction oracle is UNAVAILABLE for it (the extracted file is
    gitignored and was never force-added), which is different from a
    module that genuinely extracts to nothing.
    """
    try:
        src = open(build_sh, encoding="utf-8", errors="replace").read()
    except OSError:
        return set()
    return set(re.findall(r"\b([A-Za-z][A-Za-z0-9_]*)\.ml\b", src))


TOP_ML_VAL_RE = re.compile(
    r"^(?:let\s+rec\s+|let\s+|and\s+)([a-zA-Z_][A-Za-z0-9_']*)", re.M
)
TOP_ML_TYPE_RE = re.compile(r"^type\s+(?:'[a-z_]+\s+)*([a-zA-Z_][A-Za-z0-9_']*)",
                            re.M)


def extracted_symbols(ml_path: str) -> tuple[set[str], set[str]]:
    """Return (extracted value bindings, extracted type names).

    Only value bindings count as SHIPPING FUNCTIONS. An extracted type
    is data, not an algorithm: a lemma that mentions `rdf_graph` is not
    thereby a theorem about a shipping function.
    """
    try:
        src = open(ml_path, encoding="utf-8", errors="replace").read()
    except OSError:
        return set(), set()
    return set(TOP_ML_VAL_RE.findall(src)), set(TOP_ML_TYPE_RE.findall(src))


def ml_path_for(module: str, ocaml_dir: str) -> str:
    return os.path.join(ocaml_dir, module.replace(".", "_") + ".ml")


def name_variants(name: str) -> set[str]:
    """F* -> OCaml extraction mangles a few names."""
    v = {name, name.replace("'", "_"), name + "_"}
    if name.startswith("op_"):
        v.add(name)
    return v


# --------------------------------------------------------------------------
# Test-suite manifests (tolerant reader -- one manifest has an unquoted
# colon in its `name`, which pyyaml rejects, and CI should not need pyyaml)
# --------------------------------------------------------------------------


def read_suite_manifest(path: str) -> dict:
    out = {"name": None, "spec": None, "log_path": None, "runner_args": [],
            "trigger_paths": [], "foundational": False, "domain": None}
    section = None
    with open(path, encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            indent = len(line) - len(line.lstrip())
            stripped = line.strip()
            if indent == 0 and ":" in stripped:
                key = stripped.split(":", 1)[0].strip()
                val = stripped.split(":", 1)[1].strip()
                section = key
                if key in ("name", "spec", "log_path", "domain"):
                    out[key] = val.strip("\"'") or None
                elif key == "foundational":
                    out["foundational"] = val.strip().lower() == "true"
                continue
            if stripped.startswith("- "):
                item = stripped[2:].strip().strip("\"'")
                if section == "runner_args":
                    out["runner_args"].append(item)
                elif section in ("paths",):
                    out["trigger_paths"].append(item)
                continue
            if indent > 0 and stripped.rstrip(":") in ("paths", "excludes"):
                section = stripped.rstrip(":")
                continue
            if indent > 0 and stripped.endswith(":"):
                section = stripped[:-1].strip()
    return out


def read_foundational(path: str) -> list[str]:
    paths = []
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            for raw in fh:
                s = raw.strip()
                if s.startswith("- "):
                    paths.append(s[2:].strip())
    except OSError:
        pass
    return paths


SCORE_TOTAL_RE = re.compile(
    r"^\s*(?:TOTAL|Totals?)\s*:\s*(\d+)\s*pass\D+(\d+)\s*fail"
    r"(?:\D+(\d+)\s*skip)?", re.M | re.I)
SCORE_NAMED_RE = r"^\s*%s\s*:\s*(\d+)\s*pass\D+(\d+)\s*fail(?:\D+(\d+)\s*skip)?"
SUBSUITE_RE = r"^\s*%s\s+pass:(\d+)\s+fail:(\d+)(?:\s+skip:(\d+))?"


def _subsuite_names(man: dict) -> list[str]:
    """runner_args that name a SUB-SUITE, not a flag or a manifest path."""
    return [a for a in (man.get("runner_args") or [])
            if not a.startswith("-") and "/" not in a and "." not in a]


def _sum_subsuites(log: str, names: list[str]):
    hits = []
    for a in names:
        m = re.search(SUBSUITE_RE % re.escape(a), log, re.M)
        if not m:
            return None
        hits.append(m)
    if not hits:
        return None
    return (sum(int(h.group(1)) for h in hits),
            sum(int(h.group(2)) for h in hits),
            sum(int(h.group(3) or 0) for h in hits))


def suite_coverage(root: str, suite_key: str, man: dict, latest: dict) -> dict:
    """Resolve pass/fail/skip for a suite, recording HOW it was resolved.

    Deliberately refuses the whole-log TOTAL when the manifest names
    sub-suites the declared log does not contain: a runner invoked on a
    subset does not score the whole log, and publishing the bigger
    number would be a lie of exactly the kind this page exists to stop.
    """
    ocaml_dir = os.path.join(root, "formal", "fstar", "ocaml-output")
    log_path = man.get("log_path")
    names = _subsuite_names(man)
    log = None
    if log_path and os.path.exists(os.path.join(root, log_path)):
        log = open(os.path.join(root, log_path),
                   encoding="utf-8", errors="replace").read()

    if names:
        if log is not None:
            got = _sum_subsuites(log, names)
            if got:
                p, f, s = got
                return {"pass": p, "fail": f, "skip": s, "total": p + f + s,
                        "source": "suite-log:per-runner-arg:" + log_path}
        # the declared log_path does not carry this suite's sub-suite
        # lines. Look for them, by exact label, in the other committed
        # runner logs -- and say so, because that is a manifest bug.
        if os.path.isdir(ocaml_dir):
            for fn in sorted(os.listdir(ocaml_dir)):
                if not fn.endswith("_results.log"):
                    continue
                alt = os.path.join(ocaml_dir, fn)
                got = _sum_subsuites(
                    open(alt, encoding="utf-8", errors="replace").read(), names)
                if got:
                    p, f, s = got
                    return {
                        "pass": p, "fail": f, "skip": s, "total": p + f + s,
                        "source": "suite-log:per-runner-arg:"
                                  + os.path.relpath(alt, root),
                        "manifest_log_path_mismatch": log_path,
                    }
        return {"pass": None, "fail": None, "skip": None, "total": None,
                "source": "unresolved",
                "reason": "no committed log carries score lines for "
                          + ", ".join(names)}

    if log is not None:
        m = re.search(SCORE_NAMED_RE % re.escape(suite_key), log, re.M | re.I)
        if m:
            p, f, s = int(m.group(1)), int(m.group(2)), int(m.group(3) or 0)
            return {"pass": p, "fail": f, "skip": s, "total": p + f + s,
                    "source": "suite-log:named-line:" + log_path}
        m = SCORE_TOTAL_RE.search(log)
        if m:
            p, f, s = int(m.group(1)), int(m.group(2)), int(m.group(3) or 0)
            return {"pass": p, "fail": f, "skip": s, "total": p + f + s,
                    "source": "suite-log:TOTAL-line:" + log_path}

    key = suite_key.replace("-", "_")
    if key in latest:
        v = latest[key]
        return {"pass": v.get("pass"), "fail": v.get("fail"),
                "skip": v.get("skip", 0), "total": v.get("total"),
                "source": "docs/test-results/latest.json:" + key}
    return {"pass": None, "fail": None, "skip": None, "total": None,
            "source": "unresolved",
            "reason": ("declared log_path missing: " + str(log_path))
                      if log is None else
                      "no score line matched in " + str(log_path)}


def glob_to_re(pat: str) -> re.Pattern:
    out = []
    i = 0
    while i < len(pat):
        if pat.startswith("**/", i):
            out.append("(?:.*/)?")
            i += 3
        elif pat.startswith("**", i):
            out.append(".*")
            i += 2
        elif pat[i] == "*":
            out.append("[^/]*")
            i += 1
        elif pat[i] == "?":
            out.append("[^/]")
            i += 1
        else:
            out.append(re.escape(pat[i]))
            i += 1
    return re.compile("^" + "".join(out) + "$")


# --------------------------------------------------------------------------
# Main analysis
# --------------------------------------------------------------------------

# `magic` must be matched as an application `magic ()`: "magic" is also an
# ordinary identifier in this tree (Parquet/COTTAS magic-number constants),
# and counting those would manufacture 22 phantom admissions.
ADMISSION_PATTERNS = [
    ("admit", re.compile(r"(?<![A-Za-z0-9_'])admit\s*\(\s*\)")),
    ("admitP", re.compile(r"(?<![A-Za-z0-9_'])admitP(?![A-Za-z0-9_'])")),
    ("magic", re.compile(r"(?<![A-Za-z0-9_'])magic\s*\(\s*\)")),
    ("admit_smt_query", re.compile(
        r"(?<![A-Za-z0-9_'])admit_smt_query(?![A-Za-z0-9_'])")),
    ("assume-tactic", re.compile(
        r"(?<![A-Za-z0-9_'])Tactics\.admit_all(?![A-Za-z0-9_'])")),
]
ESCAPE_FLAGS = ["--lax", "--admit_smt_queries", "--admit_except",
                "--MLish_effect", "--warn_error"]
# --warn_error is benign; only the first three are escape hatches.
HARD_ESCAPE_FLAGS = ["--lax", "--admit_smt_queries", "--admit_except"]

PRAGMA_RE = re.compile(r"#(?:set|push)-options\s+\"([^\"]*)\"")


def analyse(root: str) -> dict:
    fstar_dir = os.path.join(root, "formal", "fstar")
    ocaml_dir = os.path.join(fstar_dir, "ocaml-output")
    build_sh = os.path.join(fstar_dir, "build-ocaml.sh")
    all_modules = read_all_modules(build_sh)
    expected_ml = read_expected_ml(build_sh)

    files = sorted(
        f for f in os.listdir(fstar_dir) if f.endswith((".fst", ".fsti"))
    )

    # ---- pass 1: lex every file, group by module -------------------------
    mods: dict[str, dict] = {}
    for fname in files:
        path = os.path.join(fstar_dir, fname)
        raw = open(path, encoding="utf-8", errors="replace").read()
        keep, blank = strip_comments(raw)
        mod = module_name_of(path, keep)
        m = mods.setdefault(mod, {
            "module": mod, "files": [], "loc": 0, "decls": [],
            "assume_vals": [], "assume_other": [], "admissions": [],
            "escape_pragmas": [], "opens": set(), "aliases": {},
        })
        m["files"].append(os.path.relpath(path, root))
        m["loc"] += raw.count("\n") + 1

        # imports (name-resolution scope)
        for om in re.finditer(r"^\s*open\s+([A-Za-z_][A-Za-z0-9_'.]*)", keep, re.M):
            m["opens"].add(om.group(1))
        for am in re.finditer(
            r"^\s*module\s+([A-Za-z_][A-Za-z0-9_']*)\s*=\s*([A-Za-z_][A-Za-z0-9_'.]*)",
            keep, re.M,
        ):
            m["aliases"][am.group(1)] = am.group(2)

        # assume val / assume type
        for am in re.finditer(
            r"^\s*assume\s+(?:new\s+)?(val|type)\s+([A-Za-z_][A-Za-z0-9_']*)",
            blank, re.M,
        ):
            line = blank[: am.start()].count("\n") + 1
            rec = {"name": am.group(2), "line": line,
                   "file": os.path.relpath(path, root)}
            if am.group(1) == "val":
                m["assume_vals"].append(rec)
            else:
                m["assume_other"].append(rec)

        # bare `assume (...)` / `assume P` (an axiom, not a realisation)
        for am in re.finditer(
            r"(?<![A-Za-z0-9_'])assume\s*\(", blank
        ):
            line = blank[: am.start()].count("\n") + 1
            m["assume_other"].append(
                {"name": "<assume-expression>", "line": line,
                 "file": os.path.relpath(path, root)})

        # admissions
        for tok, pat in ADMISSION_PATTERNS:
            for am in pat.finditer(blank):
                line = blank[: am.start()].count("\n") + 1
                m["admissions"].append(
                    {"token": tok, "line": line,
                     "file": os.path.relpath(path, root)})

        # escape-hatch pragmas (strings kept in `keep`)
        for pm in PRAGMA_RE.finditer(keep):
            flags = pm.group(1)
            for flag in HARD_ESCAPE_FLAGS:
                if flag in flags:
                    line = keep[: pm.start()].count("\n") + 1
                    m["escape_pragmas"].append(
                        {"flag": flag, "options": flags, "line": line,
                         "file": os.path.relpath(path, root)})

        for d in scan_decls(blank):
            d["file"] = os.path.relpath(path, root)
            d["interface"] = fname.endswith(".fsti")
            m["decls"].append(d)

    # ---- pass 2: extraction oracle ---------------------------------------
    for mod, m in mods.items():
        mlp = ml_path_for(mod, ocaml_dir)
        vals, types = extracted_symbols(mlp)
        m["extracted_symbols"] = vals
        m["extracted_types"] = types
        m["ml_path"] = os.path.relpath(mlp, root) if os.path.exists(mlp) else None
        m["in_build_list"] = mod in all_modules
        if m["ml_path"]:
            m["extraction"] = "extracted"
            m["oracle_available"] = True
        elif mod.replace(".", "_") in expected_ml:
            # the build links this module's .ml, so it DOES produce code;
            # the file is just not committed (formal/fstar/.gitignore
            # ignores *.ml and this one was never force-added).
            m["extraction"] = "extracted-ml-not-committed"
            m["oracle_available"] = False
        elif m["in_build_list"]:
            m["extraction"] = "fully-erased"
            m["oracle_available"] = True
        else:
            m["extraction"] = "not-in-build-list"
            m["oracle_available"] = False

    # ---- pass 3: classify declarations -----------------------------------
    # global symbol tables, keyed by name
    shipping_by_name: dict[str, set[str]] = defaultdict(set)
    specrel_by_name: dict[str, set[str]] = defaultdict(set)

    for mod, m in mods.items():
        seen = set()
        for d in m["decls"]:
            sig = signature_of(d)
            d["sig"] = sig
            d["is_lemma"] = bool(LEMMA_RE.search(sig) or SQUASH_RE.search(sig))
            d["has_requires"] = bool(REQUIRES_RE.search(sig))
            d["ret"] = return_type_head(sig)
            name = d["name"]
            if name.startswith("("):
                d["kind"] = "operator"
                continue
            extracted = bool(name_variants(name) & m["extracted_symbols"])
            extracted_ty = bool(name_variants(name) & m["extracted_types"])
            d["extracted"] = extracted or extracted_ty
            if d["is_lemma"]:
                d["kind"] = "lemma"
            elif extracted_ty and not extracted:
                d["kind"] = "type"
            elif extracted:
                d["kind"] = "shipping"
                if name not in seen:
                    shipping_by_name[name].add(mod)
            elif d["ret"] in ("prop", "Type0", "logical"):
                d["kind"] = "declarative-relation"
                specrel_by_name[name].add(mod)
            elif d["kw"] == "type":
                d["kind"] = "type"
            elif not m["oracle_available"]:
                # no extracted .ml to compare against: refuse to guess
                d["kind"] = "unclassified-definition"
            else:
                d["kind"] = "erased-definition"
            seen.add(name)

    # A PURE FORMALISATION MODULE contributes no executable code at all:
    # it is in the build list (so it really is verified on every extract
    # run) yet extracts to nothing, because everything it defines is
    # `prop` / `Type0` / a Lemma. Those are the modules that hold a
    # formalisation of a specification rather than an implementation.
    # A declarative relation that lives NEXT TO the code it constrains is
    # an internal invariant, not an independent formalisation -- the
    # pilot's discipline is that the spec is stated separately from the
    # implementation and from the proof.
    pure_formalisation = {
        mod for mod, m in mods.items()
        if m["extraction"] == "fully-erased"
        and any(d.get("kind") == "declarative-relation" for d in m["decls"])
    }

    # ---- pass 4: classify lemmas ------------------------------------------
    theorems: list[dict] = []
    for mod, m in mods.items():
        scope = {mod} | m["opens"] | set(m["aliases"].values())
        # merge val/let pairs: a `val f : Lemma ...` carries the statement
        by_name: dict[str, list[dict]] = defaultdict(list)
        for d in m["decls"]:
            by_name[d["name"]].append(d)
        handled = set()
        for d in m["decls"]:
            if d.get("kind") != "lemma":
                continue
            key = (d["name"], d["file"] != d["file"])
            group = by_name[d["name"]]
            vals = [g for g in group if g["kw"] == "val" and g.get("is_lemma")]
            stmt_decl = vals[0] if vals else d
            if (mod, d["name"]) in handled:
                continue
            handled.add((mod, d["name"]))
            stmt = stmt_decl["sig"]
            ship_hits: dict[str, set[str]] = defaultdict(set)
            spec_hits: dict[str, set[str]] = defaultdict(set)
            ambiguous = []
            for ident in idents_of(stmt):
                parts = ident.split(".")
                base = parts[-1]
                if base in FSTAR_KEYWORDS or base == d["name"]:
                    continue
                qual = None
                if len(parts) > 1:
                    prefix = ".".join(parts[:-1])
                    qual = m["aliases"].get(prefix, prefix)
                cand_scope = {qual} if qual else scope
                sm = shipping_by_name.get(base, set()) & cand_scope
                pm = specrel_by_name.get(base, set()) & cand_scope
                if len(sm) > 1:
                    ambiguous.append(base)
                    continue
                for x in sm:
                    ship_hits[x].add(base)
                if len(pm) > 1:
                    ambiguous.append(base)
                    continue
                for x in pm:
                    spec_hits[x].add(base)
            distinct_ship = {n for names in ship_hits.values() for n in names}
            # A declarative relation counts as an INDEPENDENT formalisation
            # only when it is defined in a pure-formalisation module other
            # than the one hosting the proof.
            independent_spec = {
                sm: names for sm, names in spec_hits.items()
                if sm in pure_formalisation and sm != mod
            }
            record = {
                "name": d["name"],
                "host_module": mod,
                "file": d["file"],
                "line": stmt_decl["line"],
                "unconditional": not stmt_decl["has_requires"],
                "shipping_functions_named": sorted(distinct_ship),
                "shipping_modules": sorted(ship_hits.keys()),
                "declarative_relations_named": sorted(
                    {n for names in spec_hits.values() for n in names}),
                "declarative_modules": sorted(spec_hits.keys()),
                "independent_formalisation_modules": sorted(independent_spec),
                "ambiguous_identifiers": sorted(set(ambiguous)),
            }
            if independent_spec and ship_hits:
                record["class"] = "w3c_refinement"
            elif spec_hits and ship_hits:
                record["class"] = "internal_refinement"
            elif len(distinct_ship) >= 2:
                record["class"] = "algorithm_correctness"
            elif distinct_ship or spec_hits:
                record["class"] = "local_refinement"
            elif ambiguous:
                record["class"] = "unclassified"
            else:
                record["class"] = "local_refinement"
            theorems.append(record)

    # ---- pass 5: test suites ----------------------------------------------
    suites_dir = os.path.join(root, ".github", "test-suites")
    latest = {}
    lj = os.path.join(root, "docs", "test-results", "latest.json")
    if os.path.exists(lj):
        try:
            latest = json.load(open(lj)).get("totals", {})
        except (OSError, ValueError):
            latest = {}
    foundational = read_foundational(os.path.join(suites_dir, "_foundational.yaml"))
    suites = {}
    if os.path.isdir(suites_dir):
        for fn in sorted(os.listdir(suites_dir)):
            if not fn.endswith(".yaml") or fn.startswith("_"):
                continue
            key = fn[:-5]
            man = read_suite_manifest(os.path.join(suites_dir, fn))
            man["key"] = key
            man["coverage"] = suite_coverage(root, key, man, latest)
            man["path_res"] = [glob_to_re(p) for p in man["trigger_paths"]]
            suites[key] = man

    found_res = [glob_to_re(p) for p in foundational]
    for mod, m in mods.items():
        hit = []
        rel_files = m["files"]
        is_foundational = any(
            r.match(f) for f in rel_files for r in found_res)
        for key, man in suites.items():
            direct = any(r.match(f) for f in rel_files for r in man["path_res"])
            via_found = is_foundational or (
                man["foundational"] and is_foundational)
            if direct or is_foundational:
                # coverage lives once in the top-level `suites` catalog;
                # repeating it per module inflates the JSON ~8x
                hit.append({
                    "suite": key,
                    "how": "direct-trigger" if direct else "foundational-path",
                })
        m["suites"] = hit
        m["foundational"] = is_foundational

    # ---- pass 6: per-module assurance rollup -------------------------------
    by_subject: dict[str, list[dict]] = defaultdict(list)
    for t in theorems:
        if t["class"] in ("w3c_refinement", "internal_refinement",
                          "algorithm_correctness"):
            for sm in t["shipping_modules"]:
                by_subject[sm].append(t)

    rows = []
    for mod in sorted(mods):
        m = mods[mod]
        local_lemmas = [t for t in theorems
                        if t["host_module"] == mod
                        and t["class"] in ("local_refinement", "unclassified")]
        about = by_subject.get(mod, [])
        w3c = [t for t in about if t["class"] == "w3c_refinement"]
        internal = [t for t in about if t["class"] == "internal_refinement"]
        alg = [t for t in about if t["class"] == "algorithm_correctness"]
        lemmas_here = [t for t in theorems if t["host_module"] == mod]
        n_ship = sum(1 for d in m["decls"] if d.get("kind") == "shipping")
        n_spec = sum(1 for d in m["decls"]
                     if d.get("kind") == "declarative-relation")
        n_unclassified = sum(1 for d in m["decls"]
                             if d.get("kind") == "unclassified-definition")
        merely_tot = (n_ship > 0 and not lemmas_here and not about)
        hosts_theorems = [t for t in theorems
                          if t["host_module"] == mod
                          and t["class"] in ("w3c_refinement",
                                             "internal_refinement",
                                             "algorithm_correctness")]
        if not m["oracle_available"]:
            tier = "unclassified"
        elif w3c:
            tier = "w3c-refinement"
        elif internal:
            tier = "internal-refinement"
        elif alg:
            tier = "algorithm-correctness"
        elif mod in pure_formalisation or (n_spec > 0 and hosts_theorems):
            tier = "specification-and-proof"
        elif lemmas_here:
            tier = "local-lemmas-only"
        elif merely_tot:
            tier = "merely-tot"
        elif n_spec > 0:
            tier = "specification-only"
        else:
            tier = "unclassified"
        rows.append({
            "module": mod,
            "files": m["files"],
            "loc": m["loc"],
            "provenance": "fstar-authored",
            "provenance_basis": (
                "file lives under formal/fstar/ and is not under any vendored "
                "third-party directory"),
            "extraction": m["extraction"],
            "extraction_oracle_available": m["oracle_available"],
            "extracted_ml": m["ml_path"],
            "in_build_module_list": m["in_build_list"],
            "foundational_path": m["foundational"],
            "shipping_function_count": n_ship,
            "declarative_relation_count": n_spec,
            "unclassified_definition_count": n_unclassified,
            "assume_val_active": len(m["assume_vals"]),
            "assume_val_names": [a["name"] for a in m["assume_vals"]],
            "assume_other_active": len(m["assume_other"]),
            "admissions_active": len(m["admissions"]),
            "admission_sites": m["admissions"],
            "lax_or_admit_pragmas": m["escape_pragmas"],
            "merely_tot": merely_tot,
            "local_refinement_lemma_count": len(local_lemmas),
            "local_refinement_lemma_names": [t["name"] for t in local_lemmas],
            "algorithm_correctness_theorems": [
                {"name": t["name"], "proved_in": t["host_module"],
                 "file": t["file"], "line": t["line"],
                 "unconditional": t["unconditional"],
                 "names_shipping_functions": t["shipping_functions_named"]}
                for t in alg],
            "internal_refinement_theorems": [
                {"name": t["name"], "proved_in": t["host_module"],
                 "file": t["file"], "line": t["line"],
                 "unconditional": t["unconditional"],
                 "names_shipping_functions": t["shipping_functions_named"],
                 "names_declarative_relations": t["declarative_relations_named"],
                 "declarative_relations_from": t["declarative_modules"]}
                for t in internal],
            "w3c_refinement_theorems": [
                {"name": t["name"], "proved_in": t["host_module"],
                 "file": t["file"], "line": t["line"],
                 "unconditional": t["unconditional"],
                 "names_shipping_functions": t["shipping_functions_named"],
                 "names_declarative_relations": t["declarative_relations_named"]}
                for t in w3c],
            "assurance_tier": tier,
            "suites": m["suites"],
        })

    tiers = defaultdict(int)
    for r in rows:
        tiers[r["assurance_tier"]] += 1

    return {
        "generated_by": "tools/assurance_inventory.py",
        "issue": "https://github.com/danbri/factoidal/issues/315",
        "suites": {
            key: {"name": man["name"], "spec": man["spec"],
                  "log_path": man["log_path"], "domain": man["domain"],
                  "coverage": man["coverage"]}
            for key, man in sorted(suites.items())
        },
        "modules": rows,
        "theorems": theorems,
        "totals": {
            "modules": len(rows),
            "files": sum(len(r["files"]) for r in rows),
            "assume_val_active": sum(r["assume_val_active"] for r in rows),
            "assume_other_active": sum(r["assume_other_active"] for r in rows),
            "admissions_active": sum(r["admissions_active"] for r in rows),
            "lax_or_admit_pragmas": sum(
                len(r["lax_or_admit_pragmas"]) for r in rows),
            "modules_with_w3c_refinement_theorem": sum(
                1 for r in rows if r["w3c_refinement_theorems"]),
            "modules_with_algorithm_correctness_theorem": sum(
                1 for r in rows if r["algorithm_correctness_theorems"]),
            "modules_with_internal_refinement_theorem": sum(
                1 for r in rows if r["internal_refinement_theorems"]),
            "modules_merely_tot": sum(1 for r in rows if r["merely_tot"]),
            "w3c_refinement_theorem_count": sum(
                1 for t in theorems if t["class"] == "w3c_refinement"),
            "internal_refinement_theorem_count": sum(
                1 for t in theorems if t["class"] == "internal_refinement"),
            "algorithm_correctness_theorem_count": sum(
                1 for t in theorems if t["class"] == "algorithm_correctness"),
            "unclassified_lemma_count": sum(
                1 for t in theorems if t["class"] == "unclassified"),
            "pure_formalisation_modules": sorted(pure_formalisation),
            "lemma_count": len(theorems),
            "tiers": dict(sorted(tiers.items())),
        },
    }


# --------------------------------------------------------------------------
# Rendering
# --------------------------------------------------------------------------

TIER_LABEL = {
    "w3c-refinement": "W3C-refinement theorem",
    "internal-refinement": "internal-refinement theorem",
    "algorithm-correctness": "algorithm-correctness theorem",
    "specification-and-proof": "specification / proof module",
    "local-lemmas-only": "local lemmas only",
    "merely-tot": "merely Tot",
    "specification-only": "specification only (erased)",
    "unclassified": "unclassified (oracle unavailable)",
}

TIER_ORDER = ["w3c-refinement", "internal-refinement", "algorithm-correctness",
              "specification-and-proof", "local-lemmas-only", "merely-tot",
              "specification-only", "unclassified"]


def render_markdown(data: dict, commit: str, front_matter: bool = False) -> str:
    t = data["totals"]
    L = []
    if front_matter:
        L.append("---")
        L.append("title: Per-module assurance inventory")
        L.append("layout: base.njk")
        L.append("---")
        L.append("")
    L.append("# Per-module assurance inventory")
    L.append("")
    L.append("Generated by `tools/assurance-inventory.sh`. Every row is derived "
             "from the F\\* source, the extracted OCaml, "
             "`formal/fstar/build-ocaml.sh`, `.github/test-suites/*.yaml` and "
             "the committed suite logs. No row on this page is hand-written, "
             "and nothing here can drift out of step with the tree without the "
             "regenerator noticing.")
    L.append("")
    L.append("Tree: `%s`. Modules analysed: %d, from %d `.fst`/`.fsti` files."
             % (commit, t["modules"], t["files"]))
    L.append("")
    if front_matter:
        # Eleventy's `url` filter applies the Pages path prefix; a bare
        # relative link from /web/conformance/<page>/ would resolve to
        # /web/test-results/, which does not exist.
        L.append("Machine-readable copy: "
                 "[assurance-inventory.json]"
                 "({{ '/test-results/assurance-inventory.json' | url }})"
                 " &middot; scrollable full table: "
                 "[assurance-inventory.html]"
                 "({{ '/test-results/assurance-inventory.html' | url }})")
    else:
        L.append("Machine-readable copy: "
                 "`docs/test-results/assurance-inventory.json` &middot; "
                 "scrollable full table: "
                 "`docs/test-results/assurance-inventory.html`")
    L.append("")
    L.append("## Why this page exists")
    L.append("")
    L.append("Three materially different claims are easy to blur together:")
    L.append("")
    L.append("1. **implemented in F\\*** — the module exists and extracts.")
    L.append("2. **accepted by the verifier** — F\\* checked whatever the "
             "module states, which for most modules is totality, termination "
             "and local refinements.")
    L.append("3. **proved correct against a formalisation of the spec** — a "
             "theorem ties the shipping function to a declarative relation "
             "stated independently of it.")
    L.append("")
    L.append("A module with nothing in the last two columns of the full "
             "inventory below has no correctness proof, whatever the prose "
             "around it says.")
    L.append("")
    L.append("## How the classifier decides")
    L.append("")
    L.append("The oracle is **extraction**, not naming.")
    L.append("")
    L.append("- A **shipping function** is a name that appears as a top-level "
             "value binding in `formal/fstar/ocaml-output/<Module>.ml`. It is "
             "the code that runs. Extracted *types* do not count: a lemma "
             "mentioning `rdf_graph` says nothing about an algorithm.")
    L.append("- A **declarative relation** is a top-level definition F\\* "
             "erases (absent from the extracted `.ml`) whose return type is "
             "`prop`, `Type0` or `logical`. That is formalised specification, "
             "not code.")
    L.append("- A **pure formalisation module** is in the build module list "
             "and yet extracts to no `.ml` at all — verified on every extract "
             "run, contributing zero executable code.")
    L.append("")
    L.append("| Lemma class | Requires |")
    L.append("|---|---|")
    L.append("| **W3C-refinement theorem** | names a shipping function **and** "
             "a declarative relation from a *different* pure formalisation "
             "module — the specification is stated independently of both the "
             "code and the proof |")
    L.append("| **internal-refinement theorem** | names a shipping function "
             "and a declarative relation, but the relation lives beside the "
             "code it constrains (an invariant, not an independent "
             "formalisation) |")
    L.append("| **algorithm-correctness theorem** | relates two or more "
             "shipping functions, with no declarative relation |")
    L.append("| **local refinement lemma** | everything else stated in the "
             "module |")
    L.append("| **merely `Tot`** | the module has shipping functions and no "
             "lemma anywhere in the corpus mentions them |")
    L.append("")
    L.append("Name resolution is limited to the host module plus the modules "
             "it `open`s or aliases; an ambiguous identifier is dropped rather "
             "than counted, and a module whose extracted `.ml` is missing is "
             "reported as unclassified rather than assumed either way. The "
             "classifier therefore fails **downward** — a module can be "
             "under-credited here, never over-credited.")
    L.append("")
    L.append("Pure formalisation modules in this tree: %s."
             % (", ".join("`%s`" % m
                          for m in t["pure_formalisation_modules"]) or "none"))
    L.append("")
    L.append("## Headline")
    L.append("")
    L.append("| Bucket | Modules |")
    L.append("|---|---|")
    for tier in TIER_ORDER:
        L.append("| %s | %d |" % (TIER_LABEL[tier], t["tiers"].get(tier, 0)))
    L.append("")
    L.append("Theorem counts across the whole corpus: "
             "%d W3C-refinement, %d internal-refinement and "
             "%d algorithm-correctness theorems, out of %d lemmas in total "
             "(%d lemmas the tool could not classify)."
             % (t["w3c_refinement_theorem_count"],
                t["internal_refinement_theorem_count"],
                t["algorithm_correctness_theorem_count"],
                t["lemma_count"], t["unclassified_lemma_count"]))
    L.append("")
    L.append("## Iron rule #10, proved rather than asserted")
    L.append("")
    L.append("| Measure | Count |")
    L.append("|---|---:|")
    L.append("| `--lax` / `--admit_smt_queries` / `--admit_except` pragma "
             "regions | %d |" % t["lax_or_admit_pragmas"])
    L.append("| Active admissions (`admit ()`, `admitP`, `magic ()`, "
             "`admit_smt_query`), outside comments | %d |"
             % t["admissions_active"])
    L.append("| Active `assume val` declarations | %d |"
             % t["assume_val_active"])
    L.append("")
    L.append("The `assume val` count is not a defect count: under iron rule #3 "
             "each is either an acknowledged gap with an open issue or an "
             "allowed realisation (pure I/O, a host-engine call-out, or a "
             "vendored crypto primitive).")
    L.append("")
    if t["admissions_active"]:
        L.append("Every active admission, by file and line:")
        L.append("")
        L.append("| File | Line | Token |")
        L.append("|---|---:|---|")
        for r in data["modules"]:
            for s in r["admission_sites"]:
                L.append("| `%s` | %d | `%s` |"
                         % (s["file"], s["line"], s["token"]))
        L.append("")
    L.append("## Modules with a W3C-refinement theorem")
    L.append("")
    w3c_rows = [r for r in data["modules"] if r["w3c_refinement_theorems"]]
    if not w3c_rows:
        L.append("None.")
    else:
        L.append("| Module | Theorem | Proved in | Shipping function | "
                 "Declarative relation | Unconditional |")
        L.append("|---|---|---|---|---|---|")
        for r in w3c_rows:
            for th in r["w3c_refinement_theorems"]:
                L.append("| `%s` | `%s` | `%s` | %s | %s | %s |" % (
                    r["module"], th["name"], th["proved_in"],
                    ", ".join("`%s`" % s for s in th["names_shipping_functions"])
                    or "—",
                    ", ".join("`%s`" % s
                              for s in th["names_declarative_relations"]) or "—",
                    "yes" if th["unconditional"] else "no (has `requires`)"))
    L.append("")
    L.append("## Modules with an internal-refinement theorem")
    L.append("")
    int_rows = [r for r in data["modules"] if r["internal_refinement_theorems"]]
    if not int_rows:
        L.append("None.")
    else:
        L.append("| Module | Theorem | Proved in | Shipping functions | "
                 "Declarative relation | Unconditional |")
        L.append("|---|---|---|---|---|---|")
        for r in int_rows:
            for th in r["internal_refinement_theorems"]:
                L.append("| `%s` | `%s` | `%s` | %s | %s | %s |" % (
                    r["module"], th["name"], th["proved_in"],
                    ", ".join("`%s`" % s
                              for s in th["names_shipping_functions"]) or "—",
                    ", ".join("`%s`" % s
                              for s in th["names_declarative_relations"]) or "—",
                    "yes" if th["unconditional"] else "no (has `requires`)"))
    L.append("")
    L.append("## Modules with an algorithm-correctness theorem")
    L.append("")
    alg_rows = [r for r in data["modules"] if r["algorithm_correctness_theorems"]]
    if not alg_rows:
        L.append("None.")
    else:
        L.append("| Module | Theorems | Unconditional | Example |")
        L.append("|---|---:|---:|---|")
        for r in alg_rows:
            ths = r["algorithm_correctness_theorems"]
            uncond = [x for x in ths if x["unconditional"]]
            example = (uncond or ths)[0]
            L.append("| `%s` | %d | %d | `%s` (%s) |" % (
                r["module"], len(ths), len(uncond), example["name"],
                ", ".join("`%s`" % s
                          for s in example["names_shipping_functions"][:3])))
    L.append("")
    L.append("## Full inventory")
    L.append("")
    L.append("`assume val` = active assumed declarations. `Adm` = active "
             "admissions plus `--lax`/`--admit_smt_queries` regions. "
             "`Local` = local refinement lemmas. `Alg` / `Int` / `W3C` = "
             "algorithm-correctness, internal-refinement and W3C-refinement "
             "theorems about this module's shipping functions.")
    L.append("")
    L.append("| Module | Tier | Extraction | assume val | Adm | Local | Alg | "
             "Int | W3C | Suites |")
    L.append("|---|---|---|---:|---:|---:|---:|---:|---:|---|")
    for r in data["modules"]:
        suites = ", ".join(s["suite"] for s in r["suites"][:4])
        if len(r["suites"]) > 4:
            suites += ", +%d more" % (len(r["suites"]) - 4)
        L.append("| `%s` | %s | %s | %d | %d | %d | %d | %d | %d | %s |" % (
            r["module"], TIER_LABEL[r["assurance_tier"]], r["extraction"],
            r["assume_val_active"],
            r["admissions_active"] + len(r["lax_or_admit_pragmas"]),
            r["local_refinement_lemma_count"],
            len(r["algorithm_correctness_theorems"]),
            len(r["internal_refinement_theorems"]),
            len(r["w3c_refinement_theorems"]),
            suites or "—"))
    L.append("")
    L.append("## Official suites and their exact coverage")
    L.append("")
    L.append("Every suite the per-suite manifests define, with the score read "
             "back from the committed runner log or, failing that, from "
             "`docs/test-results/latest.json`. `Source` records where each "
             "number came from, so a disagreement is traceable rather than "
             "arguable. A suite reading no numbers has no committed log line "
             "the tool can match &mdash; that is a gap in the measurement "
             "chain, reported rather than filled in.")
    L.append("")
    L.append("| Suite | Pass | Fail | Skip | Total | Source |")
    L.append("|---|---:|---:|---:|---:|---|")
    for key, s in data["suites"].items():
        c = s["coverage"]
        def _n(x):
            return "—" if x is None else str(x)
        src = c["source"]
        if c.get("manifest_log_path_mismatch"):
            src += " (manifest `log_path` points at `%s`, which does not "\
                   "carry this suite's score lines)" \
                   % c["manifest_log_path_mismatch"]
        elif c.get("reason"):
            src += " — " + c["reason"]
        L.append("| `%s` | %s | %s | %s | %s | %s |" % (
            key, _n(c["pass"]), _n(c["fail"]), _n(c["skip"]), _n(c["total"]),
            src))
    L.append("")
    L.append("Filed as [issue #315](https://github.com/danbri/factoidal/issues/315), "
             "sub-issue of the claim-discipline epic "
             "[#313](https://github.com/danbri/factoidal/issues/313).")
    L.append("")
    return "\n".join(L)


HTML_HEAD = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Per-module assurance inventory &mdash; Factoidal</title>
<style>
:root { color-scheme: light dark; --fg:#111; --bg:#fff; --mut:#555;
        --line:#d7d7d7; --acc:#0b5; --warn:#b40; }
@media (prefers-color-scheme: dark) {
  :root { --fg:#e8e8e8; --bg:#131316; --mut:#a4a4a4; --line:#33343a; }
}
body { font: 15px/1.55 -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto,
       Helvetica, Arial, sans-serif; color:var(--fg); background:var(--bg);
       margin:0; padding:1.5rem; }
main { max-width: 78rem; margin: 0 auto; }
h1 { font-size: 1.7rem; margin:.2rem 0 .4rem; }
h2 { font-size: 1.2rem; margin-top:2rem; border-bottom:1px solid var(--line);
     padding-bottom:.3rem; }
code { font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
       font-size: .92em; }
p.lede { color: var(--mut); max-width: 52rem; }
.tablewrap { overflow-x:auto; border:1px solid var(--line); border-radius:6px; }
table { border-collapse: collapse; width:100%; font-size:.88rem; }
th, td { text-align:left; padding:.35rem .6rem; border-bottom:1px solid var(--line);
         white-space:nowrap; }
th { position:sticky; top:0; background:var(--bg); z-index:1; }
td.num { text-align:right; }
.zero { color: var(--acc); font-weight:600; }
.nonzero { color: var(--warn); font-weight:600; }
.tier { font-size:.8rem; padding:.1rem .4rem; border-radius:4px;
        border:1px solid var(--line); }
.t-w3c-refinement { background:#0b5; color:#fff; border-color:#0b5; }
.t-internal-refinement { background:#5a8; color:#fff; border-color:#5a8; }
.t-algorithm-correctness { background:#37c; color:#fff; border-color:#37c; }
.t-specification-and-proof { background:#849; color:#fff; border-color:#849; }
ul.legend li { margin:.25rem 0; }
.cards { display:flex; flex-wrap:wrap; gap:.6rem; margin:.8rem 0; }
.card { border:1px solid var(--line); border-radius:6px; padding:.5rem .9rem;
        min-width:9rem; }
.card b { display:block; font-size:1.5rem; }
.card span { color:var(--mut); font-size:.8rem; }
footer { color:var(--mut); font-size:.82rem; margin-top:2.5rem; }
</style></head><body><main>
"""


def esc(s) -> str:
    return (str(s).replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;"))


def render_html(data: dict, commit: str) -> str:
    t = data["totals"]
    o = [HTML_HEAD]
    o.append("<h1>Per-module assurance inventory</h1>")
    o.append('<p class="lede">Generated by <code>tools/assurance_inventory.py</code> '
             "from the F* source, the extracted OCaml, "
             "<code>formal/fstar/build-ocaml.sh</code>, "
             "<code>.github/test-suites/*.yaml</code> and the committed suite "
             "logs. No row on this page is hand-written. It exists to keep "
             "three different claims apart: <em>implemented in F*</em>, "
             "<em>accepted by the verifier</em>, and <em>proved correct "
             "against a formalisation of the specification</em>.</p>")
    o.append('<p class="lede">Tree: <code>%s</code> &middot; %d modules from '
             "%d <code>.fst</code>/<code>.fsti</code> files.</p>"
             % (esc(commit), t["modules"], t["files"]))

    o.append('<div class="cards">')
    for tier in TIER_ORDER:
        o.append('<div class="card"><b>%d</b><span>%s</span></div>'
                 % (t["tiers"].get(tier, 0), esc(TIER_LABEL[tier])))
    o.append("</div>")

    o.append("<h2>Iron rule #10, proved rather than asserted</h2>")
    o.append('<div class="cards">')
    for label, n, good_is_zero in (
        ("active admissions", t["admissions_active"], True),
        ("--lax / --admit_smt_queries regions", t["lax_or_admit_pragmas"], True),
        ("active assume val", t["assume_val_active"], False),
    ):
        cls = ("zero" if (n == 0 and good_is_zero)
               else ("nonzero" if good_is_zero else ""))
        o.append('<div class="card"><b class="%s">%d</b><span>%s</span></div>'
                 % (cls, n, esc(label)))
    o.append("</div>")
    o.append("<p class=\"lede\">The <code>assume val</code> count is not a "
             "defect count: under iron rule #3 each is either an acknowledged "
             "gap with an open issue or an allowed realisation (pure I/O, a "
             "host-engine call-out, or a vendored crypto primitive).</p>")

    o.append("<h2>How a module earns each bucket</h2>")
    o.append('<ul class="legend">')
    o.append("<li><b>Shipping function</b> &mdash; a name that appears as a "
             "top-level <em>value</em> binding in "
             "<code>ocaml-output/&lt;Module&gt;.ml</code>. Extraction, not "
             "naming, is the oracle. Extracted types do not count.</li>")
    o.append("<li><b>Declarative relation</b> &mdash; a top-level definition "
             "F* erases (absent from the extracted <code>.ml</code>) whose "
             "return type is <code>prop</code>, <code>Type0</code> or "
             "<code>logical</code>. That is formalised specification.</li>")
    o.append("<li><b>Pure formalisation module</b> &mdash; in the build module "
             "list, yet extracts to no <code>.ml</code> at all: verified on "
             "every extract run, contributing zero executable code.</li>")
    o.append("<li><b>W3C-refinement theorem</b> &mdash; names a shipping "
             "function <em>and</em> a declarative relation from a "
             "<em>different</em> pure formalisation module, so the "
             "specification is stated independently of both the code and the "
             "proof.</li>")
    o.append("<li><b>Internal-refinement theorem</b> &mdash; names a shipping "
             "function and a declarative relation, but the relation lives "
             "beside the code it constrains: an invariant, not an independent "
             "formalisation.</li>")
    o.append("<li><b>Algorithm-correctness theorem</b> &mdash; relates two or "
             "more shipping functions, with no declarative relation.</li>")
    o.append("<li><b>merely Tot</b> &mdash; the module has shipping functions "
             "and no lemma anywhere in the corpus mentions them.</li>")
    o.append("</ul>")
    o.append('<p class="lede">Name resolution is limited to the host module '
             "plus the modules it <code>open</code>s or aliases; an ambiguous "
             "identifier is dropped rather than counted. The classifier "
             "therefore fails downward &mdash; a module can be under-credited "
             "here, never over-credited.</p>")

    w3c_rows = [r for r in data["modules"] if r["w3c_refinement_theorems"]]
    o.append("<h2>Modules with a W3C-refinement theorem (%d)</h2>" % len(w3c_rows))
    if not w3c_rows:
        o.append("<p>None.</p>")
    else:
        o.append('<div class="tablewrap"><table><thead><tr>'
                 "<th>Module</th><th>Theorem</th><th>Proved in</th>"
                 "<th>Shipping function</th><th>Declarative relation</th>"
                 "<th>Unconditional</th></tr></thead><tbody>")
        for r in w3c_rows:
            for th in r["w3c_refinement_theorems"]:
                o.append("<tr><td><code>%s</code></td><td><code>%s</code></td>"
                         "<td><code>%s</code></td><td>%s</td><td>%s</td>"
                         "<td>%s</td></tr>" % (
                             esc(r["module"]), esc(th["name"]),
                             esc(th["proved_in"]),
                             ", ".join("<code>%s</code>" % esc(s)
                                       for s in th["names_shipping_functions"])
                             or "&mdash;",
                             ", ".join("<code>%s</code>" % esc(s)
                                       for s in th["names_declarative_relations"])
                             or "&mdash;",
                             "yes" if th["unconditional"]
                             else "no (has <code>requires</code>)"))
        o.append("</tbody></table></div>")

    int_rows = [r for r in data["modules"] if r["internal_refinement_theorems"]]
    o.append("<h2>Modules with an internal-refinement theorem (%d)</h2>"
             % len(int_rows))
    if not int_rows:
        o.append("<p>None.</p>")
    else:
        o.append('<div class="tablewrap"><table><thead><tr>'
                 "<th>Module</th><th>Theorem</th><th>Proved in</th>"
                 "<th>Shipping functions</th><th>Declarative relation</th>"
                 "<th>Unconditional</th></tr></thead><tbody>")
        for r in int_rows:
            for th in r["internal_refinement_theorems"]:
                o.append("<tr><td><code>%s</code></td><td><code>%s</code></td>"
                         "<td><code>%s</code></td><td>%s</td><td>%s</td>"
                         "<td>%s</td></tr>" % (
                             esc(r["module"]), esc(th["name"]),
                             esc(th["proved_in"]),
                             ", ".join("<code>%s</code>" % esc(s)
                                       for s in th["names_shipping_functions"])
                             or "&mdash;",
                             ", ".join("<code>%s</code>" % esc(s)
                                       for s in th["names_declarative_relations"])
                             or "&mdash;",
                             "yes" if th["unconditional"]
                             else "no (has <code>requires</code>)"))
        o.append("</tbody></table></div>")

    if t["admissions_active"]:
        o.append("<h2>Active admissions (%d)</h2>" % t["admissions_active"])
        o.append('<div class="tablewrap"><table><thead><tr><th>File</th>'
                 "<th>Line</th><th>Token</th></tr></thead><tbody>")
        for r in data["modules"]:
            for s in r["admission_sites"]:
                o.append("<tr><td><code>%s</code></td>"
                         '<td class="num">%d</td><td><code>%s</code></td></tr>'
                         % (esc(s["file"]), s["line"], esc(s["token"])))
        o.append("</tbody></table></div>")

    alg_rows = [r for r in data["modules"]
                if r["algorithm_correctness_theorems"]]
    o.append("<h2>Modules with an algorithm-correctness theorem (%d)</h2>"
             % len(alg_rows))
    if not alg_rows:
        o.append("<p>None.</p>")
    else:
        o.append('<div class="tablewrap"><table><thead><tr>'
                 "<th>Module</th><th>Theorem</th><th>Proved in</th>"
                 "<th>Shipping functions named</th><th>Unconditional</th>"
                 "</tr></thead><tbody>")
        for r in alg_rows:
            for th in r["algorithm_correctness_theorems"]:
                o.append("<tr><td><code>%s</code></td><td><code>%s</code></td>"
                         "<td><code>%s</code></td><td>%s</td><td>%s</td></tr>"
                         % (esc(r["module"]), esc(th["name"]),
                            esc(th["proved_in"]),
                            ", ".join("<code>%s</code>" % esc(s)
                                      for s in th["names_shipping_functions"])
                            or "&mdash;",
                            "yes" if th["unconditional"]
                            else "no (has <code>requires</code>)"))
        o.append("</tbody></table></div>")

    o.append("<h2>Full inventory (%d modules)</h2>" % t["modules"])
    o.append('<div class="tablewrap"><table><thead><tr>'
             "<th>Module</th><th>Tier</th><th>Extraction</th>"
             "<th>assume val</th><th>Admissions / lax</th>"
             "<th>Local lemmas</th><th>Alg. corr.</th><th>Internal ref.</th>"
             "<th>W3C ref.</th><th>Suites</th></tr></thead><tbody>")
    for r in data["modules"]:
        tier = r["assurance_tier"]
        adm = r["admissions_active"] + len(r["lax_or_admit_pragmas"])
        suites = ", ".join(s["suite"] for s in r["suites"][:4])
        if len(r["suites"]) > 4:
            suites += ", +%d" % (len(r["suites"]) - 4)
        o.append("<tr><td><code>%s</code></td>"
                 '<td><span class="tier t-%s">%s</span></td>'
                 "<td>%s</td>"
                 '<td class="num">%d</td>'
                 '<td class="num %s">%d</td>'
                 '<td class="num">%d</td><td class="num">%d</td>'
                 '<td class="num">%d</td><td class="num">%d</td>'
                 "<td>%s</td></tr>" % (
                     esc(r["module"]), esc(tier), esc(TIER_LABEL[tier]),
                     esc(r["extraction"]), r["assume_val_active"],
                     "zero" if adm == 0 else "nonzero", adm,
                     r["local_refinement_lemma_count"],
                     len(r["algorithm_correctness_theorems"]),
                     len(r["internal_refinement_theorems"]),
                     len(r["w3c_refinement_theorems"]),
                     esc(suites) or "&mdash;"))
    o.append("</tbody></table></div>")

    o.append("<h2>Official suites and their exact coverage</h2>")
    o.append('<p class="lede">Scores are read back from the committed runner '
             "logs, or from <code>docs/test-results/latest.json</code> when a "
             "log carries no matchable score line. <b>Source</b> records where "
             "each number came from. A suite with no numbers has a gap in its "
             "measurement chain, reported rather than filled in.</p>")
    o.append('<div class="tablewrap"><table><thead><tr><th>Suite</th>'
             "<th>Pass</th><th>Fail</th><th>Skip</th><th>Total</th>"
             "<th>Source</th></tr></thead><tbody>")
    for key, s in data["suites"].items():
        c = s["coverage"]
        cells = ["&mdash;" if c[k] is None else str(c[k])
                 for k in ("pass", "fail", "skip", "total")]
        src = c["source"]
        if c.get("manifest_log_path_mismatch"):
            src += " (manifest log_path points at %s, which does not carry " \
                   "this suite's score lines)" % c["manifest_log_path_mismatch"]
        elif c.get("reason"):
            src += " &mdash; " + c["reason"]
        o.append("<tr><td><code>%s</code></td>"
                 '<td class="num">%s</td><td class="num">%s</td>'
                 '<td class="num">%s</td><td class="num">%s</td>'
                 "<td>%s</td></tr>"
                 % (esc(key), cells[0], cells[1], cells[2], cells[3], src))
    o.append("</tbody></table></div>")

    o.append('<footer>Regenerate with <code>tools/assurance-inventory.sh</code>. '
             'Machine-readable form: <a href="assurance-inventory.json">'
             "assurance-inventory.json</a>. Filed as "
             '<a href="https://github.com/danbri/factoidal/issues/315">issue '
             "#315</a>, sub-issue of the claim-discipline epic "
             '<a href="https://github.com/danbri/factoidal/issues/313">#313'
             "</a>.</footer>")
    o.append("</main></body></html>")
    return "\n".join(o)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo-root", default=None)
    ap.add_argument("--json", default=None)
    ap.add_argument("--markdown", default=None)
    ap.add_argument("--html", default=None)
    ap.add_argument("--eleventy", action="store_true",
                    help="prepend Eleventy front matter to the markdown output")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if any active admission or lax region exists")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args()

    root = args.repo_root or os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))
    data = analyse(root)

    commit = "unknown"
    try:
        import subprocess
        commit = subprocess.check_output(
            ["git", "-C", root, "rev-parse", "--short", "HEAD"],
            text=True).strip()
    except Exception:
        pass
    data["commit"] = commit

    if args.json:
        os.makedirs(os.path.dirname(os.path.abspath(args.json)), exist_ok=True)
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(data, fh, indent=1, sort_keys=False)
            fh.write("\n")
    if args.markdown:
        os.makedirs(os.path.dirname(os.path.abspath(args.markdown)),
                    exist_ok=True)
        with open(args.markdown, "w", encoding="utf-8") as fh:
            fh.write(render_markdown(data, commit, args.eleventy) + "\n")
    if args.html:
        os.makedirs(os.path.dirname(os.path.abspath(args.html)), exist_ok=True)
        with open(args.html, "w", encoding="utf-8") as fh:
            fh.write(render_html(data, commit) + "\n")

    if args.summary or not (args.json or args.markdown or args.html):
        t = data["totals"]
        print("modules: %d (from %d files)" % (t["modules"], t["files"]))
        for tier in TIER_ORDER:
            print("  %-34s %d" % (TIER_LABEL[tier], t["tiers"].get(tier, 0)))
        print("theorems: %d W3C-refinement, %d algorithm-correctness, "
              "%d lemmas total" % (t["w3c_refinement_theorem_count"],
                                   t["algorithm_correctness_theorem_count"],
                                   t["lemma_count"]))
        print("active assume val: %d" % t["assume_val_active"])
        print("active admissions: %d" % t["admissions_active"])
        print("lax / admit_smt_queries pragma regions: %d"
              % t["lax_or_admit_pragmas"])

    if args.check:
        bad = (data["totals"]["admissions_active"]
               + data["totals"]["lax_or_admit_pragmas"])
        if bad:
            print("assurance-inventory: FAIL -- %d active admission/lax site(s)"
                  % bad, file=sys.stderr)
            for r in data["modules"]:
                for s in r["admission_sites"]:
                    print("  %s:%d %s" % (s["file"], s["line"], s["token"]),
                          file=sys.stderr)
                for s in r["lax_or_admit_pragmas"]:
                    print("  %s:%d %s" % (s["file"], s["line"], s["flag"]),
                          file=sys.stderr)
            return 1
        print("assurance-inventory: OK -- 0 active admissions, 0 lax regions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
