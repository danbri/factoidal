#!/usr/bin/env python3
"""Audit the Lean library for recursion that is not compiled to a loop.

METHOD (read-only, over compiled output, never over source shape)
================================================================
Lean 4 compiles a *direct tail* self-call into a jump: the emitted C function
opens with a `_start:` label and the tail call becomes `goto _start;`.  Any
self-call that survives as a real C call `f(...)` therefore consumes a C stack
frame per step.  This tool reads `formal/lean4/.lake/build/ir/**/*.c`, finds
every such surviving self-call and every mutual-recursion cycle, maps the
mangled C symbol back to its Lean declaration, and classifies what bounds the
recursion depth.

Classes
-------
  length    depth is proportional to the length of an input the caller
            controls (a List, String, ByteArray, Array, token stream)
  depth     depth is the nesting depth of an input tree (JSON, XML,
            an expression or algebra term)
  counter   depth is a Nat argument -- a fuel or a count.  A count READ FROM
            THE INPUT (a wire-format entry count) is an input-length
            recursion wearing a Nat; the report says which.
  bounded   recursion over a fixed structure, or over nothing the caller
            grows
  unknown   the Lean declaration could not be located or read

LIMITS OF THE METHOD (state these with any result)
--------------------------------------------------
  * Inlining and specialisation.  Lean specialises core combinators at our
    call sites (`..._at_..._spec__N`).  Those appear as separate functions and
    are attributed to the enclosing declaration; a combinator that is NOT
    specialised (it stays in Lean's own `libleanshared`) is invisible here.
  * Higher-order recursion.  A function that recurses by handing itself to a
    combinator shows only as a closure allocation.  Closure self-references
    are reported, but a cycle that runs through an unspecialised core
    combinator is not visible.
  * `List.foldr`, `List.map`, `List.flatMap` etc. carry `@[csimp]`
    tail-recursive replacements in Lean core, so a call to one of those is
    NOT by itself evidence of stack growth.  A call to a combinator without
    such a replacement is invisible to this tool.
  * Class assignment reads the Lean source signature textually.  It ranks
    suspects; it does not prove a bound.
  * The scan sees only what was compiled.  A module absent from
    `.lake/build/ir` is not audited -- run `lake build` first.
"""

import argparse, json, os, re, sys
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IR_DIR = os.path.join(REPO, "formal", "lean4", ".lake", "build", "ir")
LEAN_DIR = os.path.join(REPO, "formal", "lean4")

PKG_PREFIXES = ("lp_l4factoidal_", "l_")

# ---------------------------------------------------------------- C scanning

FUNC_DEF = re.compile(r"^(?:LEAN_EXPORT\s+|static\s+)*[A-Za-z_][A-Za-z0-9_ \*]*?\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
IDENT_CALL = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
CLOSURE_REF = re.compile(r"\(void\*\)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)")
CONTROL = {"if", "else", "while", "for", "switch", "return", "sizeof", "do"}


STRLIT = re.compile(r'"(?:\\\\.|[^"\\\\])*"' + r"|'(?:\\\\.|[^'\\\\])*'")


def scan_c_file(path):
    """Return (defs, calls, closures) for one emitted C file.

    Function bodies are delimited by BRACE DEPTH, not by a `}` in column 0:
    Lean emits every nested block's braces in column 0 too, and a
    column-0 terminator silently truncates each body at its first inner
    block.  That bug made the first run of this tool report 24 recursions
    where there are hundreds.
    """
    defs, calls, closures = {}, defaultdict(set), defaultdict(set)
    cur = None
    depth = 0
    body = []
    with open(path, "r", errors="replace") as fh:
        lines = fh.readlines()

    def finish(name, body):
        d = defs[name]
        for b in body:
            if "goto _start;" in b:
                d["tail"] += 1
            for cm in IDENT_CALL.finditer(b):
                callee = cm.group(1)
                if callee in CONTROL:
                    continue
                calls[name].add(callee)
                if callee == name:
                    d["self"] += 1
            for cl in CLOSURE_REF.finditer(b):
                closures[name].add(cl.group(1))
                if cl.group(1) == name:
                    d["selfclosure"] += 1

    for i, raw in enumerate(lines):
        line = raw.rstrip("\n")
        stripped = STRLIT.sub('""', line)
        if cur is None:
            if not line or line[0].isspace() or line.startswith("//") or line.startswith("#"):
                continue
            if not line.endswith("{"):
                continue
            m = FUNC_DEF.match(line)
            if not m:
                continue
            name = m.group(1)
            if name in CONTROL:
                continue
            cur = name
            defs[name] = {"line": i + 1, "self": 0, "selfclosure": 0, "tail": 0}
            body = []
            depth = stripped.count("{") - stripped.count("}")
            continue
        depth += stripped.count("{") - stripped.count("}")
        body.append(line)
        if depth <= 0:
            finish(cur, body)
            cur = None
            body = []
    if cur is not None:
        finish(cur, body)
    return defs, calls, closures


# ------------------------------------------------------------- demangling

ESC = re.compile(r"_x([0-9a-f]{2})")


def mangle(lean_name):
    out = []
    for ch in lean_name:
        if ch == ".":
            out.append("_")
        elif ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_x%02x" % ord(ch))
    return "".join(out)


def strip_wrappers(sym):
    """Drop the compiler's decorations, keep the user-visible core."""
    s = sym
    for p in PKG_PREFIXES:
        if s.startswith(p):
            s = s[len(p):]
            break
    s = re.sub(r"___boxed$", "", s)
    s = re.sub(r"___closed__\d+(_value)?$", "", s)
    return s


def owner_of(sym):
    """The user declaration a specialised core function belongs to.

    `..._at___00<Owner>_spec__N` -> <Owner>.  Otherwise the symbol itself.
    """
    s = strip_wrappers(sym)
    m = re.findall(r"_at_+(?:0*)([A-Za-z0-9_]+?)_spec_+\d+", s)
    if m:
        s = m[-1]
    s = re.sub(r"^_+private_[A-Za-z0-9_]*?_0_+", "", s)
    return s


def readable(sym):
    s = owner_of(sym)
    s = ESC.sub(lambda m: chr(int(m.group(1), 16)), s)
    return s


# ------------------------------------------------------------ Lean indexing

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*"
    r"(def|abbrev|partial def)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
ENDNS = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_'.]*)")
INDUCTIVE = re.compile(r"^(?:inductive|structure)\s+([A-Za-z_][A-Za-z0-9_'.]*)")

LENGTH_TYPES = ("List ", "Array ", "ByteArray", "String", "Substring", "List(", "Array(")


CSIMP = re.compile(
    r"@\[csimp\][^\n]*\n?\s*theorem\s+[A-Za-z_][A-Za-z0-9_'!?.]*\s*:?[^:]*:\s*"
    r"@([A-Za-z_][A-Za-z0-9_'!?.]*)\s*=\s*@([A-Za-z_][A-Za-z0-9_'!?.]*)")


def index_lean():
    """mangled-name -> dict(lean, file, line, sig, partial).

    Also collects the `@[csimp]` replacements.  A definition named by the
    LEFT of a csimp theorem is a SPECIFICATION: it stays in the tree for the
    proofs to be about, the code generator emits the right-hand constant
    instead, and its surviving self-call is on no shipping path.  Reporting
    it as a live stack risk is a false positive -- and one that would keep
    the gate red after a repair, which is how a gate gets switched off.
    """
    idx = {}
    replaced = {}
    tree_types = set()
    for root, dirs, files in os.walk(LEAN_DIR):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in files:
            if not f.endswith(".lean"):
                continue
            path = os.path.join(root, f)
            rel = os.path.relpath(path, REPO)
            ns = []
            with open(path, "r", errors="replace") as fh:
                lines = fh.readlines()
            text = "".join(lines)
            for lhs, rhs in CSIMP.findall(text):
                replaced[lhs.split(".")[-1]] = rhs.split(".")[-1]
            for i, line in enumerate(lines):
                m = NAMESPACE.match(line)
                if m:
                    ns.append(m.group(1))
                    continue
                if ENDNS.match(line) and ns:
                    ns.pop()
                    continue
                mi = INDUCTIVE.match(line)
                if mi:
                    body = "".join(lines[i:i + 40])
                    nm = mi.group(1)
                    if re.search(r"\b(List|Array)\s+%s\b" % re.escape(nm), body) or \
                       re.search(r":\s*.*\b%s\b.*->.*\b%s\b" % (re.escape(nm), re.escape(nm)), body):
                        tree_types.add(nm)
                        tree_types.add(".".join(ns + [nm]) if ns else nm)
                    continue
                md = DECL.match(line)
                if not md:
                    continue
                short = md.group(2)
                full = ".".join(ns + [short]) if ns else short
                sig = "".join(lines[i:i + 12])
                sig = sig.split(":=")[0]
                idx[mangle(full)] = {
                    "lean": full, "file": rel, "line": i + 1,
                    "sig": " ".join(sig.split()),
                    "partial": line.lstrip().startswith("partial") or " partial def" in line,
                }
    return idx, tree_types, replaced


COUNTER_SIG = re.compile(r"\bNat\b")
RAW_INPUT = re.compile(r"ByteArray|List UInt8|Array UInt8|\bString\b|Substring|List Char|List Token|List Lexeme")
PARSEY = re.compile(r"decode|parse|read|scan|expand|lex|token|deserial", re.I)


def risk(entry, cls, decl, selfcalls):
    """Rank suspects.  Highest = recursion whose depth a document author sets.

    This is an ORDERING, not a proof.  It has no way to know whether a
    function is reachable from an entry point that sees untrusted input.
    """
    if cls not in ("length", "depth"):
        return 0
    r = 1
    sig = entry["sig"] if entry else ""
    if RAW_INPUT.search(sig):
        r += 3
    if PARSEY.search(decl):
        r += 2
    if cls == "depth":
        r += 1
    r += min(selfcalls, 3)
    return r


def classify(entry, tree_types):
    if entry is None:
        return "unknown", ""
    sig = entry["sig"]
    # the argument list only: everything after the declaration name
    args = sig
    tree_hit = [t for t in tree_types if re.search(r"\b%s\b" % re.escape(t.split(".")[-1]), args)]
    has_len = any(t.strip() in args or t in args for t in LENGTH_TYPES)
    has_nat = COUNTER_SIG.search(args) is not None
    if has_len:
        note = "list/array/string argument"
        if has_nat:
            note += "; Nat step count as well"
        return "length", note
    if tree_hit:
        return "depth", "recursive datatype: " + ", ".join(sorted(set(t.split(".")[-1] for t in tree_hit))[:3])
    if has_nat:
        return "counter", "Nat step argument -- input-length if the count is read from the input"
    return "bounded", ""


# ------------------------------------------------------------------- areas

AREAS = [
    ("XMPP", r"/XMPP/"),
    ("SPARQL", r"/SPARQL/"),
    ("RDF parsers/serializers", r"/RDF/"),
    ("Shardborough (storage)", r"/Storage/|/Cottas/|/HDT/"),
    ("JSON-LD", r"/JSONLD/"),
    ("XML", r"/XML/"),
    ("XSD", r"/XSD/"),
    ("OWL", r"/OWL/|/RDFS/"),
    ("SHACL/ShEx", r"/SHACL/|/ShEx/"),
    ("XPath/XSLT", r"/XPath/|/XSLT/"),
    ("CSVW", r"/CSVW/"),
]


def area_of(path):
    for name, pat in AREAS:
        if re.search(pat, "/" + path.replace(os.sep, "/")):
            return name
    return "everything else"


# -------------------------------------------------------------------- main


def sccs(graph, nodes):
    """Tarjan, iterative."""
    index = {}
    low = {}
    onstack = {}
    stack = []
    result = []
    counter = [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(graph.get(root, ())))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        onstack[root] = True
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in nodes:
                    continue
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    onstack[w] = True
                    work.append((w, iter(graph.get(w, ()))))
                    advanced = True
                    break
                elif onstack.get(w):
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    onstack[w] = False
                    comp.append(w)
                    if w == v:
                        break
                if len(comp) > 1:
                    result.append(comp)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", metavar="PATH", help="write the full table as JSON")
    ap.add_argument("--gate", action="store_true",
                    help="exit 1 if an input-length recursion appears that is "
                         "not in tools/lean-tail-recursion-allow.txt")
    ap.add_argument("--allow", default=os.path.join(REPO, "tools", "lean-tail-recursion-allow.txt"))
    ap.add_argument("--write-allow", action="store_true",
                    help="rewrite the allow file from this run (records the baseline)")
    ap.add_argument("--fstar", action="store_true",
                    help="scan formal/fstar/ocaml-output/*.ml for non-tail self-calls instead")
    ap.add_argument("--top", type=int, default=40, help="rows to print per class")
    args = ap.parse_args()

    if args.fstar:
        return fstar_mode(args)

    if not os.path.isdir(IR_DIR):
        sys.stderr.write("no compiled IR at %s -- run `lake build` in formal/lean4 first\n" % IR_DIR)
        return 2

    cfiles = []
    for root, _dirs, files in os.walk(IR_DIR):
        for f in files:
            if f.endswith(".c"):
                cfiles.append(os.path.join(root, f))
    if not cfiles:
        sys.stderr.write("no .c files under %s -- refusing to report a zero\n" % IR_DIR)
        return 2

    lean_idx, tree_types, csimp_replaced = index_lean()
    if not lean_idx:
        sys.stderr.write("no Lean declarations found under %s -- refusing to report\n" % LEAN_DIR)
        return 2

    all_defs = {}
    all_calls = defaultdict(set)
    sym_file = {}
    for path in cfiles:
        defs, calls, closures = scan_c_file(path)
        rel = os.path.relpath(path, IR_DIR)
        for n, d in defs.items():
            all_defs[n] = d
            sym_file[n] = rel
        for k, v in calls.items():
            all_calls[k] |= v
        for k, v in closures.items():
            all_calls[k] |= v

    def lookup(sym):
        core = owner_of(sym)
        if core in lean_idx:
            return lean_idx[core]
        # `where`-bound helpers compile to Owner_go / Owner_loop
        for suffix in ("_go", "_loop", "_aux", "_step"):
            if core.endswith(suffix) and core[: -len(suffix)] in lean_idx:
                return lean_idx[core[: -len(suffix)]]
        base = re.sub(r"_+lambda_+\d+$", "", core)
        if base in lean_idx:
            return lean_idx[base]
        return None

    rows = []
    for sym, d in sorted(all_defs.items()):
        if d["self"] == 0 and d["selfclosure"] == 0:
            continue
        if sym.endswith("___boxed"):
            continue
        entry = lookup(sym)
        cls, note = classify(entry, tree_types)
        short = (entry["lean"].split(".")[-1] if entry else readable(sym).split("_")[-1])
        if short in csimp_replaced:
            cls = "replaced"
            note = "specification; the code generator emits %s (@[csimp])" % csimp_replaced[short]
        leanfile = entry["file"] if entry else ""
        rows.append({
            "risk": risk(entry, cls, readable(sym), d["self"] + d["selfclosure"]),
            "symbol": sym,
            "decl": readable(sym),
            "lean": entry["lean"] if entry else "",
            "file": leanfile,
            "line": entry["line"] if entry else 0,
            "class": cls,
            "note": note,
            "selfcalls": d["self"],
            "selfclosure": d["selfclosure"],
            "tailjumps": d["tail"],
            "cfile": sym_file[sym],
            "area": area_of(leanfile or sym_file[sym]),
            "partial": bool(entry and entry["partial"]),
            "kind": "self",
        })

    # mutual cycles among our own functions
    ours = set(n for n in all_defs if n.startswith("lp_l4factoidal_"))
    cycles = [c for c in sccs(all_calls, ours)]
    cycle_rows = []
    for comp in cycles:
        members = sorted(comp)
        entry = None
        for m in members:
            entry = lookup(m)
            if entry:
                break
        cls, note = classify(entry, tree_types)
        cycle_rows.append({
            "members": [readable(m) for m in members],
            "size": len(members),
            "class": cls,
            "note": note,
            "file": entry["file"] if entry else "",
            "area": area_of(entry["file"] if entry else members[0]),
        })

    # ---------------------------------------------------------------- report
    print("Lean tail-recursion audit")
    print("=========================")
    print("C files scanned: %d   functions defined: %d   Lean declarations indexed: %d"
          % (len(cfiles), len(all_defs), len(lean_idx)))
    print("Self-recursive functions whose self-call is NOT a `goto _start` loop: %d" % len(rows))
    print("Mutual-recursion cycles among our own functions: %d" % len(cycle_rows))
    print()

    per_class = defaultdict(int)
    for r in rows:
        per_class[r["class"]] += 1
    print("By class")
    print("--------")
    for c in ("length", "depth", "counter", "bounded", "replaced", "unknown"):
        print("  %-9s %4d" % (c, per_class.get(c, 0)))
    print()

    per_area = defaultdict(lambda: defaultdict(int))
    for r in rows:
        per_area[r["area"]][r["class"]] += 1
    print("By area (length / depth / counter / bounded / replaced / unknown)")
    print("----------------------------------------------------------------")
    names = [n for n, _ in AREAS] + ["everything else"]
    for a in names:
        d = per_area.get(a)
        if not d:
            continue
        print("  %-26s %4d %4d %4d %4d %4d %4d" % (
            a, d.get("length", 0), d.get("depth", 0), d.get("counter", 0),
            d.get("bounded", 0), d.get("replaced", 0), d.get("unknown", 0)))
    print()

    ranked = sorted(rows, key=lambda r: (-r["risk"], r["area"], r["decl"]))
    print("Input-proportional recursions (class length and depth), ranked by risk")
    print("----------------------------------------------------------------------")
    print("%-4s %-48s %-8s %-24s %s" % ("risk", "declaration", "class", "area", "lean file:line"))
    shown = 0
    for r in ranked:
        if r["class"] not in ("length", "depth"):
            continue
        shown += 1
        if shown > args.top:
            break
        print("%-4d %-48s %-8s %-24s %s:%d" % (
            r["risk"], r["decl"][:48], r["class"], r["area"][:24], r["file"] or "?", r["line"]))
    remaining = sum(1 for r in ranked if r["class"] in ("length", "depth")) - min(shown, args.top)
    if remaining > 0:
        print("  ... %d more (use --json for the full table)" % remaining)
    print()

    if cycle_rows:
        print("Mutual-recursion cycles")
        print("-----------------------")
        for c in sorted(cycle_rows, key=lambda c: -c["size"])[:20]:
            print("  size %-3d %-8s %s" % (c["size"], c["class"], ", ".join(c["members"][:4])))
        print()

    print("Method limits: see the docstring at the top of this file.")

    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"rows": rows, "cycles": cycle_rows}, fh, indent=1)
        print("wrote %s" % args.json)

    if args.write_allow:
        with open(args.allow, "w") as fh:
            fh.write("# Baseline for `tools/lean-tail-recursion-audit.py --gate`.\n")
            fh.write("# Every declaration below recurses over an input-proportional\n")
            fh.write("# structure without a tail-call loop.  The gate fails when a NEW\n")
            fh.write("# one appears.  Removing a line is the goal; adding one needs a\n")
            fh.write("# reason in the commit message.\n")
            for r in sorted(set(r["decl"] for r in rows if r["class"] in ("length", "depth"))):
                fh.write(r + "\n")
        print("wrote %s" % os.path.relpath(args.allow, REPO))

    if args.gate:
        allow = set()
        if os.path.exists(args.allow):
            with open(args.allow) as fh:
                for line in fh:
                    line = line.split("#")[0].strip()
                    if line:
                        allow.add(line)
        offenders = [r for r in rows if r["class"] in ("length", "depth")
                     and r["decl"] not in allow]
        if offenders:
            print()
            print("GATE FAIL: %d input-proportional recursion(s) not in %s"
                  % (len(offenders), os.path.relpath(args.allow, REPO)))
            for r in offenders[:20]:
                print("  %s  (%s)  %s:%d" % (r["decl"], r["class"], r["file"], r["line"]))
            return 1
        print()
        print("GATE PASS: every input-proportional recursion is listed in %s"
              % os.path.relpath(args.allow, REPO))
    return 0


# ------------------------------------------------------------- F* / OCaml

ML_LET = re.compile(r"^(?:let|and)\s+rec\s+([A-Za-z_][A-Za-z0-9_']*)")
ML_TOP = re.compile(r"^(?:let|and|type|module|open|exception|external|val)\b")


def fstar_mode(args):
    ml_dir = os.path.join(REPO, "formal", "fstar", "ocaml-output")
    if not os.path.isdir(ml_dir):
        sys.stderr.write("no %s\n" % ml_dir)
        return 2
    files = sorted(f for f in os.listdir(ml_dir) if f.endswith(".ml"))
    if not files:
        sys.stderr.write("no .ml under %s -- refusing to report a zero\n" % ml_dir)
        return 2
    found = []
    for f in files:
        path = os.path.join(ml_dir, f)
        with open(path, "r", errors="replace") as fh:
            lines = fh.readlines()
        cur = None
        start = 0
        body = []
        for i, line in enumerate(lines + ["let __eof = ()\n"]):
            m = ML_LET.match(line)
            if m or (ML_TOP.match(line) and cur):
                if cur:
                    text = "".join(body)
                    calls = len(re.findall(r"\b%s\b" % re.escape(cur), text))
                    if calls:
                        found.append((f, start + 1, cur, calls))
                cur = m.group(1) if m else None
                start = i
                body = []
                continue
            if cur:
                body.append(line)
    print("F* extracted-OCaml self-recursion scan (source shape, not compiled form)")
    print("=======================================================================")
    print("files: %d   recursive functions with a self-call: %d" % (len(files), len(found)))
    print()
    print("This mode is COARSER than the Lean mode: OCaml is not compiled to a")
    print("readable IR here, so it cannot tell a tail call from a stacked one.")
    print("It ranks `let rec` definitions by self-call count as suspects only.")
    print()
    for f, ln, name, n in sorted(found, key=lambda t: -t[3])[:args.top]:
        print("  %-40s %-28s %s:%d" % (name[:40], "%d self-call(s)" % n, f, ln))
    return 0


if __name__ == "__main__":
    sys.exit(main())
