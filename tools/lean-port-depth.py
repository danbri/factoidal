#!/usr/bin/env python3
"""How much of each COVERED F* module the Lean counterpart actually carries.

`tools/lean-port-gap.py` answers "does this F* module have a Lean
counterpart".  That is a question about MODULES.  This tool asks a
narrower question about the same pairs: of the F* module's top-level
definitions, how many have a same-named definition on the Lean side?

WHY IT EXISTS.  2026-08-24: `SPARQL11.Algebra` is aliased to
`SPARQL.Algebra` and counts as covered, but
`strip_rewrite_internal_vars` and its two helpers were not in the Lean
tree at all.  An alias is a statement about a module, and a module is
not one result.

WHAT THIS METHOD CAN AND CANNOT SEE  (skills/counting-coverage rule 7).

  It CAN see: a definition absent from the Lean side under any spelling
  this normalisation recognises.

  It CANNOT see: a definition RENAMED beyond the two normalisations
  below (reported as missing when it is present), a definition split
  into several (same), a Lean definition with the right name and the
  wrong content (reported as present when it is not), or a definition
  the port deliberately drops because Lean needs no counterpart.

TWO CORRECTIONS THE FIRST VERSION NEEDED.  Run per-module and without
prefix stripping, this tool reported 73% of definitions missing, with
several modules known to be fully ported at 100%.  Both causes were
naming, not absence:

  1. F* carries a domain prefix that Lean drops under a namespace --
     `vc_looks_like_iri` against `VC.looksLikeIri`, `rif_pred_ns`
     against `RIF.predNs`.  So a leading segment matching a component
     of the F* module name is stripped before comparing, as is a
     leading `lemma_` or `theorem_`.
  2. A definition ported into a DIFFERENT Lean module -- shared
     vocabulary especially -- is invisible to a per-module comparison.
     So the search is tree-wide, and the per-module column reports
     where the counterpart module itself does not carry it.

  So a high miss count is a READING LIST, never a verdict.  Every
  number this tool prints needs a human to open the file.

Inputs are walked from the repository on every run (rule 5).  An empty
walk is a hard error, not an empty report.
"""
import re, sys, pathlib, collections

ROOT = pathlib.Path(__file__).resolve().parent.parent
FS   = ROOT / "formal" / "fstar"
LEAN = ROOT / "formal" / "lean4" / "L4Factoidal"

sys.path.insert(0, str(ROOT / "tools"))

def norm(name):
    """snake_case and camelCase collapse to the same key."""
    return re.sub(r'[^a-z0-9]', '', name.lower())

FS_DECL   = re.compile(r'^(?:let rec|let|val|assume val)\s+([a-zA-Z_][a-zA-Z_0-9\']*)', re.M)
LEAN_DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?'
    r'(?:def|abbrev|theorem|lemma|structure|inductive|instance)\s+([A-Za-z_][A-Za-z_0-9\'.]*)', re.M)

LEMMA_PREFIX = re.compile(r'^(?:lemma|theorem|thm)_')

def fs_variants(name, mod_components):
    """The F* name, and the spellings a Lean port plausibly uses."""
    out = {norm(name)}
    stripped = LEMMA_PREFIX.sub('', name)
    out.add(norm(stripped))
    for cand in (name, stripped):
        parts = cand.split('_')
        # strip up to two leading segments that echo the module name
        for depth in (1, 2):
            if len(parts) > depth and all(
                    parts[i].lower() in mod_components for i in range(depth)):
                out.add(norm('_'.join(parts[depth:])))
    return {v for v in out if v}

def fs_decls(path, mod):
    comps = {c.lower() for c in mod.split('.')}
    comps |= {c.lower().rstrip('s') for c in mod.split('.')}
    names = [m for m in FS_DECL.findall(path.read_text(errors='replace'))
             if m not in ("rec",)]
    return {n: fs_variants(n, comps) for n in names}

def lean_decls(path):
    out = set()
    for m in LEAN_DECL.findall(path.read_text(errors='replace')):
        out.add(norm(m))
        out.add(norm(m.split('.')[-1]))   # Namespace.name also matches name
    return out

# ---- the covered pairs, taken from the gap tool so the two agree ----
gap_src = (ROOT / "tools" / "lean-port-gap.py").read_text()
m = re.search(r'^alias\s*=\s*\{(.*?)^\}', gap_src, re.S | re.M)
if not m:
    sys.exit("lean-port-depth: could not read the alias table from lean-port-gap.py")
alias = dict(re.findall(r'"([^"]+)"\s*:\s*"([^"]+)"', m.group(1)))

fs_mods = {p.stem: p for p in FS.glob("*.fst")}
if not fs_mods:
    sys.exit("lean-port-depth: no .fst files found -- broken checkout, not an empty report")
lean_mods = {}
for p in LEAN.rglob("*.lean"):
    lean_mods[".".join(p.relative_to(LEAN).with_suffix("").parts)] = p
if not lean_mods:
    sys.exit("lean-port-depth: no .lean files found -- broken checkout, not an empty report")

def leafkey(mod):
    parts = mod.split('.')
    return (parts[-2] + "." + parts[-1]).lower() if len(parts) > 1 else parts[-1].lower()

TREE_HAVE = set()
for _n, _p in lean_mods.items():
    TREE_HAVE |= lean_decls(_p)

lean_by_leaf = collections.defaultdict(list)
for name in lean_mods:
    lean_by_leaf[leafkey(name)].append(name)

rows = []
for fmod, fpath in sorted(fs_mods.items()):
    targets = []
    if fmod in alias and alias[fmod] in lean_mods:
        targets = [alias[fmod]]
    else:
        targets = lean_by_leaf.get(leafkey(fmod), [])
    if not targets:
        continue                       # not covered; the gap tool reports it
    local_have = set()
    for t in targets:
        local_have |= lean_decls(lean_mods[t])
    want = fs_decls(fpath, fmod)
    if not want:
        continue
    miss = sorted(n for n, vs in want.items() if not (vs & TREE_HAVE))
    local_miss = sorted(n for n, vs in want.items() if not (vs & local_have))
    rows.append((len(miss), len(want), fmod, targets, miss, len(local_miss)))

rows.sort(key=lambda r: (-r[0], r[2]))
tot_want  = sum(r[1] for r in rows)
tot_miss  = sum(r[0] for r in rows)
tot_local = sum(r[5] for r in rows)
print("READ THIS BEFORE READING ANY NUMBER BELOW.")
print()
print("This tool DOES NOT measure how much of a module is ported, and")
print("no percentage it could print would mean that. The two trees")
print("share almost no internal vocabulary, because the Lean side was")
print("written against the W3C text rather than translated. Where F*")
print("has `rho_df_closure_iter` and `lemma_dedup_pairs_memP`, Lean has")
print("`Derives.cut` and `mem_addOne_of_mem`: the same results by a")
print("different proof architecture. A name-level comparison cannot")
print("tell that apart from an absence, and most of what it flags is")
print("the first case.")
print()
print("Use it as a READING LIST only: a module high on it is a module")
print("to open. The question it helps with is 'which covered modules")
print("should I audit by hand first', never 'how covered are they'.")
print()
print(f"Covered F* modules examined: {len(rows)}")
print(f"F* top-level definitions in them: {tot_want}")
print(f"F* names with no same-named Lean definition anywhere: {tot_miss}")
print(f"  ... and with none in the named counterpart module: {tot_local}")
print("Neither figure is a coverage number. See the paragraph above.")
print()
print("| F* module | absent from tree | of | Lean counterpart |")
print("|---|---|---|---|")
shown = 0
for miss_n, want_n, fmod, targets, _m, _l in rows:
    if miss_n == 0 or shown >= 20:
        continue
    print(f"| `{fmod}` | {miss_n} | {want_n} | `{', '.join(targets)}` |")
    shown += 1
