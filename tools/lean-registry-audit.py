#!/usr/bin/env python3
"""Audit the Lean tree against the results the project says matter.

`tools/lean-port-gap.py` answers "does this F* module have a Lean
counterpart".  `tools/lean-port-depth.py` tried to answer "how much of
it arrived" by comparing definition names, and CANNOT -- the two trees
share almost no internal vocabulary, because the Lean side was written
against the W3C text rather than translated (skills/counting-coverage
rule 6c).

This tool asks a question that CAN be answered, because it uses
SPECIFICATION vocabulary instead of implementation vocabulary. W3C
OWL 2 RL rule ids -- `cax-sco`, `prp-spo1`, `eq-ref` -- are fixed by
the Recommendation. Both trees must use them, whatever they call their
own lemmas. So the ids join the two trees where lemma names do not.

Source of truth for which ids matter: `docs/theorem-registry.md`, the
G1 reviewable-core registry, which CLAUDE.md names as the list of every
W3C rule id and its proof status.

WHAT THIS CAN AND CANNOT SEE  (skills/counting-coverage rule 7).

  It CAN see: a registry rule id with no Lean theorem naming it.

  It CANNOT see: whether that theorem says the right thing. A theorem
  named `caxSco_licensed` that proves something weaker still counts
  here. This tool locates; it does not review.

  It also cannot see a Lean theorem that proves a rule under a name
  not containing the id. Every such case found so far was a rule the
  registry itself records as unattempted or deferred, but that is an
  observation, not a guarantee.

Inputs are read from the repository on every run.  An empty read is a
hard error, not an empty report.
"""
import re, sys, pathlib, subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
REG  = ROOT / "docs" / "theorem-registry.md"
LEAN = ROOT / "formal" / "lean4" / "L4Factoidal"

# Rows the registry itself records as not proved on the F* side, each
# with the registry's own words. A Lean absence here MATCHES F* and is
# not a gap. Listed individually: a blanket exclusion would hide a
# regression.
DEFERRED = {
    "cls-maxqc3": "registry: UNATTEMPTED (F* too)",
    "cls-maxqc4": "registry: UNATTEMPTED (F* too)",
    "eq-diff2":   "clash-predicate row, truth column N/A pending domain review",
    "eq-diff3":   "clash-predicate row, truth column N/A pending domain review",
    "prp-adp":    "clash-predicate row, truth column N/A pending domain review",
    "dt-type1":   "registry: N/A -- axiomatic table, not a rule row",
}

if not REG.exists():
    sys.exit("lean-registry-audit: docs/theorem-registry.md is missing")
text = REG.read_text(errors="replace")

# Rule ids as the Recommendation spells them. Require a following
# digit-or-letter run so a git branch name like `dt-branch` (a real
# false positive, caught 2026-08-24) does not enter the set.
ids = sorted({m for m in re.findall(
    r'\b(?:cax|prp|cls|eq|scm|dt)-(?:[a-z]{2,}\d*|\d+)\b', text)
    if not m.endswith("-branch")})
if not ids:
    sys.exit("lean-registry-audit: no rule ids parsed -- broken registry read")

lean_files = list(LEAN.rglob("*.lean"))
if not lean_files:
    sys.exit("lean-registry-audit: no .lean files found -- broken checkout")
blob = "\n".join(p.read_text(errors="replace") for p in lean_files)

THM = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z_0-9\'.]+)',
    re.M)
thm_names = set(THM.findall(blob))

def camel(rid):
    parts = rid.split('-')
    return parts[0] + ''.join(w.capitalize() for w in parts[1:])

def snake(rid):
    return rid.replace('-', '_')

proved, deferred_ok, gaps = [], [], []
for rid in ids:
    key_c, key_s = camel(rid).lower(), snake(rid).lower()
    hit = any(key_c in n.lower() or key_s in n.lower() for n in thm_names)
    if hit:
        proved.append(rid)
    elif rid in DEFERRED:
        deferred_ok.append(rid)
    else:
        gaps.append(rid)

print(f"Registry rule ids: {len(ids)}")
print(f"With a Lean theorem naming them: {len(proved)}")
print(f"Absent, and recorded as unproved on the F* side too: {len(deferred_ok)}")
print(f"Absent with no such record -- REAL GAPS: {len(gaps)}")
print()
if deferred_ok:
    print("Absent by agreement with the F* side:")
    for rid in deferred_ok:
        print(f"  {rid:14s} {DEFERRED[rid]}")
    print()
if gaps:
    print("REAL GAPS -- a registry rule the Lean tree does not name:")
    for rid in gaps:
        print(f"  {rid}")
    sys.exit(1)
print("No gap: every registry rule id the F* side proves is named by a "
      "Lean theorem.")
print()
print("This locates theorems; it does not review them. See the header.")
