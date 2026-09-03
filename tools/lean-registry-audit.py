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

IDENTIFIERS ARE COMPARED WHOLE (fixed 2026-09-03).

  The first version of this tool matched a PREFIX. `\\b` ends a match at
  a `-`, because `-` is a non-word character, so `dt-rng-intersect` in
  the registry produced the id `dt-rng`, which is not a rule, and the
  tool reported it as a real gap. `eq-rep-s`, `eq-rep-p` and
  `eq-rep-o` all collapsed to one id `eq-rep`, so three rules were
  counted as one. A first patch excluded the string `dt-branch` BY
  NAME; that was a third symptom treated, not the defect.

  The defect is fixed in two places:

  1. Ids are read as WHOLE hyphenated tokens, and then kept only if
     the token is one of the 78 rule ids the OWL 2 Profiles
     Recommendation defines (RL_RULE_IDS below, Tables 4 to 9 of
     https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules).
     A token that is not a rule id is REPORTED, not silently dropped,
     so the exclusion can be audited. `dt-branch` (a git branch),
     `dt-rng-intersect` and `cax-adc-dw` (local rule-family names) and
     `prp-rfl` (the registry states the RL profile has no such row)
     leave through that list, with no name-specific rule.

  2. A Lean theorem name is matched by its camel/snake SEGMENTS, not
     by substring. `caxScoForS_ofGraph` splits to
     [cax, sco, for, s, of, graph], and `cax-sco` matches the first
     two segments. A substring test made `eq-rep` match `eqRepO`.

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
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
REG  = ROOT / "docs" / "theorem-registry.md"
LEAN = ROOT / "formal" / "lean4" / "L4Factoidal"

# The rule ids of OWL 2 RL/RDF, Tables 4 to 9 of the OWL 2 Profiles
# Recommendation. A token in the registry that is not in this set is
# not a rule id, whatever it looks like.
RL_RULE_IDS = set("""
eq-ref eq-sym eq-trans eq-rep-s eq-rep-p eq-rep-o eq-diff1 eq-diff2 eq-diff3
prp-ap prp-dom prp-rng prp-fp prp-ifp prp-irp prp-symp prp-asyp prp-trp
prp-spo1 prp-spo2 prp-eqp1 prp-eqp2 prp-pdw prp-adp prp-inv1 prp-inv2
prp-key prp-npa1 prp-npa2
cls-thing cls-nothing1 cls-nothing2 cls-int1 cls-int2 cls-uni cls-com
cls-svf1 cls-svf2 cls-avf cls-hv1 cls-hv2 cls-maxc1 cls-maxc2
cls-maxqc1 cls-maxqc2 cls-maxqc3 cls-maxqc4 cls-oo
cax-sco cax-eqc1 cax-eqc2 cax-dw cax-adc
dt-type1 dt-type2 dt-eq dt-diff dt-not-type
scm-cls scm-sco scm-eqc1 scm-eqc2 scm-op scm-dp scm-spo scm-eqp1 scm-eqp2
scm-dom1 scm-dom2 scm-rng1 scm-rng2 scm-hv scm-svf1 scm-svf2 scm-avf1
scm-avf2 scm-int scm-uni
""".split())

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
}

if not REG.exists():
    sys.exit("lean-registry-audit: docs/theorem-registry.md is missing")
text = REG.read_text(errors="replace")
if not text.strip():
    sys.exit("lean-registry-audit: docs/theorem-registry.md is empty")

# Whole hyphenated tokens. The lookbehind and the greedy tail stop a
# prefix of a longer token from being read as an id.
TOKEN = re.compile(r'(?<![A-Za-z0-9-])(?:cax|prp|cls|eq|scm|dt)-[a-z0-9]+(?:-[a-z0-9]+)*')
tokens = sorted(set(TOKEN.findall(text)))
if not tokens:
    sys.exit("lean-registry-audit: no rule-id-shaped tokens parsed -- broken registry read")

ids     = [t for t in tokens if t in RL_RULE_IDS]
not_ids = [t for t in tokens if t not in RL_RULE_IDS]
if not ids:
    sys.exit("lean-registry-audit: no OWL 2 RL rule ids parsed -- broken registry read")

lean_files = list(LEAN.rglob("*.lean"))
if not lean_files:
    sys.exit("lean-registry-audit: no .lean files found -- broken checkout")

THM = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z_0-9\'.]+)',
    re.M)
blob = "\n".join(p.read_text(errors="replace") for p in lean_files)
thm_names = set(THM.findall(blob))
if not thm_names:
    sys.exit("lean-registry-audit: no theorem or lemma names found -- broken Lean read")

SEG = re.compile(r'[A-Z]+(?![a-z])|[A-Za-z][a-z0-9]*')

def segments(name):
    """Split a Lean identifier into lowercased camel / snake segments."""
    return [s.lower() for s in SEG.findall(name.replace("'", "_"))]

name_segments = [segments(n) for n in thm_names]

def named_by_a_theorem(rid):
    want = rid.split('-')
    n = len(want)
    for segs in name_segments:
        for i in range(len(segs) - n + 1):
            if segs[i:i + n] == want:
                return True
    return False

proved, deferred_ok, gaps = [], [], []
for rid in ids:
    if named_by_a_theorem(rid):
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
if not_ids:
    print(f"Rule-id-shaped tokens that are NOT OWL 2 RL rule ids, ignored ({len(not_ids)}):")
    print("  " + ", ".join(not_ids))
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
