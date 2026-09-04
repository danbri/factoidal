#!/usr/bin/env python3
"""Rank OWL 2 RL failure bucket B3 by the clash row that should fire.

B3 is "a premise asserted inconsistent produced no clash row". The
bucket label carries no information about WHICH inconsistency was
missed, so `tools/owl-rl-failure-split.py` leaves its members unranked.
This tool reads each B3 case's PREMISE from the W3C OWL catalogs and
asks one question: could a Horn closure decide this inconsistency at
all?

An OWL 2 RL clash row (Profiles section 4.3) has all premises positive,
no case split and no invented individual. So a premise whose only proof
of inconsistency needs an existential witness or a disjunctive case
split is NOT closure work, whatever row is added; it belongs to the
tableau refuter. That is the tier gate, and it is syntactic: a premise
mentioning someValuesFrom / minCardinality / an exact cardinality goes
to tier B, and a premise mentioning unionOf / oneOf / complementOf goes
to tier B. The gate under-promises by design.

Tier A cases are then labelled with the Profiles row, or the short
composition of rows, that would decide them.

Usage:

    formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl > run.txt
    python3 tools/owl-b3-premise-rank.py run.txt

Run from the repository root; the OWL catalogs are read from
third_party/testing/owl.

WHAT THIS CANNOT SEE, per anti-pattern 28:

1. It reads the premise, not the closure. Tier A says a Horn row COULD
   decide the case, not that adding the row makes it pass: the closure
   must also derive the row's other premises. The correction is the
   measured delta after a landing.
2. The tier gate is syntactic. A premise that mentions an existential
   goes to tier B even when some other part of it is separately
   inconsistent by a Horn row.
3. Where a case carries both, fsPremiseOntology is read in preference
   to rdfXmlPremiseOntology, so the construct names are Functional
   Syntax where the catalog supplies them.
"""

import collections
import html
import os
import re
import subprocess
import sys

CATALOGS = [
    "all.rdf", "profile-EL.rdf", "profile-QL.rdf", "profile-RL.rdf",
    "semantics-direct.rdf", "syntax-dl.rdf", "type-consistency.rdf",
    "type-inconsistency.rdf", "type-negative-entailment.rdf",
    "type-positive-entailment.rdf",
]

PREMISE_TAGS = ["fsPremiseOntology", "rdfXmlPremiseOntology",
                "owlXmlPremiseOntology", "turtlePremiseOntology",
                "premiseOntology"]

EXISTENTIAL = (r"SomeValuesFrom", r"someValuesFrom", r"MinCardinality",
               r"minCardinality", r"owl:cardinality", r"ExactCardinality")
DISJUNCTIVE = (r"UnionOf", r"unionOf", r"ObjectOneOf", r"owl:oneOf",
               r"ComplementOf", r"owl:complementOf")
MAXCARD = (r"maxCardinality", r"MaxCardinality",
           r"maxQualifiedCardinality", r"MaxQualifiedCardinality")


def b3_units(run_path):
    """The B3 members of a probe run, as {case identifier: unit count}."""
    here = os.path.dirname(os.path.abspath(__file__))
    out = subprocess.run(
        [sys.executable, os.path.join(here, "owl-rl-failure-split.py"), run_path],
        capture_output=True, text=True, check=True).stdout
    if "### B3:" not in out:
        sys.exit("owl-rl-failure-split.py printed no B3 section")
    section = out.split("### B3:")[1].split("### B4:")[0]
    counts = collections.Counter()
    for line in section.splitlines():
        line = line.strip().split(" | ")[0]
        m = re.match(r"^(.*) \[(\w+)\]$", line)
        if m:
            counts[m.group(1)] += 1
    return counts


def premises(corpus, wanted):
    """The premise text of each wanted case, read from the catalogs."""
    found = {}
    for catalog in CATALOGS:
        path = os.path.join(corpus, catalog)
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8", errors="replace").read()
        for m in re.finditer(r"<test:TestCase\b.*?</test:TestCase>", text, re.S):
            block = m.group(0)
            im = re.search(r"<test:identifier[^>]*>(.*?)</test:identifier>",
                           block, re.S)
            if not im:
                continue
            ident = html.unescape(im.group(1)).strip()
            if ident not in wanted or ident in found:
                continue
            for tag in PREMISE_TAGS:
                pm = re.search(r"<test:%s[^>]*>(.*?)</test:%s>" % (tag, tag),
                               block, re.S)
                if pm:
                    found[ident] = html.unescape(pm.group(1))
                    break
            else:
                found[ident] = ""
    return found


def has(text, patterns):
    return any(re.search(p, text) for p in patterns)


def classify(text):
    """(tier, group) for one premise. Tier B first: the gate."""
    if has(text, EXISTENTIAL):
        return ("B", "an existential witness is required")
    if has(text, DISJUNCTIVE):
        return ("B", "a disjunction must be case-split")
    if has(text, MAXCARD):
        return ("B", "max-cardinality N>0 - counting distinct fillers")
    if has(text, (r"HasKey", r"owl:hasKey")):
        return ("A", "prp-key then eq-diff1")
    if has(text, (r"bottomObjectProperty", r"bottomDataProperty")):
        return ("A", "owl:bottom*Property, Table 5")
    if has(text, (r"FunctionalDataProperty", r"FunctionalProperty",
                  r"InverseFunctional")):
        return ("A", "prp-fp then literal distinctness (dt-diff + eq-diff1)")
    if (has(text, (r"DataPropertyRange", r"DataAllValuesFrom", r"DataHasValue",
                   r"rdfs:range"))
            and has(text, (r"\^\^", r"rdf:datatype"))):
        return ("A", "dt-not-type (Table 8)")
    if (has(text, (r"rdf-syntax-ns#nil", r"rdf:nil"))
            and has(text, (r"rdf:rest", r"rdf:first"))):
        return ("-", "rdf:nil is not a list cell - no Profiles row")
    if has(text, (r"owl#Thing",)) and has(text, (r"equivalentClass",
                                                 r"EquivalentClasses")):
        return ("A", "ICEXT(I(owl:Thing)) = IR then cls-nothing2")
    if has(text, (r"DisjointClasses", r"owl:disjointWith",
                  r"AllDisjointClasses")):
        return ("A", "cax-dw / cax-adc")
    if has(text, (r"DisjointDataProperties", r"DisjointObjectProperties",
                  r"propertyDisjointWith")):
        return ("A", "prp-pdw / prp-adp")
    if has(text, (r"DifferentIndividuals", r"owl:differentFrom",
                  r"AllDifferent")):
        return ("A", "eq-diff1")
    return ("?", "unclassified")


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    run_path = sys.argv[1]
    corpus = sys.argv[2] if len(sys.argv) > 2 else "third_party/testing/owl"
    if not os.path.isdir(corpus):
        sys.exit("no OWL corpus at %s - run tools/ensure-test-env.sh" % corpus)

    units = b3_units(run_path)
    if not units:
        sys.exit("no B3 members in %s" % run_path)
    texts = premises(corpus, set(units))
    missing = sorted(set(units) - set(texts))
    if missing:
        sys.exit("no premise found in the catalogs for: %s" % ", ".join(missing))

    groups = collections.defaultdict(lambda: [0, []])
    for ident, count in units.items():
        key = classify(texts[ident])
        groups[key][0] += count
        groups[key][1].append(ident)

    total = sum(units.values())
    print("B3: %d units, %d cases" % (total, len(units)))
    print()
    order = sorted(groups.items(), key=lambda kv: (kv[0][0], -kv[1][0]))
    for (tier, group), (count, idents) in order:
        print("[%s] %-58s %3d units, %2d cases" % (tier, group, count, len(idents)))
        if tier != "B":
            for ident in sorted(idents):
                print("         %s" % ident)
    print()
    for tier in ("A", "B", "-", "?"):
        n = sum(c for (t, _), (c, _) in groups.items() if t == tier)
        if n:
            print("tier %s: %d units" % (tier, n))


if __name__ == "__main__":
    main()
