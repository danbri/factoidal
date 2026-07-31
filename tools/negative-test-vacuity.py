#!/usr/bin/env python3
"""Vacuity detector for negative-style W3C tests (issue #333).

WHY THIS EXISTS
===============

A *negative* test asserts a non-entailment: the engine must NOT derive X.
An engine that derives *nothing at all* passes every such test trivially.
Those are vacuous passes. They make a suite look green while measuring
nothing.

Example that motivated this tool: the `rdf-mt` manifest has 42 entries, of
which 19 are `mf:NegativeEntailmentTest`. The suite scores 39 pass, 0 fail
(out of 42). At the same time, finding RS-2 says six RDFS rule rows are
unimplemented and RS-4 says the rdf12 "RDFS" regime runs none of rdfs1-13.
Nothing goes red, because a negative test cannot go red when the engine
concludes nothing.

WHAT THIS TOOL IS NOT
=====================

It measures. It changes no engine behaviour and no existing suite's score.

It does not reimplement entailment (iron rule #15). Every derivation it
looks at is produced by the engine itself, through `factoidal entail`
and `factoidal --dump`. This file only does set arithmetic on the engine's
own output, plus two purely syntactic shape tests on triples (subject ==
object; predicate-set intersection) that involve no vocabulary or rule
knowledge whatever.

THE VACUITY CRITERION
=====================

Take a negative entailment test T: premise graph G, conclusion graph C,
declared entailment regime R (`mf:entailmentRegime` in the manifest). The
engine passes T by computing the closure of G under R and finding no
homomorphism of C into it.

That pass tells us something only if the closure step actually did work
attributable to *this test's premise*. So:

    A_R  = closure_R(empty graph)          the regime's premise-independent
                                           axiom set, obtained by asking the
                                           engine to close an empty file
    D    = closure_R(G) \\ (G union A_R)    the premise-attributable
                                           derivations
    D_ne = { t in D : subject(t) != object(t) }

Subtracting A_R is what stops "the engine injects its 16 RDFS axiomatic
triples" from being counted as work. Filtering self-loops (`x p x`) out of
D is what stops "the engine closed subClassOf reflexively over the terms
already in the premise" from being counted as work; a triple that relates a
term only to itself carries no relation between distinct terms.

Status ladder (closure regimes -- "RDF", "RDFS", "OWL-RL"):

  vacuous   D is empty. The closure of the premise is the premise plus the
            regime axioms. This test cannot fail, whatever the engine does.
  weak      D is non-empty but D_ne is empty  -> reason `reflexive-only`;
            or D_ne is non-empty but no triple in D carries a predicate that
            occurs in the conclusion C -> reason `off-target`. The engine
            worked, but not in the direction the test probes.
  worked    D_ne is non-empty AND some triple in D carries a predicate that
            occurs in C. The engine derived something of the shape the test
            is asking about, and still did not derive C.

EXEMPTIONS
==========

An exemption must come from a stated, checkable property of the test's own
data. There is no hand-maintained list of inconvenient test names in this
file, and there must never be one.

  exempt / regime-has-no-closure
      The test declares `mf:entailmentRegime "simple"`. Simple entailment is
      defined in RDF Semantics as subgraph-with-instance; it has no
      derivation rules, so closure_simple(G) = G and an empty D is correct,
      not a defect. Checkable property: the literal value of the test's own
      `mf:entailmentRegime`.

      Simple-regime negatives are still degenerate-passable, so they get a
      weaker substitute signal instead of a score: `shared_predicates`, the
      size of the intersection of the predicate sets of G and C. If it is
      zero, the non-entailment is decidable by a predicate scan alone and
      the homomorphism search never ran; the test is recorded as
      `exempt` with `homomorphism_reached: false`.

NOT EXEMPT, ON PURPOSE
======================

  `mf:result false` entries (rdf-mt has three). These carry no conclusion
  graph; they assert that the premise is consistent. There is no X to
  not-conclude, which sounds like grounds for exemption -- but the engine
  has no inconsistency detector on this path at all (bin/w3c-runner's
  NegativeEntailmentTest arm with `mf:result` absent just checks the file
  parses), so nothing can ever fail them. That is vacuity, not an
  exemption. They are reported `vacuous` with reason
  `no-conclusion-and-no-consistency-check`.

KNOWN FALSE POSITIVES (tool says vacuous, test is arguably fine)
================================================================

  * A premise so small that even a complete implementation of the regime
    would derive nothing beyond axioms and reflexivity. Real, and the
    `weak/reflexive-only` bucket is where most such cases land rather than
    in `vacuous`. Any `vacuous` verdict should still be read against the
    premise, which is why every record carries `premise_triples` and the
    premise path.

KNOWN FALSE NEGATIVES (tool says worked, pass is still uninformative)
=====================================================================

  * The predicate-overlap test is coarse. A closure can derive many
    triples carrying a predicate that also occurs in C without ever
    exercising the rule that could have produced C itself. Closing this
    gap needs per-rule firing counts out of the F* closure, which is engine
    work and deliberately not done here.
  * Nothing here checks that the conclusion C was reachable in principle
    under a *complete* implementation of R. That check needs rule
    knowledge, which would put entailment logic in a runner.
  * Blank nodes: D is a set difference over the engine's N-Triples output.
    If the engine relabelled a premise blank node between the `--dump` and
    the `entail` invocation, premise triples would look derived. The tool
    detects that directly (`premise_subsumed`) and marks the record
    untrusted rather than reporting a number it cannot stand behind.

CLASSES CENSUSED BUT NOT SCORED
===============================

Each carries its reason in the JSON, so the exclusion is visible rather
than silent. See CENSUS_CLASSES below.
"""

from __future__ import annotations

import argparse
import collections
import datetime
import json
import os
import re
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MF = "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
TYPE = RDF + "type"
OWLT = "http://www.w3.org/2007/OWL/testOntology#"

# ---------------------------------------------------------------------------
# Test-type classification.
#
# Keyed by the FULL rdf:type IRI of a manifest entry. `polarity` records
# which degenerate engine passes the test for free:
#
#   derive-nothing   an engine that materialises nothing passes it
#   reject-all       a parser that rejects every input passes it
#   report-all       a validator that flags everything invalid passes it
#   check-nothing    a validator that flags nothing passes it
#   none             no constant-output engine passes it (positive tests)
# ---------------------------------------------------------------------------
TEST_TYPES = {
    MF + "NegativeEntailmentTest": ("entailment-negative", "derive-nothing"),
    MF + "PositiveEntailmentTest": ("entailment-positive", "none"),
    OWLT + "NegativeEntailmentTest": ("entailment-negative", "derive-nothing"),
    OWLT + "PositiveEntailmentTest": ("entailment-positive", "none"),
    OWLT + "ConsistencyTest": ("consistency", "derive-nothing"),
    OWLT + "InconsistencyTest": ("inconsistency", "none"),
    MF + "NegativeSyntaxTest": ("syntax-negative", "reject-all"),
    MF + "NegativeSyntaxTest11": ("syntax-negative", "reject-all"),
    MF + "NegativeUpdateSyntaxTest11": ("syntax-negative", "reject-all"),
    MF + "PositiveSyntaxTest": ("syntax-positive", "none"),
    MF + "PositiveSyntaxTest11": ("syntax-positive", "none"),
    MF + "PositiveUpdateSyntaxTest11": ("syntax-positive", "none"),
    MF + "QueryEvaluationTest": ("query-evaluation", "depends-on-expected"),
}

# rdftest: / sht: / shex: families follow a naming convention rather than a
# fixed IRI set, so they are matched on the local name.
LOCALNAME_RULES = [
    (re.compile(r"NegativeSyntax$"), ("syntax-negative", "reject-all")),
    (re.compile(r"NegativeEval$"), ("eval-negative", "reject-all")),
    (re.compile(r"PositiveSyntax$"), ("syntax-positive", "none")),
    (re.compile(r"^Test.*Eval$"), ("eval-positive", "none")),
    (re.compile(r"^NegativeValidationTest$"), ("validation-negative", "report-all")),
    (re.compile(r"^PositiveValidationTest$"), ("validation-positive", "check-nothing")),
    (re.compile(r"^NegativeStructure$"), ("validation-negative", "report-all")),
    (re.compile(r"^NegativeSyntax$"), ("syntax-negative", "reject-all")),
    (re.compile(r"^Validate$"), ("validation-positive", "check-nothing")),
    (re.compile(r"^ValidationTest$"), ("validation", "depends-on-expected")),
]

# Classes we census but do not score in v1, each with the reason why.
CENSUS_CLASSES = {
    "syntax-negative": (
        "not-scored",
        "A negative SYNTAX test is a different shape: 'did work' means the "
        "parser reached and rejected a specific construct, not that it "
        "derived triples, so the closure criterion does not apply. Scoring "
        "it properly needs the byte offset at which the parser gave up, "
        "which the F* parsers do not surface through any CLI today (they "
        "return None). The manifest-level anti-vacuity witness that IS "
        "computed here is `positive_siblings`: the count of positive "
        "syntax/eval tests in the same manifest. A parser that rejects "
        "everything fails all of those, so a manifest with passing "
        "positive siblings cannot be scored by a reject-all engine. That "
        "witness is per-manifest, not per-test: it does not show the "
        "rejection happened for the right reason.",
    ),
    "eval-negative": (
        "not-scored",
        "Same shape as syntax-negative: the parser must reject at a "
        "specific point. Same missing error-offset API.",
    ),
    "validation-negative": (
        "not-scored",
        "SHACL/ShEx/JSON-Schema expected-invalid tests are passed for free "
        "by a report-everything-invalid validator, not by a derive-nothing "
        "one. Their degenerate engine is the opposite of the entailment "
        "case, so the closure criterion does not transfer. Scoring needs "
        "the identity of the constraint component that fired, compared "
        "against the expected report -- that is a validator-report "
        "comparison, deliberately left to the SHACL/ShEx runners.",
    ),
    "validation-positive": (
        "not-scored",
        "Expected-conformant tests are the vacuity-prone half of a "
        "validation suite: a validator that evaluates no constraint at all "
        "reports conforms=true and passes every one. Scoring needs a count "
        "of constraint components actually evaluated, which no runner "
        "emits today.",
    ),
    "consistency": (
        "not-scored",
        "OWL ConsistencyTest asserts an ontology IS consistent, so a "
        "reasoner that derives nothing passes it. The measured path is "
        "owl_runner's DL/Tableau regime, which `factoidal entail` does not "
        "expose (it offers RDFS and OWL-RL materialisation only), so this "
        "tool cannot observe the derivations that path makes.",
    ),
    "entailment-negative": (
        "partly-scored",
        "The rdf-mt and rdf12 rdf-semantics manifests are scored with the "
        "closure criterion. The OWL 2 catalogs are NOT: their premise and "
        "non-conclusion ontologies are embedded as literals inside the "
        "catalog, and the engine's own N-Triples serializer emits those "
        "literals with raw newlines and unescaped quotes, so they cannot "
        "be recovered through `factoidal --dump` without a second parser. "
        "Recovering them some other way would mean this tool parsing RDF "
        "itself, which it does not do. Count of unrecoverable literal "
        "lines per catalog is in census_manifests[].nt_lines_skipped.",
    ),
    "validation": (
        "not-scored",
        "A SHACL/ShEx ValidationTest carries its polarity in the expected "
        "validation report (sh:conforms plus the sh:result list), not in "
        "its rdf:type, so it splits into both a vacuity-prone half "
        "(expected-conformant: passed for free by a validator that "
        "evaluates no constraint) and a non-vacuity-prone half. Splitting "
        "them needs the expected report read per test and, to score, a "
        "count of constraint components actually evaluated -- which no "
        "runner emits today.",
    ),
    "inconsistency": (
        "not-vacuity-prone",
        "An InconsistencyTest requires the engine to PRODUCE a "
        "contradiction. A derive-nothing engine fails it. Recorded for "
        "contrast with the consistency row, not flagged.",
    ),
    "entailment-positive": (
        "not-vacuity-prone",
        "A positive entailment test requires the engine to derive the "
        "conclusion. A derive-nothing engine fails it.",
    ),
    "syntax-positive": ("not-vacuity-prone", "A reject-all parser fails these."),
    "eval-positive": ("not-vacuity-prone", "A reject-all parser fails these."),
    "query-evaluation": (
        "partly-scored",
        "A SPARQL QueryEvaluationTest is negative-shaped exactly when its "
        "expected result set is empty -- then a return-nothing engine "
        "passes it. Those are identified here by counting <result> "
        "elements in the expected .srx and scored with the same closure "
        "criterion applied to the test's data graph, when the test "
        "declares an entailment regime. Tests with non-empty expected "
        "results are not vacuity-prone and are not flagged.",
    ),
}

# ---------------------------------------------------------------------------
# Manifests. Each entry: (suite id, manifest path, kind).
#   kind "rdf-manifest"  parsed with the engine's own parser via `--dump`
# ---------------------------------------------------------------------------
SCORED_MANIFESTS = [
    ("rdf-mt", "third_party/testing/w3c/rdf/rdf11/rdf-mt/manifest.ttl"),
    ("rdf12-semantics", "third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl"),
    ("sparql11-entailment", "third_party/testing/w3c/sparql/sparql11/entailment/manifest.ttl"),
]

# Additional manifests swept for the census only.
CENSUS_MANIFEST_ROOTS = [
    "third_party/testing/w3c/rdf",
    "third_party/testing/w3c/sparql",
    "third_party/testing/shacl",
    "third_party/testing/shex",
]
CENSUS_MANIFEST_EXTRA = [
    "third_party/testing/owl/type-negative-entailment.rdf",
    "third_party/testing/owl/type-consistency.rdf",
    "third_party/testing/owl/type-inconsistency.rdf",
    "third_party/testing/owl/type-positive-entailment.rdf",
]

# How a declared entailment regime is handled. This mirrors
# `apply_entailment_regime` in bin/w3c-runner/w3c_runner.ml, which is the
# behaviour actually being measured:
#
#   "simple"                 -> triples unchanged
#   "OWL-RL" / "OWL-Direct"  -> owl_rl_closure_with_reflexivity
#   "RDF" / "RDFS"           -> rdfs_closure
#   anything else            -> triples unchanged
#
# The third column of each entry is the `factoidal entail --regime` value
# that reaches the same F* closure function.
CLOSURE_REGIMES = {
    "RDF": "RDFS",
    "RDFS": "RDFS",
    "OWL-RL": "OWL-RL",
    "OWL-Direct": "OWL-RL",
}
NO_CLOSURE_BY_DEFINITION = {"simple"}
# Regimes the engine implements through something other than graph closure
# (D-entailment through literal value equality; RIF through the RIF rule
# engine). Closure growth is the wrong lens for these, so they are recorded
# unscored with the reason rather than called vacuous.
NON_CLOSURE_REGIME_NOTE = (
    "the engine does not implement this regime as a graph closure "
    "(D-entailment is handled by literal value equality, RIF by the RIF "
    "rule engine), so closure growth is the wrong measurement and no "
    "criterion for it is defined here"
)


# ---------------------------------------------------------------------------
# N-Triples handling.
#
# Deliberately minimal: this splits already-serialised N-Triples lines into
# three fields for set arithmetic. It is not an RDF parser and never sees a
# concrete RDF syntax -- every RDF file in this tool is read by the engine.
# ---------------------------------------------------------------------------
NT_LINE = re.compile(
    r"^\s*(?P<s><[^>\s]*>|_:[^\s]+)\s+(?P<p><[^>\s]*>)\s+(?P<o>.+?)\s*\.\s*$"
)


def nt_split(text):
    """Split N-Triples text into (triples, skipped_lines).

    A line is skipped when it does not match the N-Triples grammar shape.
    That happens today for literals the serializer emits with raw newlines
    and unescaped quotes (see the OWL catalogs). Skips are counted and
    reported so they can never pass unnoticed.
    """
    triples = []
    skipped = 0
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        m = NT_LINE.match(line)
        if m:
            triples.append((m.group("s"), m.group("p"), m.group("o")))
        else:
            skipped += 1
    return triples, skipped


def has_bnode(t):
    return t[0].startswith("_:") or t[2].startswith("_:")


# ---------------------------------------------------------------------------
# Engine invocation. Every RDF read and every derivation comes from here.
# ---------------------------------------------------------------------------
class Engine:
    def __init__(self, binary, timeout=600):
        self.binary = binary
        self.timeout = timeout
        self._dump_cache = {}
        self._closure_cache = {}
        self.calls = 0

    def _run(self, args):
        self.calls += 1
        try:
            r = subprocess.run(
                [self.binary] + args,
                capture_output=True,
                text=True,
                timeout=self.timeout,
                cwd=REPO_ROOT,
            )
        except subprocess.TimeoutExpired:
            return None, "timeout after %ds" % self.timeout
        if r.returncode != 0:
            return None, (r.stderr or r.stdout or "").strip()[:400]
        return r.stdout, None

    def dump(self, path):
        if path not in self._dump_cache:
            self._dump_cache[path] = self._run(["--dump", path])
        return self._dump_cache[path]

    def closure(self, path, regime):
        key = (path, regime)
        if key not in self._closure_cache:
            self._closure_cache[key] = self._run(
                ["entail", "--data", path, "--regime", regime]
            )
        return self._closure_cache[key]


# ---------------------------------------------------------------------------
# Manifest reading (via the engine).
# ---------------------------------------------------------------------------
def read_manifest(engine, path):
    """Return (subject -> predicate -> [objects], skipped_lines, error)."""
    out, err = engine.dump(path)
    if out is None:
        return None, 0, err
    triples, skipped = nt_split(out)
    po = collections.defaultdict(lambda: collections.defaultdict(list))
    for s, p, o in triples:
        po[s.strip("<>")][p.strip("<>")].append(o)
    return po, skipped, None


def lit_value(o):
    """Lexical form of an N-Triples literal, or None if it is not a literal."""
    if not o.startswith('"'):
        return None
    end = o.rfind('"')
    if end <= 0:
        return None
    return o[1:end]


def iri_value(o):
    return o[1:-1] if o.startswith("<") and o.endswith(">") else None


def file_path_of(iri):
    """Map a file:// IRI back to a repo-relative path, or None."""
    if not iri or not iri.startswith("file://"):
        return None
    p = iri[len("file://") :]
    if p.startswith(REPO_ROOT + "/"):
        return p[len(REPO_ROOT) + 1 :]
    return p


RDF_NIL = RDF + "nil"


def rdf_list(po, node, depth=0):
    """Flatten an RDF collection into its member terms.

    `sd:entailmentRegime` in the SPARQL entailment manifest is sometimes a
    single IRI and sometimes an RDF list of them. This walks rdf:first /
    rdf:rest over the already-parsed manifest triples; it does not parse
    any RDF syntax.
    """
    key = node.strip("<>")
    if depth > 64 or key == RDF_NIL:
        return []
    d = po.get(key)
    if not d or (RDF + "first") not in d:
        return [node]
    out = list(d[RDF + "first"])
    for nxt in d.get(RDF + "rest", []):
        out.extend(rdf_list(po, nxt, depth + 1))
    return out


def classify(type_iris):
    """Return (class, polarity) for a manifest entry's rdf:type set."""
    best = None
    for t in type_iris:
        if t in TEST_TYPES:
            cls, pol = TEST_TYPES[t]
            # A negative/positive entailment classification beats the
            # companion ConsistencyTest type OWL catalogs also attach.
            if best is None or cls.startswith("entailment"):
                best = (cls, pol)
            continue
        local = t.split("#")[-1].split("/")[-1]
        for rx, val in LOCALNAME_RULES:
            if rx.search(local):
                if best is None:
                    best = val
                break
    return best


# ---------------------------------------------------------------------------
# The criterion.
# ---------------------------------------------------------------------------
def score_closure_test(engine, premise_path, conclusion_path, regime, baselines):
    """Apply the vacuity criterion to one closure-regime negative test."""
    rec = {
        "regime": regime,
        "premise": premise_path,
        "conclusion": conclusion_path,
    }
    cl_regime = CLOSURE_REGIMES[regime]

    p_out, p_err = engine.dump(premise_path)
    if p_out is None:
        rec.update(
            status="error",
            error_kind="premise-not-readable-through-the-cli",
            error="`factoidal --dump` refused the premise, so no closure "
            "measurement is possible for this test. The suite runner uses "
            "its own lenient loader, so the runner still scores the test; "
            "the disagreement between the two loaders is itself worth a "
            "look. CLI said: %s" % (p_err or "").replace("\n", " ")[:300],
        )
        return rec
    premise, p_skip = nt_split(p_out)
    premise_set = set(premise)

    c_out, c_err = engine.closure(premise_path, cl_regime)
    if c_out is None:
        rec.update(status="error", error="closure failed: %s" % c_err)
        return rec
    closure, c_skip = nt_split(c_out)
    closure_set = set(closure)

    rec["premise_triples"] = len(premise_set)
    rec["closure_triples"] = len(closure_set)
    rec["baseline_axioms"] = len(baselines[cl_regime])
    rec["premise_has_bnodes"] = any(has_bnode(t) for t in premise_set)
    rec["nt_lines_skipped"] = p_skip + c_skip

    # Self-check: every premise triple must reappear in the closure. If not,
    # the two invocations disagree on blank-node labels (or the closure
    # dropped input), and the set difference below cannot be trusted.
    missing = premise_set - closure_set
    rec["premise_subsumed"] = not missing
    if missing:
        rec.update(
            status="untrusted",
            reason="closure output does not contain %d premise triple(s); "
            "blank-node relabelling or input loss makes the set "
            "difference meaningless" % len(missing),
        )
        return rec

    derived = closure_set - premise_set - baselines[cl_regime]
    derived_ne = {t for t in derived if t[0] != t[2]}
    rec["derived"] = len(derived)
    rec["derived_non_reflexive"] = len(derived_ne)

    if not derived:
        rec.update(status="vacuous", reason="closure-adds-nothing")
        return rec

    # Conclusion predicates, for the relevance signal.
    concl_preds = set()
    if conclusion_path:
        k_out, k_err = engine.dump(conclusion_path)
        if k_out is None:
            rec["conclusion_error"] = k_err
        else:
            ctr, _ = nt_split(k_out)
            concl_preds = {t[1] for t in ctr}
            rec["conclusion_triples"] = len(set(ctr))
    rec["conclusion_predicates"] = len(concl_preds)

    if not derived_ne:
        rec.update(status="weak", reason="reflexive-only")
        return rec

    if not concl_preds:
        # No conclusion graph to compare against (a query-evaluation test
        # has none). The primary criterion is met; only the secondary
        # on-target refinement is unavailable. Say that, rather than
        # downgrading the verdict for a limit of the tool.
        rec.update(
            status="worked",
            relevance_checked=False,
            relevance_note="no conclusion graph exists for this test, so "
            "the on-target refinement could not run; the verdict rests on "
            "the premise-attributable, non-self-loop derivation count alone",
        )
        return rec
    on_target = {t for t in derived if t[1] in concl_preds}
    rec["derived_on_target"] = len(on_target)
    rec["relevance_checked"] = True
    if not on_target:
        rec.update(status="weak", reason="off-target")
        return rec
    rec.update(status="worked")
    return rec


def score_simple_test(engine, premise_path, conclusion_path):
    """Simple-regime negatives: exempt, with the substitute signal."""
    rec = {
        "regime": "simple",
        "premise": premise_path,
        "conclusion": conclusion_path,
        "status": "exempt",
        "exempt_reason": "regime-has-no-closure",
        "exempt_evidence": 'the test declares mf:entailmentRegime "simple"; '
        "simple entailment has no derivation rules, so an empty "
        "derivation set is correct rather than a defect",
    }
    p_out, _ = engine.dump(premise_path)
    c_out, _ = engine.dump(conclusion_path) if conclusion_path else (None, None)
    if p_out is None or c_out is None:
        rec["homomorphism_reached"] = None
        return rec
    pt, _ = nt_split(p_out)
    ct, _ = nt_split(c_out)
    pp = {t[1] for t in pt}
    cp = {t[1] for t in ct}
    shared = pp & cp
    rec["premise_triples"] = len(set(pt))
    rec["conclusion_triples"] = len(set(ct))
    rec["shared_predicates"] = len(shared)
    rec["homomorphism_reached"] = bool(shared)
    if not shared:
        rec["exempt_note"] = (
            "premise and conclusion share no predicate, so the "
            "non-entailment is decidable by a predicate scan and the "
            "homomorphism search never ran"
        )
    return rec


# ---------------------------------------------------------------------------
# Suite drivers.
# ---------------------------------------------------------------------------
def manifest_entry_set(po):
    """The subjects listed in the manifest's mf:entries collection.

    A vendored manifest can carry typed test entries that are commented out
    of mf:entries -- rdf-mt has three. The runner never sees those, so the
    audit must not count them in its denominator either.
    """
    listed = set()
    for subj, d in po.items():
        for o in d.get(MF + "entries", []):
            for term in rdf_list(po, o):
                v = iri_value(term)
                if v:
                    listed.add(v)
    return listed


def score_entailment_manifest(engine, suite, manifest, baselines):
    po, skipped, err = read_manifest(engine, manifest)
    if po is None:
        return {"suite": suite, "manifest": manifest, "error": err, "tests": []}

    listed = manifest_entry_set(po)
    tests = []
    counts = collections.Counter()
    for subj in sorted(po):
        d = po[subj]
        types = [iri_value(o) for o in d.get(TYPE, [])]
        types = [t for t in types if t]
        info = classify(types)
        if not info or info[0] != "entailment-negative":
            continue
        if listed and subj not in listed:
            # Typed but not in mf:entries: the runner never runs it.
            counts["not_in_manifest_entries"] += 1
            continue
        counts["negative_total"] += 1
        name_vals = d.get(MF + "name", [])
        name = lit_value(name_vals[0]) if name_vals else subj.split("#")[-1]
        regimes = [lit_value(o) for o in d.get(MF + "entailmentRegime", [])]
        regime = next((r for r in regimes if r), "simple")

        action = file_path_of(iri_value(d.get(MF + "action", [""])[0]))
        result_objs = d.get(MF + "result", [])
        result_iri = iri_value(result_objs[0]) if result_objs else None
        result_lit = lit_value(result_objs[0]) if result_objs else None
        conclusion = file_path_of(result_iri)

        rec = {"id": subj, "name": name, "class": "entailment-negative"}

        if action is None or not os.path.exists(os.path.join(REPO_ROOT, action)):
            rec.update(status="error", error="premise file not found", regime=regime)
        elif conclusion is None:
            # mf:result is the boolean false, not a conclusion graph.
            rec.update(
                regime=regime,
                premise=action,
                conclusion=None,
                mf_result_literal=result_lit,
                status="vacuous",
                reason="no-conclusion-and-no-consistency-check",
                evidence="mf:result is the literal %r rather than a "
                "conclusion graph, so the test asserts the premise is "
                "consistent; the runner path for this shape only checks "
                "that the premise parses, so no engine behaviour can "
                "fail it" % result_lit,
            )
        elif regime in CLOSURE_REGIMES:
            rec.update(
                score_closure_test(engine, action, conclusion, regime, baselines)
            )
        elif regime in NO_CLOSURE_BY_DEFINITION:
            rec.update(score_simple_test(engine, action, conclusion))
        else:
            rec.update(
                regime=regime,
                premise=action,
                conclusion=conclusion,
                status="unscored",
                reason="regime-not-a-graph-closure",
                evidence=NON_CLOSURE_REGIME_NOTE,
            )
        tests.append(rec)
        counts[rec["status"]] += 1

    return {
        "suite": suite,
        "manifest": manifest,
        "nt_lines_skipped": skipped,
        "negative_total": counts["negative_total"],
        "negatives_typed_but_not_in_mf_entries": counts["not_in_manifest_entries"],
        "worked": counts["worked"],
        "weak": counts["weak"],
        "vacuous": counts["vacuous"],
        "exempt": counts["exempt"],
        "unscored": counts["unscored"],
        "untrusted": counts["untrusted"],
        "error": counts["error"],
        "tests": sorted(tests, key=lambda r: r["id"]),
    }


SRX_RESULT = re.compile(r"<result[\s>/]")


def score_sparql_entailment(engine, suite, manifest, baselines):
    """SPARQL QueryEvaluationTests are negative-shaped when the expected
    result set is empty: a return-nothing engine passes them. Identified by
    counting <result> elements in the expected .srx (a syntactic scan of the
    expected-results document, not a query run)."""
    po, skipped, err = read_manifest(engine, manifest)
    if po is None:
        return {"suite": suite, "manifest": manifest, "error": err, "tests": []}

    QT = "http://www.w3.org/2001/sw/DataAccess/tests/test-query#"
    SD = "http://www.w3.org/ns/sparql-service-description#"
    tests = []
    counts = collections.Counter()
    total_qe = 0
    for subj in sorted(po):
        d = po[subj]
        types = [iri_value(o) for o in d.get(TYPE, [])]
        if (MF + "QueryEvaluationTest") not in [t for t in types if t]:
            continue
        total_qe += 1
        result_path = file_path_of(iri_value(d.get(MF + "result", [""])[0]))
        if not result_path:
            continue
        abs_res = os.path.join(REPO_ROOT, result_path)
        if not os.path.exists(abs_res):
            continue
        with open(abs_res, "r", errors="replace") as fh:
            body = fh.read()
        n_results = len(SRX_RESULT.findall(body))
        if n_results:
            continue  # non-empty expected results: not vacuity-prone
        counts["negative_total"] += 1
        name_vals = d.get(MF + "name", [])
        name = lit_value(name_vals[0]) if name_vals else subj.split("#")[-1]

        # The data graph + regime hang off the mf:action blank node.
        action_node = d.get(MF + "action", [""])[0].strip("<>")
        ad = po.get(action_node, {})
        data = file_path_of(iri_value((ad.get(QT + "data") or [""])[0]))
        # sd:entailmentRegime values are IRIs under http://www.w3.org/ns/
        # entailment/ -- Simple, RDF, RDFS, D, OWL-Direct, OWL-RDF-Based,
        # RIF. The local name is the same label rdf-mt uses in its
        # mf:entailmentRegime literal, so the same regime table applies.
        regime_terms = []
        for o in ad.get(SD + "entailmentRegime", []):
            regime_terms.extend(rdf_list(po, o))
        regimes = [iri_value(o) for o in regime_terms]
        labels = [r.rstrip("/").rsplit("/", 1)[-1] for r in regimes if r]
        # A test may list several regimes it is valid under. Prefer the
        # strongest one this engine implements as a closure, since that is
        # the code path the suite runner exercises.
        regime = next((x for x in labels if x in CLOSURE_REGIMES), None)
        if regime is None:
            regime = next(
                (x for x in labels if x in NO_CLOSURE_BY_DEFINITION), None
            )
        if regime is None and labels:
            regime = labels[0]
        rec = {
            "id": subj,
            "name": name,
            "class": "query-evaluation-empty-expected",
            "expected_solutions": 0,
            "declared_regimes": sorted(labels),
        }
        if not data or not os.path.exists(os.path.join(REPO_ROOT, data)):
            rec.update(status="error", error="data graph not found: %r" % data)
        elif regime in CLOSURE_REGIMES:
            rec.update(score_closure_test(engine, data, None, regime, baselines))
        elif regime in NO_CLOSURE_BY_DEFINITION:
            rec.update(
                regime=regime,
                premise=data,
                status="exempt",
                exempt_reason="regime-has-no-closure",
                exempt_evidence="the test declares sd:entailmentRegime "
                "ent:Simple; simple entailment has no derivation rules",
            )
        else:
            rec.update(
                regime=regime,
                premise=data,
                status="unscored",
                reason="regime-not-a-graph-closure",
                evidence=NON_CLOSURE_REGIME_NOTE,
            )
        tests.append(rec)
        counts[rec["status"]] += 1

    return {
        "suite": suite,
        "manifest": manifest,
        "nt_lines_skipped": skipped,
        "query_evaluation_total": total_qe,
        "negative_total": counts["negative_total"],
        "worked": counts["worked"],
        "weak": counts["weak"],
        "vacuous": counts["vacuous"],
        "exempt": counts["exempt"],
        "unscored": counts["unscored"],
        "untrusted": counts["untrusted"],
        "error": counts["error"],
        "tests": sorted(tests, key=lambda r: r["id"]),
    }


# ---------------------------------------------------------------------------
# Census.
# ---------------------------------------------------------------------------
def discover_manifests():
    found = []
    for root in CENSUS_MANIFEST_ROOTS:
        base = os.path.join(REPO_ROOT, root)
        if not os.path.isdir(base):
            continue
        for dirpath, _dirnames, filenames in os.walk(base):
            for fn in filenames:
                if fn.startswith("manifest") and fn.endswith((".ttl", ".n3")):
                    p = os.path.join(dirpath, fn)
                    found.append(os.path.relpath(p, REPO_ROOT))
    for extra in CENSUS_MANIFEST_EXTRA:
        if os.path.exists(os.path.join(REPO_ROOT, extra)):
            found.append(extra)
    return sorted(set(found))


def census(engine, manifests):
    rows = []
    for man in manifests:
        po, skipped, err = read_manifest(engine, man)
        if po is None:
            rows.append(
                {"manifest": man, "error": err, "classes": {}, "entries": 0}
            )
            continue
        classes = collections.Counter()
        entries = 0
        for subj, d in po.items():
            types = [iri_value(o) for o in d.get(TYPE, [])]
            types = [t for t in types if t]
            if not types:
                continue
            info = classify(types)
            if not info:
                continue
            entries += 1
            classes[info[0]] += 1
        if not entries:
            continue
        rows.append(
            {
                "manifest": man,
                "entries": entries,
                "nt_lines_skipped": skipped,
                "classes": dict(sorted(classes.items())),
            }
        )
    return rows


def summarise_census(rows):
    """Roll census rows up per class, with the reason each is or is not
    scored, and the manifest-level anti-vacuity witness for syntax-shaped
    classes."""
    per_class = collections.Counter()
    denom = 0
    for r in rows:
        for c, n in r.get("classes", {}).items():
            per_class[c] += n
        denom += r.get("entries", 0)

    # positive_siblings: for every manifest holding syntax-shaped negatives,
    # how many positive syntax/eval tests sit alongside them. A reject-all
    # parser fails all of those, so a manifest with positive siblings cannot
    # be scored by a degenerate parser.
    neg_syntax_manifests = 0
    neg_syntax_with_siblings = 0
    for r in rows:
        cs = r.get("classes", {})
        neg = cs.get("syntax-negative", 0) + cs.get("eval-negative", 0)
        if not neg:
            continue
        neg_syntax_manifests += 1
        if cs.get("syntax-positive", 0) + cs.get("eval-positive", 0):
            neg_syntax_with_siblings += 1

    out = []
    for cls in sorted(per_class):
        scored, reason = CENSUS_CLASSES.get(
            cls, ("scored", "scored with the closure criterion")
        )
        row = {
            "class": cls,
            "count": per_class[cls],
            "denominator_all_classified_entries": denom,
            "scored": scored,
            "reason": reason,
        }
        if cls in ("syntax-negative", "eval-negative"):
            row["manifests_holding_this_class"] = neg_syntax_manifests
            row["manifests_with_positive_siblings"] = neg_syntax_with_siblings
        out.append(row)
    return out


# ---------------------------------------------------------------------------
# Reporting.
# ---------------------------------------------------------------------------
def markdown_report(doc):
    L = []
    L.append("# Negative-test vacuity check (issue #333)\n")
    L.append(
        "A negative test asserts a non-entailment. An engine that derives "
        "nothing passes every one of them for free. This table says how "
        "many negative tests the engine actually did work on.\n"
    )
    L.append("## Scored: entailment-shaped negatives\n")
    cols = ["worked", "weak", "vacuous", "exempt", "unscored", "untrusted", "error"]
    L.append(
        "| suite | negative tests | " + " | ".join(cols) + " |"
    )
    L.append("|---|---:|" + "|".join(["---:"] * len(cols)) + "|")
    tot = collections.Counter()
    for s in doc["scored_suites"]:
        L.append(
            "| %s | %d | %s |"
            % (
                s["suite"],
                s.get("negative_total", 0),
                " | ".join(str(s.get(c, 0)) for c in cols),
            )
        )
        tot["negative_total"] += s.get("negative_total", 0)
        for c in cols:
            tot[c] += s.get(c, 0)
    L.append(
        "| **all scored suites** | **%d** | %s |"
        % (
            tot["negative_total"],
            " | ".join("**%d**" % tot[c] for c in cols),
        )
    )
    L.append("")
    L.append(
        "Read as: %d negative tests examined; %d did premise-attributable, "
        "on-target work; %d did only weak work; %d are vacuous; %d are "
        "exempt on a data-derived ground; %d unscored (no criterion "
        "defined for their regime); %d untrusted; %d errored (out of %d)."
        % (
            tot["negative_total"],
            tot["worked"],
            tot["weak"],
            tot["vacuous"],
            tot["exempt"],
            tot["unscored"],
            tot["untrusted"],
            tot["error"],
            tot["negative_total"],
        )
    )
    L.append("")

    L.append("## Vacuous tests, by name\n")
    any_v = False
    for s in doc["scored_suites"]:
        vs = [t for t in s["tests"] if t.get("status") == "vacuous"]
        if not vs:
            continue
        any_v = True
        L.append("### %s (%d vacuous out of %d negative)\n" % (s["suite"], len(vs), s.get("negative_total", 0)))
        L.append("| test | regime | reason | premise triples | derived |")
        L.append("|---|---|---|---:|---:|")
        for t in vs:
            L.append(
                "| `%s` | %s | %s | %s | %s |"
                % (
                    t.get("name", t["id"]),
                    t.get("regime", "-"),
                    t.get("reason", "-"),
                    t.get("premise_triples", "-"),
                    t.get("derived", 0),
                )
            )
        L.append("")
    if not any_v:
        L.append(
            "None reported. Be suspicious of the checker before believing "
            "this: re-read the criterion and confirm the baseline "
            "subtraction is running.\n"
        )

    L.append("## Weak tests, by name\n")
    for s in doc["scored_suites"]:
        ws = [t for t in s["tests"] if t.get("status") == "weak"]
        if not ws:
            continue
        L.append("### %s (%d weak)\n" % (s["suite"], len(ws)))
        L.append("| test | regime | reason | derived | non-reflexive | on-target |")
        L.append("|---|---|---|---:|---:|---:|")
        for t in ws:
            L.append(
                "| `%s` | %s | %s | %s | %s | %s |"
                % (
                    t.get("name", t["id"]),
                    t.get("regime", "-"),
                    t.get("reason", "-"),
                    t.get("derived", "-"),
                    t.get("derived_non_reflexive", "-"),
                    t.get("derived_on_target", "-"),
                )
            )
        L.append("")

    L.append("## Tests where the engine did work, with the numbers\n")
    L.append(
        "| suite | test | regime | premise | closure | derived | non-reflexive | on-target | relevance checked |"
    )
    L.append("|---|---|---|---:|---:|---:|---:|---:|---|")
    for s in doc["scored_suites"]:
        for t in s["tests"]:
            if t.get("status") != "worked":
                continue
            L.append(
                "| %s | `%s` | %s | %s | %s | %s | %s | %s | %s |"
                % (
                    s["suite"],
                    t.get("name", t["id"])[:60],
                    t.get("regime", "-"),
                    t.get("premise_triples", "-"),
                    t.get("closure_triples", "-"),
                    t.get("derived", "-"),
                    t.get("derived_non_reflexive", "-"),
                    t.get("derived_on_target", "n/a"),
                    "yes" if t.get("relevance_checked") else "no",
                )
            )
    L.append("")

    L.append("## Exemptions, with the data property each rests on\n")
    L.append("| suite | test | exemption | evidence |")
    L.append("|---|---|---|---|")
    for s in doc["scored_suites"]:
        for t in s["tests"]:
            if t.get("status") != "exempt":
                continue
            L.append(
                "| %s | `%s` | %s | %s |"
                % (
                    s["suite"],
                    t.get("name", t["id"]),
                    t.get("exempt_reason", "-"),
                    t.get("exempt_evidence", "-"),
                )
            )
    L.append("")

    L.append("## Unscored and errored tests, with the reason\n")
    L.append("| suite | test | status | reason |")
    L.append("|---|---|---|---|")
    for s in doc["scored_suites"]:
        for t in s["tests"]:
            if t.get("status") not in ("unscored", "error", "untrusted"):
                continue
            L.append(
                "| %s | `%s` | %s | %s |"
                % (
                    s["suite"],
                    t.get("name", t["id"])[:70],
                    t.get("status"),
                    (t.get("evidence") or t.get("error") or t.get("reason") or "-")
                    .replace("|", "/")
                    .replace("\n", " ")[:300],
                )
            )
    L.append("")

    L.append("## Side findings (engine behaviour noticed while measuring)\n")
    for f in doc.get("side_findings", []):
        L.append("- **%s** — %s" % (f["id"], f["what"]))
        L.append("  - effect here: %s" % f.get("impact_on_this_tool", "-"))
    L.append("")

    L.append("## Census: every negative-style class found in the vendored manifests\n")
    L.append("| class | count | of all classified entries | scored | why |")
    L.append("|---|---:|---:|---|---|")
    for r in doc["census_summary"]:
        L.append(
            "| %s | %d | %d | %s | %s |"
            % (
                r["class"],
                r["count"],
                r["denominator_all_classified_entries"],
                r["scored"],
                r["reason"].replace("|", "/"),
            )
        )
    L.append("")
    return "\n".join(L)


# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument(
        "--factoidal",
        default=os.path.join(REPO_ROOT, "bin", "linux-x86_64", "factoidal"),
        help="path to the factoidal CLI (the engine under test)",
    )
    ap.add_argument(
        "--out",
        default=os.path.join(
            REPO_ROOT, "docs", "test-results", "by-suite", "negative-test-vacuity.json"
        ),
    )
    ap.add_argument("--markdown", help="also write a markdown report here")
    ap.add_argument("--census-only", action="store_true")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument(
        "--fail-on-vacuous",
        action="store_true",
        help="exit 1 when any vacuous negative test is found. OFF by "
        "default: the number is a finding to track, not a gate, until "
        "the RDFS rule gaps it exposes are closed.",
    )
    args = ap.parse_args()

    if not os.path.exists(args.factoidal):
        print("error: factoidal binary not found at %s" % args.factoidal, file=sys.stderr)
        return 2
    engine = Engine(args.factoidal, timeout=args.timeout)

    # Regime axiom baselines: closure of the EMPTY graph. Everything the
    # engine emits from nothing is premise-independent and must not count as
    # work on any test's premise.
    fd, empty = tempfile.mkstemp(suffix=".nt", prefix="vacuity-empty-")
    os.close(fd)
    baselines = {}
    try:
        for regime in ("RDFS", "OWL-RL"):
            out, err = engine.closure(empty, regime)
            if out is None:
                print(
                    "error: baseline closure for %s failed: %s" % (regime, err),
                    file=sys.stderr,
                )
                return 2
            triples, _ = nt_split(out)
            baselines[regime] = set(triples)
    finally:
        os.remove(empty)

    doc = {
        "tool": "tools/negative-test-vacuity.py",
        "schema_version": 1,
        "issue": "https://github.com/danbri/factoidal/issues/333",
        "criterion": {
            "summary": "For a negative entailment test with premise G, "
            "conclusion C and regime R, the engine did premise-attributable "
            "work iff closure_R(G) minus (G union closure_R(empty)) is "
            "non-empty. Self-loop triples (subject == object) are excluded "
            "from that set. A derivation counts as on-target iff it carries "
            "a predicate that occurs in C.",
            "statuses": {
                "worked": "premise-attributable, non-self-loop derivations "
                "exist AND at least one carries a predicate occurring in the "
                "conclusion. When the test has no conclusion graph at all (a "
                "query-evaluation test), the second half cannot be checked "
                "and the record carries relevance_checked: false",
                "weak": "derivations exist but are reflexive-only or off-target",
                "vacuous": "closure of the premise adds nothing beyond the regime axioms",
                "exempt": "closure-free regime, exempted on a stated data property",
                "untrusted": "the engine's own output failed the tool's self-check",
                "error": "premise or closure could not be obtained",
            },
            "false_positive_modes": [
                "a premise so small that a complete implementation of the "
                "regime would also derive nothing beyond axioms and "
                "reflexivity",
            ],
            "false_negative_modes": [
                "predicate overlap is coarse: a closure can derive many "
                "triples sharing a predicate with C without exercising the "
                "rule that could produce C",
                "no check that C is reachable in principle under a complete "
                "implementation of R (that needs rule knowledge, which "
                "would put entailment logic in a runner)",
            ],
        },
        "baselines": {
            k: {"regime": k, "axiom_triples": len(v)} for k, v in baselines.items()
        },
        "scored_suites": [],
        "census_summary": [],
        "census_manifests": [],
        "side_findings": [
            {
                "id": "ntriples-serializer-does-not-escape-literals",
                "what": "`factoidal --dump` emits literals containing a "
                "newline or a double quote verbatim, instead of as the "
                "\\n and \\\" escapes the N-Triples grammar requires. The "
                "output is therefore not re-readable as N-Triples for any "
                "graph with such a literal.",
                "reproduce": "echo '<http://e/s> <http://e/p> "
                "\"a\\\\nb\" .' > t.nt && factoidal --dump t.nt",
                "impact_on_this_tool": "manifest lines carrying multi-line "
                "rdfs:comment or embedded-ontology literals cannot be "
                "split into triples and are counted in nt_lines_skipped. "
                "It is why the OWL 2 catalogs are censused but not scored. "
                "It does not affect any verdict here: every predicate this "
                "tool reads (rdf:type, mf:action, mf:result, "
                "mf:entailmentRegime, mf:entries, sd:entailmentRegime) has "
                "an IRI or a single-line literal object.",
                "not_fixed_here": "fixing the serializer changes engine "
                "output, and this tool is not allowed to change engine "
                "behaviour or any suite's score",
            },
            {
                "id": "cli-and-runner-loaders-disagree-on-malformed-literals",
                "what": "third_party/testing/w3c/rdf/rdf12/rdf-semantics/"
                "malformed-literal.ttl is rejected by `factoidal --dump` "
                "under the issue-325 zero-triples guard, while the suite "
                "runner's own loader accepts it and scores the two tests "
                "that use it as their premise.",
                "impact_on_this_tool": "those two tests are recorded "
                "`error`, not vacuous — the tool cannot measure what it "
                "cannot load.",
            },
        ],
    }

    if not args.census_only:
        for suite, man in SCORED_MANIFESTS:
            if not os.path.exists(os.path.join(REPO_ROOT, man)):
                doc["scored_suites"].append(
                    {"suite": suite, "manifest": man, "error": "manifest missing", "tests": []}
                )
                continue
            if suite == "sparql11-entailment":
                doc["scored_suites"].append(
                    score_sparql_entailment(engine, suite, man, baselines)
                )
            else:
                doc["scored_suites"].append(
                    score_entailment_manifest(engine, suite, man, baselines)
                )

    manifests = discover_manifests()
    rows = census(engine, manifests)
    doc["census_manifests"] = rows
    doc["census_summary"] = summarise_census(rows)

    # Dashboard-convention totals, alongside the detail above. `pass` and
    # `fail` here do NOT mean a suite passed or failed -- no engine
    # behaviour and no suite score is affected by this tool. `metric` spells
    # out what each number counts, per anti-pattern #3 and #25.
    tot = collections.Counter()
    for s in doc["scored_suites"]:
        for k in (
            "negative_total",
            "worked",
            "weak",
            "vacuous",
            "exempt",
            "unscored",
            "untrusted",
            "error",
        ):
            tot[k] += s.get(k, 0)
    skip = tot["weak"] + tot["exempt"] + tot["unscored"] + tot["untrusted"] + tot["error"]
    doc.update(
        {
            "suite": "negative-test-vacuity",
            "spec": "internal — vacuity audit of negative-style W3C tests",
            "runner": "tools/negative-test-vacuity.py",
            "present": True,
            "metric": "pass = negative tests on which the engine did "
            "premise-attributable, non-self-loop, on-target derivation; "
            "fail = negative tests that are VACUOUS (the engine derives "
            "nothing the test could catch, so the test cannot go red); "
            "skip = weak + exempt + unscored + untrusted + error, broken "
            "out in skip_breakdown. This tool measures; it changes no "
            "engine behaviour and no other suite's score.",
            "pass": tot["worked"],
            "fail": tot["vacuous"],
            "skip": skip,
            "total": tot["negative_total"],
            "skip_breakdown": {
                "weak": tot["weak"],
                "exempt": tot["exempt"],
                "unscored": tot["unscored"],
                "untrusted": tot["untrusted"],
                "error": tot["error"],
            },
        }
    )
    doc["run"] = {
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime(
            "%Y-%m-%d %H:%M UTC"
        ),
        "engine_invocations": engine.calls,
        "manifests_censused": len(rows),
    }

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w") as fh:
        json.dump(doc, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("wrote %s" % args.out)

    md = markdown_report(doc)
    if args.markdown:
        with open(args.markdown, "w") as fh:
            fh.write(md)
        print("wrote %s" % args.markdown)
    print()
    print(md)

    vac = sum(s.get("vacuous", 0) for s in doc["scored_suites"])
    if args.fail_on_vacuous and vac:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
