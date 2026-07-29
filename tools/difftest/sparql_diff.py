#!/usr/bin/env python3
"""
SPARQL evaluation differential harness (issue #317, gate 4).

For each generated Doc (graph profile), serialize to N-Triples (the one
format the RDF harness found zero disagreements on -- so any difference
found here is attributable to QUERY EVALUATION, not to a parsing
divergence already tracked separately in rdf_diff.py), run the battery
from sparqlgen.py against:
  - factoidal (`factoidal query -o json`)
  - rdflib   (pure-Python, independent SPARQL implementation)
  - pyoxigraph / Oxigraph (Rust, independent SPARQL implementation)

SELECT rows are compared as sets after a per-table, first-seen-order
blank-node relabeling (blank node IDENTITY is not meaningful across
independent engines, only the graph SHAPE is -- this is a documented
approximation, not full result-set isomorphism, see the ledger).
ASK compares booleans directly. CONSTRUCT is compared via RDFC-1.0
canonicalization of the constructed graph (same method as rdf_diff.py).
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from collections import Counter

import rdfgen
import sparqlgen
import compare

FACTOIDAL_BIN = os.environ.get(
    "FACTOIDAL_BIN",
    os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "bin", "linux-x86_64", "factoidal"),
)

try:
    import pyoxigraph as ox
except ImportError:
    ox = None
try:
    import rdflib
except ImportError:
    rdflib = None


def _sort_key(x):
    """Robust sort key for the nested tuples-with-None term/row structures
    below: json.dumps total-orders any mix of str/None/int/nested-tuple
    without Python's native '<' choking on e.g. None-vs-str (which it does
    the moment two rows share a value but differ in whether a sibling
    field is None -- hit live at fuzzing scale: an OPTIONAL-unmatched
    variable's term or a literal's (datatype, lang) pair with one side
    None is exactly this shape)."""
    return json.dumps(x, sort_keys=True, default=str)


XSD_STRING = "http://www.w3.org/2001/XMLSchema#string"


def term_key(kind, value, extra=None):
    """extra, for literals, is (datatype_or_None, lang_or_None). Normalize
    so an implicit xsd:string (datatype omitted, e.g. Factoidal's JSON) and
    an explicit one (e.g. pyoxigraph always fills it in) compare equal --
    they are the SAME literal per RDF 1.1 Concepts sec 3.3 ("a literal
    without ... a language tag has the datatype IRI xsd:string"), and fold
    language-tag case (known cross-implementation ambiguity, tracked
    separately in the ledger -- see rdf_diff.py's compare.py classifier;
    this harness only needs to not let it masquerade as a QUERY bug)."""
    if kind == "literal" and extra is not None:
        dt, lang = extra
        if lang:
            dt = None
            lang = lang.lower()
        elif dt is None:
            dt = XSD_STRING
        extra = (dt, lang)
    return (kind, value, extra)


def _canonical_bnode_labels(rows: list) -> dict:
    """Iterative-refinement (Weisfeiler-Leman-style) canonical labeling of
    the blank-node VALUES appearing in a result table -- the same idea
    RDFC-1.0 applies to graphs, applied here to result rows, because a
    result table's row ORDER is unspecified by SPARQL and a bnode's raw
    identifier is engine-private: neither is safe to compare directly, but
    the multiset of (variable, row-context) each bnode appears in IS a
    property of the query's actual answer, and converges to a stable
    canonical label after a couple of refinement rounds. Adequate for the
    small distinct-bnode counts these fuzz queries produce -- NOT a claim
    of general graph-isomorphism-hardness-proof soundness; documented
    limitation, see the ledger."""
    bnodes = set()
    for row in rows:
        for term in row.values():
            if term[0] == "bnode":
                bnodes.add(term[1])
    if not bnodes:
        return {}

    label = {b: "0" for b in bnodes}
    for _round in range(3):
        sig_of = {b: [] for b in bnodes}
        for row in rows:
            row_bnodes = [(var, term[1]) for var, term in row.items() if term[0] == "bnode"]
            if not row_bnodes:
                continue
            ctx = tuple(sorted(
                (
                    (var, (term[0], label.get(term[1], term[1]) if term[0] == "bnode" else term[1], term[2]))
                    for var, term in row.items()
                ),
                key=_sort_key,
            ))
            for _var, b in row_bnodes:
                sig_of[b].append(ctx)
        new_sig = {b: tuple(sorted(sig_of[b], key=_sort_key)) for b in bnodes}
        uniq = sorted(set(new_sig.values()), key=_sort_key)
        rank = {sig: i for i, sig in enumerate(uniq)}
        label = {b: str(rank[new_sig[b]]) for b in bnodes}
    return label


def normalize_table(rows: list) -> list:
    """rows: list of dict[var] -> (kind, value, extra). Returns a sorted
    list of row-tuples after relabeling blank nodes to their canonical
    (iterative-refinement) label, so tables from different engines with
    arbitrary-but-internally-consistent bnode identifiers, in arbitrary
    row order, compare equal iff they represent the same answer."""
    labels = _canonical_bnode_labels(rows)

    def relabel(term):
        kind, value, extra = term
        if kind == "bnode":
            return (kind, f"_:wl{labels.get(value, value)}", extra)
        return term

    out = []
    for row in rows:
        relabeled = tuple(sorted(((var, relabel(term)) for var, term in row.items()), key=_sort_key))
        out.append(relabeled)
    return sorted(out, key=_sort_key)


def run_factoidal_select(data_path: str, query_text: str, timeout: int = 20):
    try:
        r = subprocess.run(
            [FACTOIDAL_BIN, "query", "-d", data_path, "-e", query_text, "-o", "json"],
            capture_output=True, text=True, encoding="utf-8", timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, "TIMEOUT"
    if r.returncode != 0:
        return None, f"rc={r.returncode} err={r.stderr.strip()[:300]!r}"
    try:
        payload = json.loads(r.stdout)
    except json.JSONDecodeError as e:
        return None, f"bad JSON from factoidal: {e}; stdout={r.stdout[:300]!r}"
    if "boolean" in payload:
        return ("ask", payload["boolean"]), None
    rows = []
    for b in payload["results"]["bindings"]:
        row = {}
        for var, term in b.items():
            if term["type"] == "uri":
                row[var] = term_key("uri", term["value"])
            elif term["type"] == "bnode":
                row[var] = term_key("bnode", term["value"])
            else:
                row[var] = term_key("literal", term["value"], (term.get("datatype"), term.get("xml:lang")))
        rows.append(row)
    return ("select", rows), None


def run_factoidal_construct(data_path: str, query_text: str, timeout: int = 20):
    try:
        r = subprocess.run(
            [FACTOIDAL_BIN, "query", "-d", data_path, "-e", query_text, "-o", "ntriples"],
            capture_output=True, text=True, encoding="utf-8", timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, "TIMEOUT"
    if r.returncode != 0:
        return None, f"rc={r.returncode} err={r.stderr.strip()[:300]!r}"
    return r.stdout, None


def run_rdflib(data_path: str, query_text: str, form: str):
    if rdflib is None:
        return None, "rdflib not installed"
    g = rdflib.Graph()
    try:
        g.parse(data_path, format="nt")
        qres = g.query(query_text)
    except Exception as e:  # noqa: BLE001 -- reference-side error is data
        return None, f"rdflib error: {e}"
    if form == "ask":
        return ("ask", bool(qres)), None
    if form == "construct":
        lines = []
        for s, p, o in qres:
            lines.append(_nt_line(s, p, o, rdflib_term=True))
        return "\n".join(lines), None
    rows = []
    for row in qres:
        d = row.asdict()
        conv = {}
        for var, term in d.items():
            conv[str(var)] = _rdflib_term_key(term)
        rows.append(conv)
    return ("select", rows), None


def _rdflib_term_key(term):
    import rdflib as rl
    if isinstance(term, rl.URIRef):
        return term_key("uri", str(term))
    if isinstance(term, rl.BNode):
        return term_key("bnode", str(term))
    dt = str(term.datatype) if term.datatype else None
    lang = term.language
    return term_key("literal", str(term), (dt, lang))


def _nt_line(s, p, o, rdflib_term=False):
    def fmt(t):
        import rdflib as rl
        if isinstance(t, rl.URIRef):
            return f"<{t}>"
        if isinstance(t, rl.BNode):
            return f"_:{t}"
        lit = f'"{str(t)}"'
        if t.language:
            lit += f"@{t.language}"
        elif t.datatype:
            lit += f"^^<{t.datatype}>"
        return lit
    return f"{fmt(s)} {fmt(p)} {fmt(o)} ."


def canonicalize_ntriples_text(nt_text: str, tmp_path: str) -> str:
    """RDFC-1.0-canonicalize a blob of N-Triples text via factoidal itself
    (writes to tmp_path first -- factoidal's CLI is file-based)."""
    with open(tmp_path, "w", encoding="utf-8") as f:
        f.write(nt_text)
    rc, out, err = None, "", ""
    r = subprocess.run(
        [FACTOIDAL_BIN, "canonicalize", tmp_path],
        capture_output=True, text=True, encoding="utf-8", timeout=20,
    )
    if r.returncode != 0:
        return None
    return r.stdout


def canonicalize_ntriples_text_pyox(nt_text: str) -> str:
    if ox is None or not nt_text.strip():
        return nt_text
    try:
        d = ox.Dataset(ox.parse(input=nt_text, format=ox.RdfFormat.N_TRIPLES))
        d.canonicalize(ox.CanonicalizationAlgorithm.RDFC_1_0)
    except Exception:  # noqa: BLE001
        return nt_text
    return "\n".join(str(q) for q in d)


def run_pyoxigraph(data_path: str, query_text: str, form: str):
    if ox is None:
        return None, "pyoxigraph not installed"
    store = ox.Store()
    try:
        store.bulk_load(path=data_path, format=ox.RdfFormat.N_TRIPLES)
        res = store.query(query_text)
    except Exception as e:  # noqa: BLE001
        return None, f"pyoxigraph error: {e}"
    if form == "ask":
        return ("ask", bool(res)), None
    if form == "construct":
        lines = [f"{q.subject} {q.predicate} {q.object} ." for q in res]
        return "\n".join(lines), None
    rows = []
    for row in res:
        d = {}
        for v in res.variables:
            name = str(v)[1:] if str(v).startswith("?") else str(v)
            term = row[v]
            d[name] = _pyox_term_key(term)
        rows.append(d)
    return ("select", rows), None


def _pyox_term_key(term):
    if term is None:
        return term_key("unbound", None)
    if isinstance(term, ox.NamedNode):
        return term_key("uri", term.value)
    if isinstance(term, ox.BlankNode):
        return term_key("bnode", term.value)
    dt = term.datatype.value if term.datatype else None
    lang = term.language
    return term_key("literal", term.value, (dt, lang))


def compare_select(rows_a, rows_b):
    na, nb = normalize_table(rows_a), normalize_table(rows_b)
    return na == nb, na, nb


def run_one(seed: int, size: str, out_dir: str, findings: list):
    doc = rdfgen.generate_graph(seed=seed, profile="graph", size=size)
    import random
    rng = random.Random(seed * 104729)
    nt_text = rdfgen.serialize_ntriples(doc, rng)
    inst_dir = os.path.join(out_dir, f"seed{seed}_{size}")
    os.makedirs(inst_dir, exist_ok=True)
    data_path = os.path.join(inst_dir, "data.nt")
    with open(data_path, "w", encoding="utf-8") as f:
        f.write(nt_text)
    inst_tmp_dir = inst_dir

    for name, query_text, form in sparqlgen.queries_for(doc):
        if form == "construct":
            fout, ferr = run_factoidal_construct(data_path, query_text)
        else:
            fout, ferr = run_factoidal_select(data_path, query_text)
        rout, rerr = run_rdflib(data_path, query_text, form)
        oout, oerr = run_pyoxigraph(data_path, query_text, form)

        entry = {"seed": seed, "size": size, "query": name, "form": form}
        if ferr:
            entry["disposition"] = "factoidal-error"
            entry["detail"] = ferr
            findings.append(entry)
            continue

        for ref_name, ref_out, ref_err in (("rdflib", rout, rerr), ("pyoxigraph", oout, oerr)):
            if ref_err:
                continue  # reference-side limitation, not our finding
            e2 = dict(entry)
            e2["reference"] = ref_name
            if form == "ask":
                if fout[1] != ref_out[1]:
                    e2["disposition"] = "disagreement"
                    e2["factoidal"] = fout[1]
                    e2["reference_value"] = ref_out[1]
                    findings.append(e2)
            elif form == "construct":
                us_canon = canonicalize_ntriples_text(fout, os.path.join(inst_tmp_dir, f"construct_{name}.nt")) or fout
                ref_canon = canonicalize_ntriples_text_pyox(ref_out)
                agree, only_us, only_ref = compare.diff_canonical(us_canon, ref_canon)
                if not agree:
                    if compare.is_only_langtag_case_difference(only_us, only_ref):
                        e2["disposition"] = "spec-ambiguous-langtag-case"
                        findings.append(e2)
                        continue
                    e2["disposition"] = "disagreement"
                    e2["only_factoidal"] = only_us[:10]
                    e2["only_reference"] = only_ref[:10]
                    if only_us and not only_ref:
                        e2["soundness_suspect"] = "factoidal CONSTRUCTed extra triples"
                    elif only_ref and not only_us:
                        e2["soundness_suspect"] = "factoidal DROPPED constructed triples"
                    findings.append(e2)
            else:  # select
                agree, na, nb = compare_select(fout[1], ref_out[1])
                if not agree:
                    e2["disposition"] = "disagreement"
                    e2["factoidal_rows"] = len(fout[1])
                    e2["reference_rows"] = len(ref_out[1])
                    e2["factoidal_sample"] = [dict(r) for r in na[:5]]
                    e2["reference_sample"] = [dict(r) for r in nb[:5]]
                    findings.append(e2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=30)
    ap.add_argument("--seed-base", type=int, default=5000)
    ap.add_argument("--out", default=".claude-runs/difftest/sparql-corpus")
    ap.add_argument("--sizes", default="small,medium")
    args = ap.parse_args()

    sizes = args.sizes.split(",")
    findings = []
    t0 = time.time()
    for i in range(args.n):
        seed = args.seed_base + i
        size = sizes[i % len(sizes)]
        run_one(seed, size, args.out, findings)
    elapsed = time.time() - t0

    by_disp = Counter(f.get("disposition", "?") for f in findings)
    by_query = Counter(f.get("query", "?") for f in findings if f.get("disposition") == "disagreement")

    report = {
        "harness": "sparql_diff",
        "n_instances": args.n,
        "elapsed_sec": round(elapsed, 1),
        "reference_implementations": ["rdflib", "pyoxigraph"],
        "findings": findings,
    }
    os.makedirs(args.out, exist_ok=True)
    report_path = os.path.join(args.out, "report.json")
    with open(report_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, default=str)

    print(f"instances={args.n} elapsed={elapsed:.1f}s")
    print(f"findings by disposition: {dict(by_disp)}")
    print(f"disagreements by query shape: {dict(by_query)}")
    print(f"report: {report_path}")


if __name__ == "__main__":
    main()
