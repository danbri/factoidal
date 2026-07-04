#!/usr/bin/env python3
"""Corpus-driven cross-backend SPARQL parity harness.

Runs every query in a manifest (queries.json) against every backend the
factoidal CLI exposes for the same fixture data:

  - in-memory:  factoidal query --data FIXTURE.nq ...
  - COTTAS:     factoidal query --data-cottas FIXTURE.cottas ...
                (artifact built on the fly from the .nq via the pycottas
                venv + DuckDB, PARQUET_VERSION V2 + DICTIONARY_SIZE_LIMIT 1,
                same writer as tests/local/graph_default_semantics_regressions.sh,
                cached in the workdir keyed by fixture content hash)

and reports, per query:

  PASS             all backends agree (and the optional `expect` holds
                   on the in-memory reference)
  DIVERGENT        backends disagree — per-backend row counts, digests,
                   and row-level differences are printed
  KNOWN-DIVERGENT  backends disagree but the manifest entry carries
                   `known_divergent` referencing an open issue (e.g.
                   "issue #267"); printed, not counted as failure
  EXPECT-FAIL      backends agree but the in-memory reference violates
                   the entry's `expect` — catches a bug shared by ALL
                   backends
  ERROR            a backend exited non-zero, timed out, or produced
                   unparseable output

Manifest schema (paths relative to the manifest file):

  {
    "fixtures": { "<fixture-name>": "fixtures/foo.nq", ... },
    "queries": [
      {
        "name": "unique-name",
        "fixture": "<fixture-name>",
        "query": "SELECT ...",
        "expect": { "rows": 3 } | { "boolean": true }
                 | { "single_value": "42" },          // optional
        "ordered": true,                              // optional: compare
                                                      // rows in order
                                                      // (ORDER BY queries)
        "known_divergent": "issue #267 — ..."         // optional: MUST
                                                      // reference an open
                                                      // issue as #NNN
      }, ...
    ]
  }

Policy (mirrors tests/beyond-w3c known_failures): `known_divergent` is
the only escape hatch, every entry must carry an issue number, and
removing the entry belongs in the same PR that fixes the bug.

stdlib only. Exit code: 0 iff no DIVERGENT / EXPECT-FAIL / ERROR.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

COMMAND_TIMEOUT_SECONDS = 600

# Same writer as tests/local/graph_default_semantics_regressions.sh,
# with one deviation: DICTIONARY_SIZE_LIMIT 0, not 1. With limit 1 a
# column holding exactly ONE distinct value (e.g. the g column of an
# all-default-graph fixture, or a single-predicate dataset's p column)
# still fits the dictionary and DuckDB emits RLE_DICTIONARY pages,
# which the F*-verified reader cannot decode — SELECT/COUNT then fail
# hard ("could not decode column N") and ASK silently answers false.
# Limit 0 disables dictionaries entirely, forcing the
# DeltaLengthByteArray pages the verified reader supports.
COTTAS_WRITER = r'''
import pathlib
import re
import sys

import duckdb

src, dst = sys.argv[1], sys.argv[2]
pat = re.compile(r'^(\S+)\s+(\S+)\s+(".*?"(?:\^\^\S+|@\S+)?|\S+)\s+(\S+)?\s*\.$')
rows = []
for line in pathlib.Path(src).read_text().splitlines():
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    m = pat.match(line)
    if m is None:
        sys.stderr.write("cottas writer: unparseable N-Quads line: %s\n" % line)
        sys.exit(2)
    rows.append((m.group(1), m.group(2), m.group(3), m.group(4) or "DEFAULT"))
con = duckdb.connect()
con.execute("CREATE TABLE t (s VARCHAR, p VARCHAR, o VARCHAR, g VARCHAR)")
con.executemany("INSERT INTO t VALUES (?,?,?,?)", rows)
con.execute(
    "COPY t TO '%s' (FORMAT PARQUET, COMPRESSION ZSTD, "
    "DICTIONARY_SIZE_LIMIT 0, PARQUET_VERSION V2)" % dst
)
'''


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


class CottasCache:
    """Build .cottas artifacts from .nq fixtures once, keyed by content."""

    def __init__(self, workdir, pycottas_python):
        self.workdir = workdir
        self.pycottas_python = pycottas_python
        self.writer_path = os.path.join(workdir, "_cottas_writer.py")
        with open(self.writer_path, "w") as f:
            f.write(COTTAS_WRITER)

    def artifact_for(self, fixture_name, nq_path):
        key = sha256_file(nq_path)[:12]
        out = os.path.join(self.workdir, "%s.%s.cottas" % (fixture_name, key))
        if os.path.exists(out):
            return out
        proc = subprocess.run(
            [self.pycottas_python, self.writer_path, nq_path, out],
            capture_output=True,
            text=True,
            timeout=COMMAND_TIMEOUT_SECONDS,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                "COTTAS build failed for %s (exit %d): %s"
                % (nq_path, proc.returncode, proc.stderr.strip())
            )
        return out


def run_query(bin_path, data_flag, data_file, query):
    """Run one query on one backend. Returns a parsed-result dict or
    {"error": message}."""
    cmd = [bin_path, "query", data_flag, data_file, "-e", query, "-o", "json"]
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=COMMAND_TIMEOUT_SECONDS
        )
    except subprocess.TimeoutExpired:
        return {"error": "timeout after %ds" % COMMAND_TIMEOUT_SECONDS}
    if proc.returncode != 0:
        return {
            "error": "exit %d: %s"
            % (proc.returncode, proc.stderr.strip()[:300] or proc.stdout.strip()[:300])
        }
    try:
        doc = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return {"error": "unparseable JSON output (%s): %r" % (exc, proc.stdout[:200])}
    if "boolean" in doc:
        return {"kind": "ask", "boolean": bool(doc["boolean"])}
    bindings = doc.get("results", {}).get("bindings", [])
    return {"kind": "select", "bindings": bindings}


def canonical_result(parsed, ordered):
    """Normalise a parsed result for cross-backend comparison.

    SELECT rows become lists of {var: [type, value, datatype, lang]}.
    Unless `ordered`, rows are sorted (multiset comparison). Blank-node
    labels are engine-internal, so they are canonically relabelled in
    first-occurrence order over the comparison order.
    """
    if parsed["kind"] == "ask":
        return {"kind": "ask", "boolean": parsed["boolean"]}
    rows = []
    for b in parsed["bindings"]:
        row = {}
        for var, val in b.items():
            row[var] = (
                val.get("type", ""),
                val.get("value", ""),
                val.get("datatype", ""),
                val.get("xml:lang", ""),
            )
        rows.append(row)

    def masked_key(row):
        return json.dumps(
            {
                v: (t, "_:" if t == "bnode" else s, d, l)
                for v, (t, s, d, l) in sorted(row.items())
            },
            sort_keys=True,
        )

    if ordered:
        order = list(range(len(rows)))
    else:
        order = sorted(range(len(rows)), key=lambda i: masked_key(rows[i]))
    label_map = {}
    out = []
    for i in order:
        row2 = {}
        for v, (t, s, d, l) in sorted(rows[i].items()):
            if t == "bnode":
                s = label_map.setdefault(s, "_:c%d" % len(label_map))
            row2[v] = [t, s, d, l]
        out.append(row2)
    return {"kind": "select", "rows": out}


def digest_of(canon):
    return hashlib.sha256(
        json.dumps(canon, sort_keys=True).encode()
    ).hexdigest()[:12]


def summarise_canon(canon):
    if canon["kind"] == "ask":
        return "boolean=%s" % str(canon["boolean"]).lower()
    return "rows=%d digest=%s" % (len(canon["rows"]), digest_of(canon))


def check_expect(expect, canon):
    """Check the manifest `expect` against the in-memory reference
    result. Returns None on success, else a failure message."""
    if "boolean" in expect:
        if canon["kind"] != "ask":
            return "expected ASK boolean=%s but result is a SELECT" % expect["boolean"]
        if canon["boolean"] != expect["boolean"]:
            return "expected boolean=%s, reference returned boolean=%s" % (
                str(expect["boolean"]).lower(),
                str(canon["boolean"]).lower(),
            )
        return None
    if canon["kind"] != "select":
        return "expected a SELECT result, got ASK"
    if "rows" in expect:
        if len(canon["rows"]) != expect["rows"]:
            return "expected rows=%d, reference returned rows=%d" % (
                expect["rows"],
                len(canon["rows"]),
            )
        return None
    if "single_value" in expect:
        if len(canon["rows"]) != 1:
            return "expected a single row, reference returned rows=%d" % len(
                canon["rows"]
            )
        bound = [cell for cell in canon["rows"][0].values() if cell[0] != ""]
        if len(bound) != 1:
            return "expected a single bound variable, got %d" % len(bound)
        if bound[0][1] != expect["single_value"]:
            return "expected value [%s], reference returned [%s]" % (
                expect["single_value"],
                bound[0][1],
            )
        return None
    return "unrecognised expect form: %r" % (expect,)


def print_row_diff(name_a, canon_a, name_b, canon_b, limit=5):
    if canon_a["kind"] != "select" or canon_b["kind"] != "select":
        return
    set_a = {json.dumps(r, sort_keys=True) for r in canon_a["rows"]}
    set_b = {json.dumps(r, sort_keys=True) for r in canon_b["rows"]}
    only_a = sorted(set_a - set_b)
    only_b = sorted(set_b - set_a)
    for r in only_a[:limit]:
        print("    only-in-%s: %s" % (name_a, r))
    if len(only_a) > limit:
        print("    ... %d more rows only in %s" % (len(only_a) - limit, name_a))
    for r in only_b[:limit]:
        print("    only-in-%s: %s" % (name_b, r))
    if len(only_b) > limit:
        print("    ... %d more rows only in %s" % (len(only_b) - limit, name_b))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--manifest", required=True, help="queries.json path")
    ap.add_argument("--bin", required=True, help="factoidal binary")
    ap.add_argument(
        "--pycottas-python",
        required=True,
        help="python interpreter with duckdb (the pycottas venv)",
    )
    ap.add_argument(
        "--workdir",
        default=None,
        help="cache dir for built .cottas artifacts (default: fresh tempdir)",
    )
    args = ap.parse_args()

    with open(args.manifest) as f:
        manifest = json.load(f)
    manifest_dir = os.path.dirname(os.path.abspath(args.manifest))

    # Validate the escape hatch up front: known_divergent MUST reference
    # an issue (#NNN). A bare "known" with no tracker is a manifest error.
    manifest_errors = []
    seen_names = set()
    for q in manifest["queries"]:
        if q["name"] in seen_names:
            manifest_errors.append("duplicate query name: %s" % q["name"])
        seen_names.add(q["name"])
        if q.get("fixture") not in manifest["fixtures"]:
            manifest_errors.append(
                "query %s references unknown fixture %r" % (q["name"], q.get("fixture"))
            )
        kd = q.get("known_divergent")
        if kd is not None and not re.search(r"#\d+", kd):
            manifest_errors.append(
                "query %s: known_divergent must reference an open issue "
                "as #NNN, got: %r" % (q["name"], kd)
            )
    if manifest_errors:
        for e in manifest_errors:
            print("MANIFEST-ERROR %s" % e)
        sys.exit(2)

    if args.workdir:
        workdir = args.workdir
        os.makedirs(workdir, exist_ok=True)
    else:
        workdir = tempfile.mkdtemp(prefix="factoidal-backend-parity-")
    cache = CottasCache(workdir, args.pycottas_python)

    # Resolve fixtures and build per-backend data files.
    backends = ["inmem", "cottas"]
    fixture_files = {}  # fixture name -> {backend: (data_flag, path)}
    for fname, rel in manifest["fixtures"].items():
        nq = os.path.join(manifest_dir, rel)
        if not os.path.exists(nq):
            print("MANIFEST-ERROR fixture %s missing: %s" % (fname, nq))
            sys.exit(2)
        cottas = cache.artifact_for(fname, nq)
        fixture_files[fname] = {
            "inmem": ("--data", nq),
            "cottas": ("--data-cottas", cottas),
        }

    n_pass = 0
    n_known = 0
    n_divergent = 0
    n_expect_fail = 0
    n_error = 0
    known_refs = set()

    for q in manifest["queries"]:
        name = q["name"]
        ordered = bool(q.get("ordered", False))
        known = q.get("known_divergent")
        results = {}
        errors = {}
        for backend in backends:
            data_flag, data_file = fixture_files[q["fixture"]][backend]
            parsed = run_query(args.bin, data_flag, data_file, q["query"])
            if "error" in parsed:
                errors[backend] = parsed["error"]
            else:
                results[backend] = canonical_result(parsed, ordered)

        if errors:
            detail = "; ".join(
                "%s: %s" % (b, errors[b]) for b in backends if b in errors
            )
            if known:
                print("KNOWN-DIVERGENT %s (%s): backend error — %s" % (name, known, detail))
                n_known += 1
                known_refs.add(known)
            else:
                print("ERROR %s: %s" % (name, detail))
                n_error += 1
            continue

        digests = {b: digest_of(results[b]) for b in backends}
        agree = len(set(digests.values())) == 1
        per_backend = ", ".join(
            "%s %s" % (b, summarise_canon(results[b])) for b in backends
        )

        if not agree:
            if known:
                print("KNOWN-DIVERGENT %s (%s): %s" % (name, known, per_backend))
                n_known += 1
                known_refs.add(known)
            else:
                print("DIVERGENT %s: %s" % (name, per_backend))
                print_row_diff(
                    backends[0], results[backends[0]], backends[1], results[backends[1]]
                )
                n_divergent += 1
            continue

        # Backends agree. Check expect against the in-memory reference so a
        # bug shared by ALL backends is still caught.
        expect_msg = None
        if "expect" in q:
            expect_msg = check_expect(q["expect"], results["inmem"])
        if expect_msg is not None:
            if known:
                # A shared-by-all-backends bug tracked by an open issue:
                # report as known (same policy as known_divergent), flip
                # back to a hard expect when the issue closes.
                print("KNOWN-EXPECT-FAIL %s (%s): %s" % (name, known, expect_msg))
                n_known += 1
                known_refs.add(known)
            else:
                print("EXPECT-FAIL %s: %s (backends agree with each other)" % (name, expect_msg))
                n_expect_fail += 1
            continue

        if known:
            print(
                "PASS %s (FIXED — backends now agree; remove known_divergent, see %s)"
                % (name, known)
            )
        else:
            print("PASS %s [%s]" % (name, summarise_canon(results["inmem"])))
        n_pass += 1

    total = len(manifest["queries"])
    known_note = (
        " (%s)" % "; ".join(sorted({re.search(r"#\d+", k).group(0) for k in known_refs}))
        if known_refs
        else ""
    )
    print(
        "Backend parity summary: %d of %d queries pass on both backends, "
        "%d known-divergent%s, %d new divergences, %d expect failures, "
        "%d errors (backends: %s)."
        % (
            n_pass,
            total,
            n_known,
            known_note,
            n_divergent,
            n_expect_fail,
            n_error,
            ", ".join(backends),
        )
    )
    if n_divergent or n_expect_fail or n_error:
        sys.exit(1)


if __name__ == "__main__":
    main()
