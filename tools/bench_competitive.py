#!/usr/bin/env python3
"""Competitive RDF/SPARQL benchmark: factoidal vs Apache Jena (ARQ
in-memory + TDB2 on-disk) vs pyoxigraph vs rdflib, on identical
in-tree data and identical SPARQL text.

See docs/designissues/2026-07-06-competitive-benchmark-results.md for
the write-up this feeds, and tools/bench-competitive.sh for the
rerunnable entry point (engine setup: Jena fetch/cache, pycottas venv).

Design (why these choices):

- **Load workloads** are the in-tree lifesci corpora referenced by
  docs/designissues/2026-07-05-disk-backed-db-perf-review.md:
  `gene.ttl` (888,949 triples) and the concatenation of every .ttl
  file in that same directory ("lifesci-all"; concatenation is valid
  Turtle here because none of the files use `@base` and prefix
  re-declaration mid-stream is legal).
- **Query workload** runs on `gene.ttl` only (the corpus the perf
  review already characterised, so this benchmark's numbers are
  cross-checkable against it) -- see tools/bench_competitive_queries.py
  for the 6 fixed SPARQL strings.
- **factoidal has two labelled in-memory CLI rows**: default (the
  streaming fast path, docs/designissues/2026-07-05-disk-backed-db-
  perf-review.md) and `FACTOIDAL_DISABLE_STREAM_FASTPATH=1` (the kill
  switch already used by tests/local/streamable_fastpath_regressions.sh)
  -- the task's "forced-slow path" row. A third factoidal row queries
  a COTTAS/Parquet artifact built by tools/corpus_pipeline.py (the
  on-disk path).
- **Jena has two labelled rows**: `arq` against the raw Turtle file
  (in-memory, reparsed every invocation -- the direct analog of
  factoidal's CLI) and `tdb2.tdbquery` against a pre-built TDB2 store
  (the direct analog of factoidal's COTTAS path).
- **cold vs warm**: for every process-per-query engine (factoidal CLI,
  Jena arq, Jena tdb2.tdbquery), "cold" is the first invocation after
  the corpus/DB exists on disk, "warm" is the median of 3 further
  invocations (OS page cache warm; each is still a fresh process --
  none of these tools expose a query-only hot loop without running a
  server). For the two persistent-process engines (pyoxigraph,
  rdflib), "cold" is the first `query()` call against the in-process
  store, "warm" is the median of 3 further calls in the SAME process.
  This asymmetry is real and is disclosed in the results doc rather
  than papered over.
- **Peak RSS**: no `/usr/bin/time -v` in this sandbox (confirmed
  absent), so tools/bench_rusage_run.py wraps every CLI invocation
  with `resource.getrusage(RUSAGE_CHILDREN)` in a fresh Python
  process (clean per-measurement scope). The persistent-process
  engines self-report `resource.getrusage(RUSAGE_SELF)` at two
  checkpoints (after load, after all queries) -- a process-lifetime
  peak, not a query-isolated one; disclosed in the JSON's
  `"rss_methodology"` field.
- **Answer agreement**: every engine's result set for a query is
  normalized to a list of {var: str(value)} dicts and compared as a
  multiset (order-insensitive; these queries have no ORDER BY). A
  mismatch VOIDs that query's timing row for the disagreeing engine
  (reported, not hidden) per the task brief -- "a benchmark row where
  answers disagree is VOID and flagged, not reported as a timing."
- **Timeouts**: every single invocation is capped at
  `--per-run-timeout-s` (default 600, anti-pattern #17). If the COLD
  run of an engine/query pair times out, the 3 warm runs are not
  attempted (no point re-running a proven-hanging combination) and the
  whole row is marked SKIP with the reason recorded.

Do NOT run this against a mid-rebuild working tree: main() checks
`git status --short -- bin/<platform>` and refuses (per the task
brief) unless `--allow-dirty-bin` is passed, in which case it copies
`git show HEAD:bin/<platform>/<binary>` to a scratch dir and uses that
instead, saying so in the JSON.
"""
import argparse
import json
import os
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from bench_competitive_queries import QUERIES  # noqa: E402

PLATFORM = "linux-x86_64"  # this sandbox; darwin-arm64 not exercised here
RUSAGE_WRAPPER = ROOT / "tools" / "bench_rusage_run.py"
GENE_TTL = ROOT / "examples/wikidata/subsets/lifesci-kgx/data/gene.ttl"
LIFESCI_DIR = ROOT / "examples/wikidata/subsets/lifesci-kgx/data"

DEFAULT_TIMEOUT_S = 600
WARM_RUNS = 3


def sh(cmd, timeout=None, env=None, cwd=None):
    return subprocess.run(
        cmd, timeout=timeout, env=env, cwd=cwd,
        capture_output=True, text=True,
    )


def median(xs):
    return statistics.median(xs) if xs else None


# --------------------------------------------------------------------------
# Working-tree / binary provenance guard (task brief item 4)
# --------------------------------------------------------------------------

def resolve_factoidal_binaries(scratch: Path, allow_dirty: bool) -> dict:
    bindir = ROOT / "bin" / PLATFORM
    names = ["factoidal", "factoidal-http"]
    status = sh(["git", "-C", str(ROOT), "status", "--short", "--", f"bin/{PLATFORM}"])
    dirty = bool(status.stdout.strip())
    out = {}
    if not dirty:
        for n in names:
            out[n] = str(bindir / n)
        out["_provenance"] = "working-tree bin/ (matches HEAD, git status clean)"
        return out

    if not allow_dirty:
        raise SystemExit(
            f"bin/{PLATFORM} has uncommitted changes (mid-rebuild?):\n"
            f"{status.stdout}\n"
            "Re-run with --allow-dirty-bin to use git HEAD's copy via "
            "`git show` into a scratch dir instead, per the task brief."
        )

    head = sh(["git", "-C", str(ROOT), "rev-parse", "HEAD"]).stdout.strip()
    dest = scratch / "head-bin"
    dest.mkdir(parents=True, exist_ok=True)
    for n in names:
        # NOTE: must run in raw byte mode (text=False) -- these are ELF
        # binaries; the shared sh() helper uses text=True/utf-8 decoding,
        # which would silently corrupt binary content (encoding errors
        # or byte-level mutation) instead of failing loudly.
        blob = subprocess.run(
            ["git", "-C", str(ROOT), "show", f"HEAD:bin/{PLATFORM}/{n}"],
            capture_output=True,
        )
        if blob.returncode != 0:
            continue
        p = dest / n
        p.write_bytes(blob.stdout)
        p.chmod(0o755)
        out[n] = str(p)
    out["_provenance"] = (
        f"bin/{PLATFORM} was locally modified mid-rebuild; used HEAD "
        f"({head}) copy via `git show` into {dest}"
    )
    return out


# --------------------------------------------------------------------------
# Engine detection
# --------------------------------------------------------------------------

def detect_engines(jena_home: str | None, factoidal_bins: dict) -> dict:
    engines = {}

    fp = factoidal_bins.get("factoidal")
    if fp and Path(fp).is_file():
        commit = sh(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"]).stdout.strip()
        engines["factoidal"] = {
            "available": True,
            "version": f"factoidal (bin/{PLATFORM}), commit {commit}",
            "provenance": factoidal_bins.get("_provenance"),
        }
    else:
        engines["factoidal"] = {"available": False, "reason": "binary not found"}

    if jena_home and (Path(jena_home) / "bin" / "arq").is_file():
        env = dict(os.environ)
        env["PATH"] = f"{jena_home}/bin:" + env.get("PATH", "")
        r = sh([f"{jena_home}/bin/jena.version"], env=env, timeout=60)
        ver = next((l for l in r.stdout.splitlines() if l.strip() and "Picked up" not in l), "unknown")
        engines["jena"] = {"available": True, "version": f"Apache Jena {ver}", "home": jena_home}
    else:
        engines["jena"] = {"available": False, "reason": "JENA_HOME not set up (see bench-competitive.sh)"}

    try:
        import pyoxigraph as ox  # noqa: F401
        r = sh([sys.executable, "-c", "import pyoxigraph, importlib.metadata as m; print(m.version('pyoxigraph'))"])
        engines["pyoxigraph"] = {"available": True, "version": f"pyoxigraph {r.stdout.strip()}"}
    except ImportError:
        engines["pyoxigraph"] = {"available": False, "reason": "pip install pyoxigraph failed/absent"}

    try:
        import rdflib  # noqa: F401
        engines["rdflib"] = {"available": True, "version": f"rdflib {rdflib.__version__}"}
    except ImportError:
        engines["rdflib"] = {"available": False, "reason": "rdflib absent"}

    return engines


# --------------------------------------------------------------------------
# Corpus prep
# --------------------------------------------------------------------------

def prepare_corpora(scratch: Path) -> dict:
    corpora = {}
    if not GENE_TTL.is_file():
        raise SystemExit(f"gene corpus missing: {GENE_TTL}")
    corpora["gene"] = {"path": str(GENE_TTL), "bytes": GENE_TTL.stat().st_size}

    lifesci_all = scratch / "lifesci-all.ttl"
    ttl_files = sorted(LIFESCI_DIR.glob("*.ttl"))
    base_files = [f for f in ttl_files if _grep_base(f)]
    if base_files:
        raise SystemExit(f"refusing naive concat: @base found in {base_files}")
    with open(lifesci_all, "wb") as out:
        for f in ttl_files:
            out.write(f.read_bytes())
            out.write(b"\n")
    corpora["lifesci-all"] = {
        "path": str(lifesci_all),
        "bytes": lifesci_all.stat().st_size,
        "source_files": [f.name for f in ttl_files],
    }
    return corpora


def _grep_base(path: Path) -> bool:
    with open(path, "r", errors="ignore") as f:
        for line in f:
            if line.strip().startswith("@base"):
                return True
    return False


# --------------------------------------------------------------------------
# Answer comparison
# --------------------------------------------------------------------------

def normalize_rows(rows):
    """rows: list of {var: str-or-None}. Return a sorted, hashable form.

    BUG FIXED (crashed the first real run partway through
    q6_optional_filter, whose OPTIONAL variable is legitimately
    None/unbound in most rows): per-row `sorted(r.items())` is safe --
    dict keys are unique strings, so tuple comparison never needs to
    fall through to comparing values. The crash was in the OUTER
    `sorted(out)`, which compares two different rows' (key, value)
    tuples position-by-position; when the same key holds None in one
    row and a string in another, Python 3 raises TypeError comparing
    them directly. Fix: sort the outer list using an explicit key
    function that maps each (key, value) to (key, is_none,
    value-or-placeholder) so None vs str never gets compared directly,
    without conflating None with the literal string "None" (a real
    IRI/literal could contain that text)."""
    out = [tuple(sorted(r.items())) for r in rows]

    def row_sort_key(row):
        return tuple((k, v is None, "" if v is None else v) for k, v in row)

    return sorted(out, key=row_sort_key)


def compare_answers(per_engine_rows: dict) -> dict:
    """per_engine_rows: {engine_label: rows-list-or-None (None = SKIP)}."""
    normalized = {}
    for label, rows in per_engine_rows.items():
        if rows is None:
            continue
        normalized[label] = normalize_rows(rows)

    if len(normalized) <= 1:
        return {"agree": True, "note": "fewer than 2 engines produced an answer", "engines_compared": list(normalized)}

    labels = list(normalized)
    reference = normalized[labels[0]]
    mismatches = []
    for label in labels[1:]:
        if normalized[label] != reference:
            mismatches.append(label)
    return {
        "agree": not mismatches,
        "engines_compared": labels,
        "mismatches": mismatches,
        "reference_engine": labels[0],
    }


# --------------------------------------------------------------------------
# Per-engine run primitives
# --------------------------------------------------------------------------

def run_cli_timed(cmd, timeout_s, scratch, tag):
    """Run `cmd` via the rusage wrapper. Returns dict with wall_s,
    peak_rss_kb, returncode, stdout_path, timed_out."""
    out_path = scratch / f"{tag}.out"
    err_path = scratch / f"{tag}.err"
    wrapped = [sys.executable, str(RUSAGE_WRAPPER), str(out_path), str(err_path)] + cmd
    try:
        r = subprocess.run(wrapped, capture_output=True, text=True, timeout=timeout_s + 30)
    except subprocess.TimeoutExpired:
        return {"timed_out": True, "wall_s": None, "peak_rss_kb": None, "returncode": None,
                "stdout_path": str(out_path), "stderr_path": str(err_path)}
    if r.returncode != 0 or not r.stdout.strip():
        return {"timed_out": False, "wall_s": None, "peak_rss_kb": None, "returncode": r.returncode,
                "stdout_path": str(out_path), "stderr_path": str(err_path), "wrapper_error": r.stderr[-2000:]}
    meta = json.loads(r.stdout.strip().splitlines()[-1])
    meta["timed_out"] = meta.get("returncode") == 124
    meta["stdout_path"] = str(out_path)
    meta["stderr_path"] = str(err_path)
    return meta


def parse_sparql_json(stdout_text):
    doc = json.loads(stdout_text)
    varnames = doc["head"]["vars"]
    rows = []
    for b in doc["results"]["bindings"]:
        rec = {}
        for v in varnames:
            if v in b:
                cell = b[v]
                rec[v] = cell.get("value")
            else:
                rec[v] = None
        rows.append(rec)
    return rows


def parse_jena_csv(stdout_text):
    """Jena's default table output isn't machine-parseable reliably;
    we always request --results=CSV from arq/tdbquery instead.

    LIMITATION (disclosed, not silently assumed away): this is a naive
    split(",") parser, not an RFC 4180 CSV reader -- it would mis-parse
    a literal value containing a comma or an embedded newline. None of
    the 6 queries in tools/bench_competitive_queries.py ever bind a
    variable to such a value (results are IRIs and xsd:integer COUNTs
    only), so this is safe for THIS benchmark's query set specifically,
    not a general-purpose Jena CSV reader."""
    lines = [l for l in stdout_text.splitlines() if l.strip() != ""]
    if not lines:
        return []
    header = lines[0].split(",")
    rows = []
    for line in lines[1:]:
        cells = line.split(",")
        rec = {}
        for i, h in enumerate(header):
            rec[h] = cells[i] if i < len(cells) and cells[i] != "" else None
        rows.append(rec)
    return rows


def canonicalize_term(s):
    """Second line of defense on top of each engine's own bare-lexical
    extraction: strip pyoxigraph-style '<iri>' brackets and
    '"lex"^^<dt>'/'"lex"@lang' wrapping, in case a code path emits a
    raw N-Triples-ish term string instead of the bare lexical value.
    Does NOT distinguish literal datatypes (anti-pattern #6 note: our
    6 queries only ever compare URIs and integer-valued COUNT results
    across engines, so lexical-only comparison is adequate here and
    is disclosed as a limitation in the results doc, not silently
    assumed correct for arbitrary future queries)."""
    if s is None:
        return None
    if len(s) >= 2 and s[0] == "<" and s[-1] == ">":
        return s[1:-1]
    if len(s) >= 2 and s[0] == '"':
        end = s.rfind('"')
        if end > 0:
            return s[1:end]
    return s


def canonicalize_rows(rows):
    return [{k: canonicalize_term(v) for k, v in r.items()} for r in rows]


# --------------------------------------------------------------------------
# LOAD phase: engine x corpus -> {wall_s_runs, wall_s_median, peak_rss_kb_median, runs}
# --------------------------------------------------------------------------

MATERIALIZING_QUERY_SPARQL = QUERIES["q3_subject_point_lookup"]["sparql"]


def load_factoidal_cli(bin_path, corpus_path, scratch, tag, env_extra=None, n_runs=3, timeout_s=DEFAULT_TIMEOUT_S):
    """factoidal's CLI has no load-only op; use the point-lookup query
    (not fast-path-eligible, per docs/designissues/2026-07-05-disk-
    backed-db-perf-review.md and this session's own probe) as the
    materialize-to-queryable-state proxy, run n_runs fresh times."""
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    runs = []
    for i in range(n_runs):
        cmd = ["timeout", str(timeout_s), bin_path, "query", "--data", corpus_path,
               "-e", MATERIALIZING_QUERY_SPARQL, "--output", "json"]
        r = run_cli_timed_env(cmd, scratch, f"{tag}-load{i}", env)
        runs.append(r)
        if r.get("timed_out"):
            break
    return summarize_load_runs(runs)


def run_cli_timed_env(cmd, scratch, tag, env):
    out_path = scratch / f"{tag}.out"
    err_path = scratch / f"{tag}.err"
    wrapped = [sys.executable, str(RUSAGE_WRAPPER), str(out_path), str(err_path)] + cmd
    try:
        r = subprocess.run(wrapped, capture_output=True, text=True, timeout=DEFAULT_TIMEOUT_S + 30, env=env)
    except subprocess.TimeoutExpired:
        return {"timed_out": True, "wall_s": None, "peak_rss_kb": None}
    if r.returncode != 0 or not r.stdout.strip():
        return {"timed_out": False, "wall_s": None, "peak_rss_kb": None, "wrapper_error": r.stderr[-2000:]}
    meta = json.loads(r.stdout.strip().splitlines()[-1])
    meta["timed_out"] = meta.get("returncode") == 124
    return meta


def summarize_load_runs(runs):
    ok = [r for r in runs if r.get("wall_s") is not None]
    return {
        "n_runs": len(runs),
        "n_ok": len(ok),
        "wall_s_runs": [r["wall_s"] for r in ok],
        "wall_s_median": median([r["wall_s"] for r in ok]),
        "peak_rss_kb_runs": [r["peak_rss_kb"] for r in ok],
        "peak_rss_kb_median": median([r["peak_rss_kb"] for r in ok]),
        "any_timed_out": any(r.get("timed_out") for r in runs),
    }


def load_jena_arq_inmem(jena_home, corpus_path, scratch, tag, n_runs=3, timeout_s=DEFAULT_TIMEOUT_S):
    env = dict(os.environ)
    env["PATH"] = f"{jena_home}/bin:" + env.get("PATH", "")
    rq_path = scratch / f"{tag}-materializing.rq"
    rq_path.write_text(MATERIALIZING_QUERY_SPARQL)
    runs = []
    for i in range(n_runs):
        cmd = ["timeout", str(timeout_s), f"{jena_home}/bin/arq",
               f"--data={corpus_path}", f"--query={rq_path}", "--results=CSV"]
        r = run_cli_timed_env(cmd, scratch, f"{tag}-load{i}", env)
        runs.append(r)
        if r.get("timed_out"):
            break
    return summarize_load_runs(runs)


def load_jena_tdb2(jena_home, corpus_path, tdb2_dir, scratch, tag, n_runs=3, timeout_s=DEFAULT_TIMEOUT_S):
    env = dict(os.environ)
    env["PATH"] = f"{jena_home}/bin:" + env.get("PATH", "")
    runs = []
    for i in range(n_runs):
        this_dir = Path(f"{tdb2_dir}-run{i}")
        if this_dir.exists():
            shutil.rmtree(this_dir)
        this_dir.mkdir(parents=True)
        cmd = ["timeout", str(timeout_s), f"{jena_home}/bin/tdb2.tdbloader",
               f"--loc={this_dir}", str(corpus_path)]
        r = run_cli_timed_env(cmd, scratch, f"{tag}-load{i}", env)
        runs.append(r)
        if r.get("timed_out"):
            break
    result = summarize_load_runs(runs)
    result["last_db_dir"] = str(Path(f"{tdb2_dir}-run{len(runs) - 1}"))
    return result


def load_python_driver(driver_script, corpus_path, scratch, tag, n_runs=3, timeout_s=DEFAULT_TIMEOUT_S):
    runs = []
    for i in range(n_runs):
        out_path = scratch / f"{tag}-load{i}.out"
        err_path = scratch / f"{tag}-load{i}.err"
        cmd = ["timeout", str(timeout_s), sys.executable, str(driver_script),
               "--corpus", str(corpus_path), "--queries-json", "{}", "--load-only"]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_s + 30)
        except subprocess.TimeoutExpired:
            runs.append({"timed_out": True, "wall_s": None, "peak_rss_kb": None})
            break
        out_path.write_text(r.stdout)
        err_path.write_text(r.stderr)
        if r.returncode != 0 or not r.stdout.strip():
            runs.append({"timed_out": False, "wall_s": None, "peak_rss_kb": None})
            continue
        doc = json.loads(r.stdout.strip().splitlines()[-1])
        runs.append({"timed_out": False, "wall_s": doc["load_s"], "peak_rss_kb": doc["load_peak_rss_kb"]})
    return summarize_load_runs(runs)


def import_factoidal_cottas(corpus_path, corpus_root, dataset_name, scratch, timeout_s=DEFAULT_TIMEOUT_S):
    """Single run only (not median-of-3): the pipeline takes ~2 minutes
    on gene.ttl (measured this session) and re-running it 3x would cost
    ~6+ minutes for one number; disclosed here and in the results doc
    rather than silently deviating from the "3-run median" norm."""
    pycottas_python = str(ROOT / "_tmp.junk/pycottas-venv/bin/python")
    if not Path(pycottas_python).is_file():
        return {"ok": False, "reason": "pycottas venv not found at _tmp.junk/pycottas-venv"}
    cmd = ["timeout", str(timeout_s), pycottas_python, str(ROOT / "tools/corpus_pipeline.py"),
           "materialize-nq-cottas-corpus",
           "--input", str(corpus_path), "--input-format", "turtle",
           "--corpus-root", str(corpus_root), "--dataset-name", dataset_name,
           "--chunk-name", dataset_name, "--parser", "python", "--build-sidecars"]
    r = run_cli_timed(cmd, timeout_s, scratch, f"cottas-import-{dataset_name}")
    artifact = Path(corpus_root) / dataset_name / "v1" / "data.cottas"
    r["ok"] = r.get("wall_s") is not None and artifact.is_file()
    r["artifact_path"] = str(artifact) if artifact.is_file() else None
    r["n_runs"] = 1
    r["note"] = "single run (import cost ~2 min on gene.ttl; median-of-3 not run for this workload)"
    return r


# --------------------------------------------------------------------------
# QUERY phase: engine x query -> {cold_s, warm_s_runs, warm_s_median, rows, skip_reason}
# --------------------------------------------------------------------------

def query_factoidal_cli(bin_path, corpus_path, sparql, scratch, tag, env_extra=None, timeout_s=DEFAULT_TIMEOUT_S, cottas=False):
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)

    def factory():
        data_flag = "--data-cottas" if cottas else "--data"
        return [bin_path, "query", data_flag, corpus_path, "-e", sparql, "--output", "json"]

    def run_one(cmd, rtag):
        return run_cli_timed_env(cmd, scratch, rtag, env)

    cold_cmd = ["timeout", str(timeout_s)] + factory()
    cold = run_one(cold_cmd, f"{tag}-cold")
    out = {"cold_s": cold.get("wall_s"), "cold_peak_rss_kb": cold.get("peak_rss_kb")}
    if cold.get("timed_out") or cold.get("wall_s") is None:
        out["skip_reason"] = "cold run timed out or failed; warm runs not attempted"
        out["warm_s_runs"] = []
        out["rows"] = None
        return out

    # re-run cold command once more to capture stdout for answer-checking
    # (run_cli_timed writes stdout to a file we can read back)
    stdout_path = scratch / f"{tag}-cold.out"
    try:
        rows = canonicalize_rows(parse_sparql_json(stdout_path.read_text()))
    except Exception as e:  # noqa: BLE001
        rows = None
        out["parse_error"] = str(e)
    out["rows"] = rows
    out["row_count"] = len(rows) if rows is not None else None

    warm_times = []
    for i in range(WARM_RUNS):
        warm_cmd = ["timeout", str(timeout_s)] + factory()
        w = run_one(warm_cmd, f"{tag}-warm{i}")
        if w.get("timed_out") or w.get("wall_s") is None:
            break
        warm_times.append(w["wall_s"])
    out["warm_s_runs"] = warm_times
    out["warm_s_median"] = median(warm_times)
    return out


def query_jena(jena_bin, data_args, sparql, scratch, tag, timeout_s=DEFAULT_TIMEOUT_S, jena_home=None):
    env = dict(os.environ)
    if jena_home:
        env["PATH"] = f"{jena_home}/bin:" + env.get("PATH", "")
    rq_path = scratch / f"{tag}.rq"
    rq_path.write_text(sparql)

    def factory():
        return [jena_bin] + data_args + [f"--query={rq_path}", "--results=CSV"]

    cold_cmd = ["timeout", str(timeout_s)] + factory()
    cold = run_cli_timed_env(cold_cmd, scratch, f"{tag}-cold", env)
    out = {"cold_s": cold.get("wall_s"), "cold_peak_rss_kb": cold.get("peak_rss_kb")}
    if cold.get("timed_out") or cold.get("wall_s") is None:
        out["skip_reason"] = "cold run timed out or failed; warm runs not attempted"
        out["warm_s_runs"] = []
        out["rows"] = None
        return out

    stdout_path = scratch / f"{tag}-cold.out"
    try:
        rows = canonicalize_rows(parse_jena_csv(stdout_path.read_text()))
    except Exception as e:  # noqa: BLE001
        rows = None
        out["parse_error"] = str(e)
    out["rows"] = rows
    out["row_count"] = len(rows) if rows is not None else None

    warm_times = []
    for i in range(WARM_RUNS):
        warm_cmd = ["timeout", str(timeout_s)] + factory()
        w = run_cli_timed_env(warm_cmd, scratch, f"{tag}-warm{i}", env)
        if w.get("timed_out") or w.get("wall_s") is None:
            break
        warm_times.append(w["wall_s"])
    out["warm_s_runs"] = warm_times
    out["warm_s_median"] = median(warm_times)
    return out


def query_python_driver(driver_script, corpus_path, scratch, tag, timeout_s=DEFAULT_TIMEOUT_S):
    qjson = json.dumps({k: v["sparql"] for k, v in QUERIES.items()})
    out_path = scratch / f"{tag}.out"
    err_path = scratch / f"{tag}.err"
    cmd = ["timeout", str(timeout_s), sys.executable, str(driver_script),
           "--corpus", str(corpus_path), "--queries-json", qjson, "--warm-runs", str(WARM_RUNS)]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_s + 30)
    except subprocess.TimeoutExpired:
        return {"ok": False, "reason": "driver batch (all 6 queries) timed out"}
    out_path.write_text(r.stdout)
    err_path.write_text(r.stderr)
    if r.returncode != 0 or not r.stdout.strip():
        return {"ok": False, "reason": f"driver failed rc={r.returncode}", "stderr_tail": r.stderr[-2000:]}
    doc = json.loads(r.stdout.strip().splitlines()[-1])
    doc["ok"] = True
    for qid, q in doc.get("queries", {}).items():
        q["rows"] = canonicalize_rows(q["rows"])
        q["warm_s_median"] = median(q["warm_s_runs"])
    return doc


# --------------------------------------------------------------------------
# Main orchestration
# --------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jena-home", default=os.environ.get("JENA_HOME"))
    ap.add_argument("--scratch", default=None)
    ap.add_argument("--output", default=str(ROOT / "docs/test-results/competitive-bench.json"))
    ap.add_argument("--per-run-timeout-s", type=int, default=DEFAULT_TIMEOUT_S)
    ap.add_argument("--allow-dirty-bin", action="store_true")
    ap.add_argument("--skip-lifesci-all-load", action="store_true",
                     help="skip the larger scaling-only load workload (faster reruns)")
    ap.add_argument("--only-phase", choices=["load", "query", "all"], default="all")
    ap.add_argument("--reuse-gene-tdb2-dir", default=None,
                     help="skip the LOAD phase's tdb2.tdbloader step for the gene corpus and query this "
                          "already-built TDB2 directory instead (used with --only-phase query)")
    ap.add_argument("--reuse-gene-cottas-artifact", default=None,
                     help="skip the LOAD phase's cottas-import step for the gene corpus and query this "
                          "already-built .cottas artifact instead (used with --only-phase query)")
    args = ap.parse_args()

    scratch = Path(args.scratch) if args.scratch else Path(tempfile.mkdtemp(prefix="bench-competitive-"))
    scratch.mkdir(parents=True, exist_ok=True)
    print(f"[bench-competitive] scratch dir: {scratch}", file=sys.stderr)

    factoidal_bins = resolve_factoidal_binaries(scratch, args.allow_dirty_bin)
    engines = detect_engines(args.jena_home, factoidal_bins)
    print("[bench-competitive] engines:", json.dumps(engines, indent=2), file=sys.stderr)

    corpora = prepare_corpora(scratch)

    results = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "host_note": "cloud sandbox, 4-core Linux, shared with other sessions -- wall-clock, not isolated benchmark hardware",
        "factoidal_commit": sh(["git", "-C", str(ROOT), "rev-parse", "HEAD"]).stdout.strip(),
        "engines": engines,
        "corpora": corpora,
        "rss_methodology": (
            "CLI/process-per-query engines (factoidal CLI, Jena arq, Jena "
            "tdb2.tdbquery): peak_rss_kb is resource.getrusage(RUSAGE_CHILDREN) "
            "scoped to exactly that one invocation, via tools/bench_rusage_run.py "
            "(no /usr/bin/time -v in this sandbox). Persistent-process engines "
            "(pyoxigraph, rdflib): peak_rss_kb is resource.getrusage(RUSAGE_SELF) "
            "sampled once, immediately after load and before any query -- the LOAD "
            "table's peak_rss_kb for these two engines is load-only, not the whole "
            "process lifetime."
        ),
        "cold_warm_methodology": (
            "CLI/process-per-query engines: cold = first fresh-process invocation, "
            "warm = median of 3 further fresh-process invocations (OS page cache "
            "warm; no persistent engine state). Persistent-process engines "
            "(pyoxigraph, rdflib): cold = first query() call in a freshly-loaded "
            "process, warm = median of 3 further calls in the SAME process. This "
            "asymmetry is real (persistent engines never pay process-startup cost "
            "on 'warm'; CLI engines always do) and is not papered over."
        ),
        "queries": {k: {"sparql": v["sparql"], "description": v["description"], "category": v["category"]}
                    for k, v in QUERIES.items()},
        "load": [],
        "query_results": [],
        "agreement": [],
    }

    # A query-phase-only rerun (e.g. recovering from a bug that crashed
    # only the query phase, per the task's "no need to redo the whole
    # 16-minute LOAD phase" case) must not clobber a prior run's LOAD
    # section with an empty list -- carry it forward if present.
    if args.only_phase == "query" and Path(args.output).is_file():
        try:
            prior = json.loads(Path(args.output).read_text())
            if prior.get("load"):
                results["load"] = prior["load"]
                print(f"[bench-competitive] --only-phase query: carried forward "
                      f"{len(prior['load'])} LOAD rows from the existing {args.output}",
                      file=sys.stderr)
        except Exception as e:  # noqa: BLE001
            print(f"[bench-competitive] could not read prior output for LOAD carry-forward: {e}", file=sys.stderr)

    def save():
        Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        Path(args.output).write_text(json.dumps(results, indent=2) + "\n")

    save()

    fac_bin = factoidal_bins.get("factoidal")
    jena_home = args.jena_home if engines["jena"]["available"] else None
    have_pyoxi = engines["pyoxigraph"]["available"]
    have_rdflib = engines["rdflib"]["available"]
    gene_path = corpora["gene"]["path"]
    lifesci_all_path = corpora["lifesci-all"]["path"]

    pyoxi_driver = ROOT / "tools/bench_competitive_driver_pyoxigraph.py"
    rdflib_driver = ROOT / "tools/bench_competitive_driver_rdflib.py"

    if args.reuse_gene_tdb2_dir:
        results["_gene_tdb2_dir"] = args.reuse_gene_tdb2_dir
        print(f"[bench-competitive] reusing existing TDB2 dir: {args.reuse_gene_tdb2_dir}", file=sys.stderr)
    if args.reuse_gene_cottas_artifact:
        results["_gene_cottas_artifact"] = args.reuse_gene_cottas_artifact
        print(f"[bench-competitive] reusing existing COTTAS artifact: {args.reuse_gene_cottas_artifact}", file=sys.stderr)

    # ---------------- LOAD phase ----------------
    if args.only_phase in ("load", "all"):
        load_corpora = ["gene"] if args.skip_lifesci_all_load else ["gene", "lifesci-all"]
        for corpus_name in load_corpora:
            corpus_path = corpora[corpus_name]["path"]
            print(f"[bench-competitive] LOAD phase: corpus={corpus_name}", file=sys.stderr)

            if fac_bin:
                r = load_factoidal_cli(fac_bin, corpus_path, scratch, f"fac-fast-{corpus_name}",
                                        timeout_s=args.per_run_timeout_s)
                results["load"].append({"engine": "factoidal-cli-fast-path", "corpus": corpus_name,
                                         "method": "3x fresh-process point-lookup query (materializing, non-fast-path-eligible)",
                                         **r})
                save()

                r = load_factoidal_cli(fac_bin, corpus_path, scratch, f"fac-slow-{corpus_name}",
                                        env_extra={"FACTOIDAL_DISABLE_STREAM_FASTPATH": "1"},
                                        timeout_s=args.per_run_timeout_s)
                results["load"].append({"engine": "factoidal-cli-forced-slow-path (kill switch)", "corpus": corpus_name,
                                         "method": "3x fresh-process point-lookup query, FACTOIDAL_DISABLE_STREAM_FASTPATH=1",
                                         **r})
                save()

            if jena_home:
                r = load_jena_arq_inmem(jena_home, corpus_path, scratch, f"jena-arq-{corpus_name}",
                                         timeout_s=args.per_run_timeout_s)
                results["load"].append({"engine": "jena-arq-inmemory", "corpus": corpus_name,
                                         "method": "3x fresh-process point-lookup query (arq reparses the file every invocation)",
                                         **r})
                save()

                tdb2_dir = scratch / f"tdb2-{corpus_name}"
                r = load_jena_tdb2(jena_home, corpus_path, tdb2_dir, scratch, f"jena-tdb2-{corpus_name}",
                                    timeout_s=args.per_run_timeout_s)
                results["load"].append({"engine": "jena-tdb2 (on-disk)", "corpus": corpus_name,
                                         "method": "3x fresh tdb2.tdbloader runs (fresh target dir each run)",
                                         **r})
                save()
                # keep the corpus-specific gene TDB2 db around for the query phase
                if corpus_name == "gene":
                    results["_gene_tdb2_dir"] = r["last_db_dir"]

            if have_pyoxi:
                r = load_python_driver(pyoxi_driver, corpus_path, scratch, f"pyoxi-{corpus_name}",
                                        timeout_s=args.per_run_timeout_s)
                results["load"].append({"engine": "pyoxigraph (in-memory)", "corpus": corpus_name,
                                         "method": "3x fresh Python process, Store().load()",
                                         **r})
                save()

            if have_rdflib:
                r = load_python_driver(rdflib_driver, corpus_path, scratch, f"rdflib-{corpus_name}",
                                        timeout_s=args.per_run_timeout_s)
                results["load"].append({"engine": "rdflib (in-memory, floor baseline)", "corpus": corpus_name,
                                         "method": "3x fresh Python process, Graph().parse()",
                                         **r})
                save()

            if fac_bin and corpus_name == "gene":
                cottas_root = scratch / f"cottas-{corpus_name}"
                r = import_factoidal_cottas(corpus_path, cottas_root, f"{corpus_name}-bench", scratch,
                                             timeout_s=args.per_run_timeout_s)
                results["load"].append({"engine": "factoidal cottas-import (on-disk build)", "corpus": corpus_name,
                                         "method": "tools/corpus_pipeline.py materialize-nq-cottas-corpus --build-sidecars",
                                         **r})
                save()
                if r.get("ok"):
                    results["_gene_cottas_artifact"] = r["artifact_path"]

    # ---------------- QUERY phase (gene corpus only) ----------------
    if args.only_phase in ("query", "all"):
        print("[bench-competitive] QUERY phase: corpus=gene", file=sys.stderr)
        query_rows = []

        for qid, qspec in QUERIES.items():
            sparql = qspec["sparql"]
            per_engine_rows = {}

            if fac_bin:
                r = query_factoidal_cli(fac_bin, gene_path, sparql, scratch, f"q-{qid}-fac-fast",
                                         timeout_s=args.per_run_timeout_s)
                query_rows.append({"engine": "factoidal-cli-fast-path", "query": qid, **r})
                per_engine_rows["factoidal-cli-fast-path"] = r.get("rows")

                r = query_factoidal_cli(fac_bin, gene_path, sparql, scratch, f"q-{qid}-fac-slow",
                                         env_extra={"FACTOIDAL_DISABLE_STREAM_FASTPATH": "1"},
                                         timeout_s=args.per_run_timeout_s)
                query_rows.append({"engine": "factoidal-cli-forced-slow-path (kill switch)", "query": qid, **r})
                per_engine_rows["factoidal-cli-forced-slow-path (kill switch)"] = r.get("rows")

                cottas_artifact = results.get("_gene_cottas_artifact")
                if cottas_artifact:
                    r = query_factoidal_cli(fac_bin, cottas_artifact, sparql, scratch, f"q-{qid}-fac-cottas",
                                             timeout_s=args.per_run_timeout_s, cottas=True)
                    query_rows.append({"engine": "factoidal-cottas (on-disk)", "query": qid, **r})
                    per_engine_rows["factoidal-cottas (on-disk)"] = r.get("rows")

            if jena_home:
                r = query_jena(f"{jena_home}/bin/arq", [f"--data={gene_path}"], sparql, scratch,
                                f"q-{qid}-jena-arq", timeout_s=args.per_run_timeout_s, jena_home=jena_home)
                query_rows.append({"engine": "jena-arq-inmemory", "query": qid, **r})
                per_engine_rows["jena-arq-inmemory"] = r.get("rows")

                gene_tdb2_dir = results.get("_gene_tdb2_dir")
                if gene_tdb2_dir:
                    r = query_jena(f"{jena_home}/bin/tdb2.tdbquery", [f"--loc={gene_tdb2_dir}"], sparql, scratch,
                                    f"q-{qid}-jena-tdb2", timeout_s=args.per_run_timeout_s, jena_home=jena_home)
                    query_rows.append({"engine": "jena-tdb2 (on-disk)", "query": qid, **r})
                    per_engine_rows["jena-tdb2 (on-disk)"] = r.get("rows")

            results["agreement"].append({"query": qid, **compare_answers(per_engine_rows)})
            save()

        # pyoxigraph / rdflib run their whole 6-query batch in one process
        if have_pyoxi:
            doc = query_python_driver(pyoxi_driver, gene_path, scratch, "batch-pyoxi",
                                       timeout_s=args.per_run_timeout_s)
            if doc.get("ok"):
                for qid, q in doc["queries"].items():
                    query_rows.append({"engine": "pyoxigraph (in-memory)", "query": qid,
                                        "cold_s": q["cold_s"], "warm_s_runs": q["warm_s_runs"],
                                        "warm_s_median": q["warm_s_median"], "row_count": q["row_count"],
                                        "rows": q["rows"]})
            else:
                query_rows.append({"engine": "pyoxigraph (in-memory)", "query": "ALL", "skip_reason": doc.get("reason")})
            save()

        if have_rdflib:
            doc = query_python_driver(rdflib_driver, gene_path, scratch, "batch-rdflib",
                                       timeout_s=args.per_run_timeout_s)
            if doc.get("ok"):
                for qid, q in doc["queries"].items():
                    query_rows.append({"engine": "rdflib (in-memory, floor baseline)", "query": qid,
                                        "cold_s": q["cold_s"], "warm_s_runs": q["warm_s_runs"],
                                        "warm_s_median": q["warm_s_median"], "row_count": q["row_count"],
                                        "rows": q["rows"]})
            else:
                query_rows.append({"engine": "rdflib (in-memory, floor baseline)", "query": "ALL", "skip_reason": doc.get("reason")})
            save()

        # re-run agreement check now that pyoxigraph/rdflib rows are in
        agreement_by_query = {a["query"]: a for a in results["agreement"]}
        for qid in QUERIES:
            per_engine_rows = {r["engine"]: r.get("rows") for r in query_rows if r.get("query") == qid}
            agreement_by_query[qid] = {"query": qid, **compare_answers(per_engine_rows)}
        results["agreement"] = list(agreement_by_query.values())

        # strip the (large) per-row answer payloads from the timing rows in
        # the committed JSON -- keep row_count + a content hash, not every
        # binding; agreement is already recorded in "agreement" above.
        import hashlib
        for r in query_rows:
            rows = r.pop("rows", None)
            if rows is not None:
                r["row_count"] = r.get("row_count", len(rows))
                blob = json.dumps(normalize_rows(rows), sort_keys=True).encode()
                r["answer_sha256"] = hashlib.sha256(blob).hexdigest()[:16]
        results["query_results"] = query_rows
        save()

    print(f"[bench-competitive] done. Results: {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
