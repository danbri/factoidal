#!/usr/bin/env python3
"""Experimental local query trace harness.

Runs the existing Factoidal CLI against an on-disk COTTAS artifact using:

1. `--explain-only` with `--explain-out` for planner-side JSON and text
2. a real query execution with `-o json` for actual results

It then normalizes the current outputs into a first-cut trace schema plus a
human-facing history overview. This is intentionally experimental and private:
the goal is to learn what a future `/query-trace` endpoint should return.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BIN = REPO_ROOT / "bin" / "darwin-arm64" / "factoidal"


SECTION_HEADER_RE = re.compile(r"^=== (.+) ===$")
TRACE_LINE_RE = re.compile(r"^\[([^\]]+)\]\s*(.*)$")
JOIN_ORDER_RE = re.compile(r"^\s*F\* planner \(runtime ground truth\):(.*)$")
ELAPSED_RE = re.compile(
    r"parse=(?P<parse>[0-9.]+)ms\s+open=(?P<open>[0-9.]+)ms\s+"
    r"algebra=(?P<algebra>[0-9.]+)ms\s+estimate=(?P<estimate>[0-9.]+)ms\s+"
    r"total=(?P<total>[0-9.]+)ms"
)
SEARCH_BOUND_RE = re.compile(
    r"search_fast: bound s=(?P<s>\S+) p=(?P<p>\S+) o=(?P<o>\S+) g=(?P<g>\S+)"
)
RG_COUNT_RE = re.compile(r"search_fast: rg_count=(?P<count>\d+)")


def run_command(
    args: list[str], cwd: Path, timeout_sec: float | None = None
) -> tuple[subprocess.CompletedProcess[str], float]:
    started = time.monotonic()
    proc = subprocess.run(
        args,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        check=False,
        timeout=timeout_sec,
    )
    return proc, (time.monotonic() - started) * 1000.0


def read_query_text(query_file: Path | None, inline_query: str | None) -> str:
    if inline_query is not None:
        return inline_query
    if query_file is None:
        raise ValueError("need query text")
    return query_file.read_text(encoding="utf-8")


def ensure_text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def split_sections(text: str) -> dict[str, list[str]]:
    sections: dict[str, list[str]] = {}
    current = "PRELUDE"
    sections[current] = []
    for line in text.splitlines():
        match = SECTION_HEADER_RE.match(line)
        if match:
            current = match.group(1)
            sections[current] = []
            continue
        sections.setdefault(current, []).append(line)
    return sections


def discover_index_artifacts(data_cottas: Path) -> list[dict[str, Any]]:
    artifacts: list[dict[str, Any]] = []
    base = str(data_cottas)
    explicit_kinds = {
        ".s.dict": "dict",
        ".p.dict": "dict",
        ".o.dict": "dict",
        ".g.dict": "dict",
        ".s.presence": "presence",
        ".p.presence": "presence",
        ".o.presence": "presence",
        ".g.presence": "presence",
        ".p.offsets": "offsets",
        ".po.presence": "compound_presence",
        ".row_ids": "row_ids",
    }
    seen: set[Path] = set()
    for suffix, kind in explicit_kinds.items():
        path = Path(base + suffix)
        if path.exists():
            seen.add(path)
            artifacts.append(
                {
                    "path": str(path),
                    "kind": kind,
                    "scope": "external_binary_mmap_artifact",
                    "size_bytes": path.stat().st_size,
                }
            )

    for path in sorted(data_cottas.parent.glob(data_cottas.name + ".*")):
        if path in seen:
            continue
        artifacts.append(
            {
                "path": str(path),
                "kind": "unknown_sidecar",
                "scope": "external_binary_mmap_artifact",
                "size_bytes": path.stat().st_size,
            }
        )
    return artifacts


def parse_trace_lines(stderr_text: str) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    seq = 1
    current_search: dict[str, Any] | None = None

    for line in stderr_text.splitlines():
        match = TRACE_LINE_RE.match(line)
        if not match:
            continue
        tag = match.group(1)
        message = match.group(2)
        data: dict[str, Any] = {"tag": tag, "raw": message}
        kind = "engine_trace"
        summary = f"{tag}: {message}"

        bound_match = SEARCH_BOUND_RE.search(message)
        if bound_match:
            current_search = {
                "s": bound_match.group("s"),
                "p": bound_match.group("p"),
                "o": bound_match.group("o"),
                "g": bound_match.group("g"),
            }
            kind = "backend_search_started"
            summary = (
                "Started backend search with "
                f"s={current_search['s']} p={current_search['p']} "
                f"o={current_search['o']} g={current_search['g']}."
            )
            data.update(current_search)

        rg_match = RG_COUNT_RE.search(message)
        if rg_match:
            kind = "candidate_row_groups_known"
            data["row_group_count"] = int(rg_match.group("count"))
            if current_search is not None:
                data["bound"] = current_search
            summary = f"Backend search will consider {data['row_group_count']} row groups."

        if "ensure_predicates_loaded:" in message:
            kind = "index_loaded"
            summary = message
        elif "ensure_subjects_loaded:" in message:
            kind = "index_loaded"
            summary = message
        elif "ensure_objects_loaded:" in message:
            kind = "index_loaded"
            summary = message
        elif "ensure_graphs_loaded:" in message:
            kind = "index_loaded"
            summary = message

        events.append(
            {
                "seq": seq,
                "kind": kind,
                "summary": summary,
                "data": data,
            }
        )
        seq += 1
    return events


def parse_join_orders(section_lines: list[str]) -> list[dict[str, Any]]:
    orders: list[dict[str, Any]] = []
    current_bgp: int | None = None
    for line in section_lines:
        line = line.rstrip()
        if line.startswith("  BGP #"):
            try:
                current_bgp = int(line.split("#", 1)[1].split(":", 1)[0])
            except ValueError:
                current_bgp = None
            continue
        match = JOIN_ORDER_RE.match(line)
        if match and current_bgp is not None:
            raw = match.group(1).strip()
            parts = [p for p in raw.split(" ") if p]
            orders.append(
                {
                    "bgp_id": current_bgp,
                    "order": parts,
                }
            )
    return orders


def bound_term_count(tp: dict[str, Any]) -> int:
    count = 0
    for key in ("s", "p", "o"):
        if tp.get(key, {}).get("kind") in {"hit", "miss", "other"}:
            count += 1
    return count


def planner_reason_for_pattern(tp: dict[str, Any]) -> str:
    bound_count = bound_term_count(tp)
    estimate = tp.get("estimate")
    pred_present = tp.get("predicate_present")
    reasons: list[str] = [f"{bound_count}/3 positions concrete before execution"]
    if isinstance(estimate, int):
        reasons.append(f"estimated {estimate} row(s)")
    if pred_present is True:
        reasons.append("predicate present in index")
    elif pred_present is False:
        reasons.append("predicate absent in index")
    if not tp.get("bound_built", True):
        reasons.append("bound encoding failed, so runtime expects empty results")
    return "; ".join(reasons)


def parse_order_label(step: str) -> str:
    return step.split("(", 1)[0]


def planner_events_from_explain(
    explain_json: dict[str, Any], explain_sections: dict[str, list[str]]
) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    seq = 1
    tps = explain_json.get("triple_patterns", [])
    events.append(
        {
            "seq": seq,
            "kind": "parse_completed",
            "summary": "Parsed query text successfully.",
            "data": {
                "query": explain_json.get("query", ""),
            },
        }
    )
    seq += 1

    algebra_text = "\n".join(explain_sections.get("ALGEBRA", [])).strip()
    if algebra_text:
        events.append(
            {
                "seq": seq,
                "kind": "algebra_built",
                "summary": "Built algebra tree for the query.",
                "data": {"algebra_text": algebra_text},
            }
        )
        seq += 1

    for tp in tps:
        events.append(
            {
                "seq": seq,
                "kind": "triple_pattern_estimated",
                "summary": (
                    f"Estimated {tp['pattern']} at {tp['estimate']} row(s); "
                    f"{planner_reason_for_pattern(tp)}."
                ),
                "data": tp,
            }
        )
        seq += 1

    for order in parse_join_orders(explain_sections.get("JOIN ORDER (per BGP)", [])):
        events.append(
            {
                "seq": seq,
                "kind": "bgp_join_order_chosen",
                "summary": (
                    f"BGP #{order['bgp_id']} planner order: {' '.join(order['order'])}."
                ),
                "data": order,
            }
        )
        seq += 1
    return events


def build_history_overview(trace_doc: dict[str, Any]) -> list[str]:
    history: list[str] = []
    req = trace_doc["request"]
    trace_meta = trace_doc["trace"]
    results = trace_doc["results"]
    planner = trace_doc["planner"]

    history.append(
        f"Opened {req['data_cottas']} and discovered "
        f"{len(trace_doc['index_artifacts'])} index artifact(s)."
    )
    history.append(
        f"Parsed the query and extracted {len(planner.get('triple_patterns', []))} "
        "triple pattern(s)."
    )
    tp_by_label = {
        tp["label"]: tp for tp in planner.get("triple_patterns", [])
    }
    for order in planner.get("join_orders", []):
        history.append(f"BGP #{order['bgp_id']} planner order: {' '.join(order['order'])}.")
        ordered_labels = [parse_order_label(step) for step in order.get("order", [])]
        ordered_tps = [tp_by_label[label] for label in ordered_labels if label in tp_by_label]
        if ordered_tps:
            first_estimate = ordered_tps[0].get("estimate")
            tied = [
                tp for tp in ordered_tps
                if tp.get("estimate") == first_estimate
            ]
            if len(tied) > 1:
                tied_labels = ", ".join(tp["label"] for tp in tied)
                history.append(
                    f"BGP #{order['bgp_id']} opened with a coarse estimate tie at "
                    f"{first_estimate} row(s) between {tied_labels}; current implementation "
                    "therefore falls back to query order."
                )
        for step in order.get("order", []):
            label = parse_order_label(step)
            tp = tp_by_label.get(label)
            if tp is not None:
                history.append(
                    f"{label} = `{tp['pattern']}` because {planner_reason_for_pattern(tp)}."
                )
    if results.get("summary", {}).get("kind") == "select":
        count = results["summary"].get("binding_count", 0)
        vars_ = ", ".join(results["summary"].get("vars", []))
        history.append(
            f"Real execution returned {count} binding row(s) for variables: {vars_}."
        )
    elif results.get("summary", {}).get("kind") == "error":
        history.append(
            f"Real execution did not complete normally: {results['summary'].get('error')}."
        )
    elif results.get("summary", {}).get("kind") == "ask":
        history.append(
            f"Real execution returned ASK = {results['summary'].get('boolean')}."
        )

    elapsed = trace_meta.get("elapsed_ms", {})
    if elapsed:
        exec_total = elapsed.get("exec_total")
        exec_total_text = (
            f"{exec_total:.1f} ms"
            if isinstance(exec_total, (int, float))
            else "unknown"
        )
        history.append(
            "Observed timings: "
            f"plan total {elapsed.get('plan_total', 0):.1f} ms, "
            f"exec total {exec_total_text}."
        )
    return history


def summarize_results(result_json: dict[str, Any]) -> dict[str, Any]:
    if "error" in result_json:
        return {
            "kind": "error",
            "error": result_json["error"],
        }
    if "boolean" in result_json:
        return {
            "kind": "ask",
            "boolean": bool(result_json["boolean"]),
        }
    bindings = result_json.get("results", {}).get("bindings", [])
    vars_ = result_json.get("head", {}).get("vars", [])
    return {
        "kind": "select",
        "vars": vars_,
        "binding_count": len(bindings),
        "preview_bindings": bindings[:5],
    }


def render_binding_value(cell: dict[str, Any]) -> str:
    value = cell.get("value", "")
    cell_type = cell.get("type", "")
    if cell_type == "uri":
        return f"<{value}>"
    if cell_type == "literal":
        if "xml:lang" in cell:
            return f"\"{value}\"@{cell['xml:lang']}"
        if "datatype" in cell:
            return f"\"{value}\"^^<{cell['datatype']}>"
        return f"\"{value}\""
    return value


def render_preview_row(binding: dict[str, Any]) -> str:
    parts = []
    for var, cell in binding.items():
        parts.append(f"?{var}={render_binding_value(cell)}")
    return "  ".join(parts)


def build_trace_document(
    *,
    trace_mode: str,
    factoidal_bin: Path,
    data_cottas: Path,
    query_text: str,
    explain_json: dict[str, Any],
    explain_stdout: str,
    exec_result_json: dict[str, Any],
    exec_stderr: str,
    exec_elapsed_ms: float,
) -> dict[str, Any]:
    explain_sections = split_sections(explain_stdout)
    planner_events = planner_events_from_explain(explain_json, explain_sections)
    exec_events = parse_trace_lines(exec_stderr)
    index_artifacts = discover_index_artifacts(data_cottas)

    explain_elapsed = explain_json.get("timing_ms", {})
    for line in explain_sections.get("ELAPSED", []):
        match = ELAPSED_RE.search(line)
        if match:
            explain_elapsed = {
                "parse": float(match.group("parse")),
                "open": float(match.group("open")),
                "algebra": float(match.group("algebra")),
                "estimate": float(match.group("estimate")),
                "total": float(match.group("total")),
            }
            break

    result_summary = summarize_results(exec_result_json)
    planner = {
        "query": explain_json.get("query"),
        "triple_patterns": explain_json.get("triple_patterns", []),
        "join_orders": parse_join_orders(explain_sections.get("JOIN ORDER (per BGP)", [])),
        "algebra_text": "\n".join(explain_sections.get("ALGEBRA", [])).strip(),
        "index_use_summary": "\n".join(explain_sections.get("INDEX-USE SUMMARY", [])).strip(),
    }

    trace_doc = {
        "trace_mode": trace_mode,
        "request": {
            "method": "CLI",
            "binary": str(factoidal_bin),
            "query_text": query_text.strip(),
            "data_cottas": str(data_cottas),
        },
        "index_artifacts": index_artifacts,
        "results": {
            "type": "sparql-results+json",
            "payload": exec_result_json,
            "summary": result_summary,
        },
        "planner": planner,
        "trace": {
            "engine": "factoidal-cli-experiment",
            "engine_build": "native_cli_plus_explain",
            "backend": "GB_CottasOnDisk",
            "elapsed_ms": {
                "plan_parse": explain_elapsed.get("parse"),
                "plan_open": explain_elapsed.get("open"),
                "plan_algebra": explain_elapsed.get("algebra"),
                "plan_estimate": explain_elapsed.get("estimate"),
                "plan_total": explain_elapsed.get("total"),
                "exec_total": exec_elapsed_ms,
            },
            "event_count": len(planner_events) + len(exec_events),
        },
        "events": planner_events + [
            {
                "seq": len(planner_events) + ev["seq"],
                "kind": ev["kind"],
                "summary": ev["summary"],
                "data": ev["data"],
            }
            for ev in exec_events
        ],
    }
    trace_doc["history_overview"] = build_history_overview(trace_doc)
    return trace_doc


def write_history_markdown(trace_doc: dict[str, Any], out_path: Path) -> None:
    lines = [
        "# Query Trace Experiment",
        "",
        f"Trace mode: `{trace_doc['trace_mode']}`",
        f"Data: `{trace_doc['request']['data_cottas']}`",
        "",
        "## History Overview",
        "",
    ]
    for item in trace_doc["history_overview"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Planner",
            "",
            "```text",
            trace_doc["planner"].get("algebra_text", ""),
            "```",
            "",
            "## Full Query",
            "",
            "```sparql",
            trace_doc["request"]["query_text"],
            "```",
            "",
            "## Index Artifacts",
            "",
        ]
    )
    for artifact in trace_doc["index_artifacts"]:
        lines.append(
            f"- `{artifact['kind']}` `{artifact['path']}` ({artifact['size_bytes']} bytes)"
        )
    lines.extend(
        [
            "",
            "## Sample Output Rows",
            "",
        ]
    )
    summary = trace_doc["results"].get("summary", {})
    if summary.get("kind") == "select":
        preview = summary.get("preview_bindings", [])
        if preview:
            for row in preview:
                lines.append(f"- `{render_preview_row(row)}`")
        else:
            lines.append("- No result rows.")
    elif summary.get("kind") == "ask":
        lines.append(f"- ASK = `{summary.get('boolean')}`")
    else:
        lines.append(f"- No normal result rows: `{summary.get('error', 'unknown error')}`")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data-cottas", required=True, type=Path)
    parser.add_argument("--query-file", type=Path)
    parser.add_argument("-e", "--query", dest="inline_query")
    parser.add_argument(
        "--factoidal-bin",
        type=Path,
        default=DEFAULT_BIN,
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=REPO_ROOT / "tmp" / "query-trace-experiment",
    )
    parser.add_argument(
        "--name",
        default="run",
        help="subdirectory name under out-dir",
    )
    parser.add_argument(
        "--trace-mode",
        default="exec",
        choices=["plan", "exec", "debug"],
    )
    parser.add_argument(
        "--exec-timeout-sec",
        type=float,
        default=30.0,
        help="timeout for the real execution leg; explain still runs to completion",
    )
    args = parser.parse_args()

    query_text = read_query_text(args.query_file, args.inline_query)
    out_dir = args.out_dir / args.name
    out_dir.mkdir(parents=True, exist_ok=True)
    explain_json_path = out_dir / "explain.json"

    explain_cmd = [
        str(args.factoidal_bin),
        "--data-cottas",
        str(args.data_cottas),
        "--explain-only",
        "--explain-out",
        str(explain_json_path),
    ]
    if args.query_file is not None:
        explain_cmd.extend(["--query", str(args.query_file)])
    else:
        explain_cmd.extend(["-e", query_text])

    exec_cmd = [
        str(args.factoidal_bin),
        "--data-cottas",
        str(args.data_cottas),
        "-o",
        "json",
    ]
    if args.query_file is not None:
        exec_cmd.extend(["--query", str(args.query_file)])
    else:
        exec_cmd.extend(["-e", query_text])

    explain_proc, _explain_elapsed_ms = run_command(explain_cmd, REPO_ROOT)
    if explain_proc.returncode != 0:
        sys.stderr.write(explain_proc.stderr)
        sys.stderr.write(explain_proc.stdout)
        return explain_proc.returncode

    explain_json = json.loads(explain_json_path.read_text(encoding="utf-8"))
    exec_stderr = ""
    try:
        exec_proc, exec_elapsed_ms = run_command(
            exec_cmd, REPO_ROOT, timeout_sec=args.exec_timeout_sec
        )
        exec_stderr = exec_proc.stderr
        if exec_proc.returncode != 0:
            exec_result_json = {
                "error": f"factoidal exited with code {exec_proc.returncode}",
                "stdout": exec_proc.stdout,
            }
        else:
            exec_result_json = json.loads(exec_proc.stdout)
    except subprocess.TimeoutExpired as exc:
        exec_elapsed_ms = args.exec_timeout_sec * 1000.0
        exec_stderr = ensure_text(exc.stderr)
        exec_result_json = {
            "error": f"execution timed out after {args.exec_timeout_sec:.1f}s",
            "stdout": ensure_text(exc.stdout),
        }

    trace_doc = build_trace_document(
        trace_mode=args.trace_mode,
        factoidal_bin=args.factoidal_bin,
        data_cottas=args.data_cottas,
        query_text=query_text,
        explain_json=explain_json,
        explain_stdout=explain_proc.stdout,
        exec_result_json=exec_result_json,
        exec_stderr=exec_stderr,
        exec_elapsed_ms=exec_elapsed_ms,
    )

    trace_json_path = out_dir / "trace.json"
    trace_json_path.write_text(json.dumps(trace_doc, indent=2) + "\n", encoding="utf-8")
    write_history_markdown(trace_doc, out_dir / "history.md")

    print(str(trace_json_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
