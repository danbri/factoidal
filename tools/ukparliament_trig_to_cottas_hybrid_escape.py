#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

import pandas as pd
from pyoxigraph import parse

import ukparliament_trig_to_cottas as base


def _nt_escape_literal_lex(value: str) -> str:
    out: list[str] = []
    for ch in value:
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif ord(ch) < 0x20 or ord(ch) == 0x7F:
            out.append(f"\\u{ord(ch):04X}")
        else:
            out.append(ch)
    return "".join(out)


def _nt_term(term) -> str:
    cls_name = type(term).__name__
    if cls_name == "NamedNode":
        return f"<{term.value}>"
    if cls_name == "BlankNode":
        return f"_:{term.value}"
    if cls_name == "DefaultGraph":
        return "DEFAULT"
    if cls_name == "Literal":
        lex = _nt_escape_literal_lex(term.value)
        lang = getattr(term, "language", None)
        dt = getattr(term, "datatype", None)
        if lang:
            return f"\"{lex}\"@{lang}"
        if dt is not None and str(dt) != "<http://www.w3.org/2001/XMLSchema#string>":
            iri = dt.value if hasattr(dt, "value") else str(dt).strip("<>")
            return f"\"{lex}\"^^<{iri}>"
        return f"\"{lex}\""
    return str(term)


def stream_trig_to_nq_and_duckdb(
    input_path: Path,
    data_nq_path: Path,
    con,
    batch_size: int,
    progress_every: int,
    quad_limit: int | None,
):
    quad_count = 0
    named_graphs: set[str] = set()
    batch: list[tuple[str, str, str, str]] = []
    started = base.time.time()

    def flush_batch() -> None:
        nonlocal batch
        if not batch:
            return
        frame = pd.DataFrame.from_records(batch, columns=["s", "p", "o", "g"])
        con.register("input_quads", frame)
        try:
            con.execute("INSERT INTO quads SELECT s, p, o, g FROM input_quads")
        finally:
            con.unregister("input_quads")
        batch = []

    with input_path.open("rb") as src, data_nq_path.open("w", encoding="utf-8") as out:
        for quad in parse(src, "application/trig"):
            s = _nt_term(quad.subject)
            p = _nt_term(quad.predicate)
            o = _nt_term(quad.object)
            g = _nt_term(quad.graph_name)
            if g == "DEFAULT":
                out.write(f"{s} {p} {o} .\n")
            else:
                named_graphs.add(g)
                out.write(f"{s} {p} {o} {g} .\n")

            batch.append((s, p, o, g))
            quad_count += 1

            if len(batch) >= batch_size:
                flush_batch()

            if progress_every > 0 and quad_count % progress_every == 0:
                elapsed = base.time.time() - started
                print(
                    f"progress quads={quad_count} named_graphs={len(named_graphs)} elapsed_s={elapsed:.1f}",
                    file=base.sys.stderr,
                    flush=True,
                )

            if quad_limit is not None and quad_count >= quad_limit:
                break

        flush_batch()

    return quad_count, named_graphs


if __name__ == "__main__":
    base.stream_trig_to_nq_and_duckdb = stream_trig_to_nq_and_duckdb
    raise SystemExit(base.main())
