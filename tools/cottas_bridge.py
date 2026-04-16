#!/usr/bin/env python3

import argparse
import sys

import duckdb


def add_graph_filter(clauses: list[str], params: list[str], args: argparse.Namespace) -> None:
    if args.default_graph:
        clauses.append("(g IS NULL OR g = 'DEFAULT')")
    elif args.graph is not None:
        clauses.append("g = ?")
        params.append(args.graph)


def build_where(args: argparse.Namespace) -> tuple[str, list[str]]:
    clauses: list[str] = []
    params: list[str] = []
    if args.s is not None:
        clauses.append("s = ?")
        params.append(args.s)
    if args.p is not None:
        clauses.append("p = ?")
        params.append(args.p)
    if args.o is not None:
        clauses.append("o = ?")
        params.append(args.o)
    add_graph_filter(clauses, params, args)
    if not clauses:
        return "", params
    return " WHERE " + " AND ".join(clauses), params


def cmd_graphs(args: argparse.Namespace) -> int:
    rows = duckdb.execute(
        "SELECT DISTINCT g FROM PARQUET_SCAN(?) WHERE g IS NOT NULL AND g <> 'DEFAULT' ORDER BY g",
        [args.artifact],
    ).fetchall()
    for (graph,) in rows:
        print(graph)
    return 0


def cmd_estimate(args: argparse.Namespace) -> int:
    where_sql, params = build_where(args)
    row = duckdb.execute(
        "SELECT COUNT(*) FROM PARQUET_SCAN(?)" + where_sql,
        [args.artifact] + params,
    ).fetchone()
    print(int(row[0]))
    return 0


def cmd_predicate_present(args: argparse.Namespace) -> int:
    clauses = ["p = ?"]
    params = [args.predicate]
    add_graph_filter(clauses, params, args)
    row = duckdb.execute(
        "SELECT COUNT(*) FROM PARQUET_SCAN(?) WHERE " + " AND ".join(clauses),
        [args.artifact] + params,
    ).fetchone()
    print("true" if int(row[0]) > 0 else "false")
    return 0


def cmd_search(args: argparse.Namespace) -> int:
    where_sql, params = build_where(args)
    rows = duckdb.execute(
        "SELECT s, p, o, g FROM PARQUET_SCAN(?)" + where_sql,
        [args.artifact] + params,
    ).fetchall()
    for s, p, o, g in rows:
        if g is None or g == "DEFAULT":
            print(f"{s} {p} {o} .")
        else:
            print(f"{s} {p} {o} {g} .")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Factoidal COTTAS bridge")
    sub = parser.add_subparsers(dest="cmd", required=True)

    graphs = sub.add_parser("graphs")
    graphs.add_argument("--artifact", required=True)
    graphs.set_defaults(func=cmd_graphs)

    for name, func in [("search", cmd_search), ("estimate", cmd_estimate)]:
        cmd = sub.add_parser(name)
        cmd.add_argument("--artifact", required=True)
        cmd.add_argument("--s")
        cmd.add_argument("--p")
        cmd.add_argument("--o")
        cmd.add_argument("--graph")
        cmd.add_argument("--default-graph", action="store_true")
        cmd.set_defaults(func=func)

    pred = sub.add_parser("predicate-present")
    pred.add_argument("--artifact", required=True)
    pred.add_argument("--predicate", required=True)
    pred.add_argument("--graph")
    pred.add_argument("--default-graph", action="store_true")
    pred.set_defaults(func=cmd_predicate_present)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
